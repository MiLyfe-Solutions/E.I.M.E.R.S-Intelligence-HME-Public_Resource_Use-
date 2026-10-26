import V185TrunkScan20Chunk129

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_790846 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_790846 : Nat := 118140960795 + 790846 * 2 ^ 59
def prefixEnd_790846 : Nat := 4983230072969 + 3 ^ 40 * 790846 * 2
def baseEnd_790846 : Nat := 360963663720638262300419

theorem tailTrace_790846 : CollatzResearch.WordTrace tailWord_790846 prefixEnd_790846 360963663720638262300419 := by
  unfold tailWord_790846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3605565411613435323597049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19229682195271655059184261 3605565411613435323597049)
  ·
    refine ⟨2704174058710076492697787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3605565411613435323597049 2704174058710076492697787)
    ·
      refine ⟨4056261088065114739046681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2704174058710076492697787 4056261088065114739046681)
      ·
        refine ⟨3042195816048836054285011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4056261088065114739046681 3042195816048836054285011)
        ·
          refine ⟨4563293724073254081427517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3042195816048836054285011 4563293724073254081427517)
          ·
            refine ⟨1711235146527470280535319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4563293724073254081427517 1711235146527470280535319)
            ·
              refine ⟨2566852719791205420802979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711235146527470280535319 2566852719791205420802979)
              ·
                refine ⟨3850279079686808131204469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2566852719791205420802979 3850279079686808131204469)
                ·
                  refine ⟨360963663720638262300419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3850279079686808131204469 360963663720638262300419)
                  ·
                    rfl

theorem cell20_790846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_790846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790846 prefixEnd_790846 := by exact prefixLift 790846
  have htrace : WordTrace (prefixWord ++ tailWord_790846) baseStart_790846 baseEnd_790846 := by
    simpa [prefixWord, tailWord_790846, baseEnd_790846] using wordTrace_append hprefix tailTrace_790846
  have hstable : (prefixWord ++ tailWord_790846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790846).length < 2 ^ (prefixWord ++ tailWord_790846).sum := by decide
  have hdescent : baseEnd_790846 < baseStart_790846 := by decide
  rcases family_descends (prefixWord ++ tailWord_790846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790887 : List Nat := [1, 1, 5, 1, 3, 3, 1, 3, 2]
def baseStart_790887 : Nat := 118140960795 + 790887 * 2 ^ 59
def prefixEnd_790887 : Nat := 4983230072969 + 3 ^ 40 * 790887 * 2
def baseEnd_790887 : Nat := 360982377237824341933585

theorem tailTrace_790887 : CollatzResearch.WordTrace tailWord_790887 prefixEnd_790887 360982377237824341933585 := by
  unfold tailWord_790887
  simp only [CollatzResearch.WordTrace]
  refine ⟨28846018685758946591018915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19230679123839297727345943 28846018685758946591018915)
  ·
    refine ⟨43269028028638419886528373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28846018685758946591018915 43269028028638419886528373)
    ·
      refine ⟨4056471377684851864362035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43269028028638419886528373 4056471377684851864362035)
      ·
        refine ⟨6084707066527277796543053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4056471377684851864362035 6084707066527277796543053)
        ·
          refine ⟨2281765149947729173703645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6084707066527277796543053 2281765149947729173703645)
          ·
            refine ⟨855661931230398440138867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2281765149947729173703645 855661931230398440138867)
            ·
              refine ⟨1283492896845597660208301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855661931230398440138867 1283492896845597660208301)
              ·
                refine ⟨481309836317099122578113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1283492896845597660208301 481309836317099122578113)
                ·
                  refine ⟨360982377237824341933585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 481309836317099122578113 360982377237824341933585)
                  ·
                    rfl

theorem cell20_790887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 3, 2].length) (baseStart_790887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790887 prefixEnd_790887 := by exact prefixLift 790887
  have htrace : WordTrace (prefixWord ++ tailWord_790887) baseStart_790887 baseEnd_790887 := by
    simpa [prefixWord, tailWord_790887, baseEnd_790887] using wordTrace_append hprefix tailTrace_790887
  have hstable : (prefixWord ++ tailWord_790887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790887).length < 2 ^ (prefixWord ++ tailWord_790887).sum := by decide
  have hdescent : baseEnd_790887 < baseStart_790887 := by decide
  rcases family_descends (prefixWord ++ tailWord_790887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790898 : List Nat := [3, 2, 1, 2, 1, 5, 6]
def baseStart_790898 : Nat := 118140960795 + 790898 * 2 ^ 59
def prefixEnd_790898 : Nat := 4983230072969 + 3 ^ 40 * 790898 * 2
def baseEnd_790898 : Nat := 40109710881950799174097

theorem tailTrace_790898 : CollatzResearch.WordTrace tailWord_790898 prefixEnd_790898 40109710881950799174097 := by
  unfold tailWord_790898
  simp only [CollatzResearch.WordTrace]
  refine ⟨7211604972179773867417337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19230946592479396979779565 7211604972179773867417337)
  ·
    refine ⟨5408703729134830400563003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7211604972179773867417337 5408703729134830400563003)
    ·
      refine ⟨8113055593702245600844505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5408703729134830400563003 8113055593702245600844505)
      ·
        refine ⟨6084791695276684200633379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8113055593702245600844505 6084791695276684200633379)
        ·
          refine ⟨9127187542915026300950069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6084791695276684200633379 9127187542915026300950069)
          ·
            refine ⟨855673832148283715714069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9127187542915026300950069 855673832148283715714069)
            ·
              refine ⟨40109710881950799174097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 855673832148283715714069 40109710881950799174097)
              ·
                rfl

theorem cell20_790898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 6].length) (baseStart_790898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790898 prefixEnd_790898 := by exact prefixLift 790898
  have htrace : WordTrace (prefixWord ++ tailWord_790898) baseStart_790898 baseEnd_790898 := by
    simpa [prefixWord, tailWord_790898, baseEnd_790898] using wordTrace_append hprefix tailTrace_790898
  have hstable : (prefixWord ++ tailWord_790898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790898).length < 2 ^ (prefixWord ++ tailWord_790898).sum := by decide
  have hdescent : baseEnd_790898 < baseStart_790898 := by decide
  rcases family_descends (prefixWord ++ tailWord_790898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790905 : List Nat := [1, 2, 1, 3, 2, 1, 1, 6, 3]
def baseStart_790905 : Nat := 118140960795 + 790905 * 2 ^ 59
def prefixEnd_790905 : Nat := 4983230072969 + 3 ^ 40 * 790905 * 2
def baseEnd_790905 : Nat := 360990592928296279333511

theorem tailTrace_790905 : CollatzResearch.WordTrace tailWord_790905 prefixEnd_790905 360990592928296279333511 := by
  unfold tailWord_790905
  simp only [CollatzResearch.WordTrace]
  refine ⟨28846675199693735665174169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19231116799795823776782779 28846675199693735665174169)
  ·
    refine ⟨21635006399770301748880627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28846675199693735665174169 21635006399770301748880627)
    ·
      refine ⟨32452509599655452623320941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21635006399770301748880627 32452509599655452623320941)
      ·
        refine ⟨12169691099870794733745353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32452509599655452623320941 12169691099870794733745353)
        ·
          refine ⟨9127268324903096050309015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12169691099870794733745353 9127268324903096050309015)
          ·
            refine ⟨13690902487354644075463523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9127268324903096050309015 13690902487354644075463523)
            ·
              refine ⟨20536353731031966113195285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13690902487354644075463523 20536353731031966113195285)
              ·
                refine ⟨962641581142123411556029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20536353731031966113195285 962641581142123411556029)
                ·
                  refine ⟨360990592928296279333511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 962641581142123411556029 360990592928296279333511)
                  ·
                    rfl

theorem cell20_790905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_790905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790905 prefixEnd_790905 := by exact prefixLift 790905
  have htrace : WordTrace (prefixWord ++ tailWord_790905) baseStart_790905 baseEnd_790905 := by
    simpa [prefixWord, tailWord_790905, baseEnd_790905] using wordTrace_append hprefix tailTrace_790905
  have hstable : (prefixWord ++ tailWord_790905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790905).length < 2 ^ (prefixWord ++ tailWord_790905).sum := by decide
  have hdescent : baseEnd_790905 < baseStart_790905 := by decide
  rcases family_descends (prefixWord ++ tailWord_790905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790914 : List Nat := [3, 4, 2, 1, 3, 1, 2, 1, 3]
def baseStart_790914 : Nat := 118140960795 + 790914 * 2 ^ 59
def prefixEnd_790914 : Nat := 4983230072969 + 3 ^ 40 * 790914 * 2
def baseEnd_790914 : Nat := 360994700773532248033475

theorem tailTrace_790914 : CollatzResearch.WordTrace tailWord_790914 prefixEnd_790914 360994700773532248033475 := by
  unfold tailWord_790914
  simp only [CollatzResearch.WordTrace]
  refine ⟨7211750864165282550562949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19231335637774086801501197 7211750864165282550562949)
  ·
    refine ⟨1352203287030990478230553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7211750864165282550562949 1352203287030990478230553)
    ·
      refine ⟨1014152465273242858672915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1352203287030990478230553 1014152465273242858672915)
      ·
        refine ⟨1521228697909864288009373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1014152465273242858672915 1521228697909864288009373)
        ·
          refine ⟨570460761716199108003515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1521228697909864288009373 570460761716199108003515)
          ·
            refine ⟨855691142574298662005273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570460761716199108003515 855691142574298662005273)
            ·
              refine ⟨641768356930723996503955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 855691142574298662005273 641768356930723996503955)
              ·
                refine ⟨962652535396085994755933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641768356930723996503955 962652535396085994755933)
                ·
                  refine ⟨360994700773532248033475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 962652535396085994755933 360994700773532248033475)
                  ·
                    rfl

theorem cell20_790914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_790914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790914 prefixEnd_790914 := by exact prefixLift 790914
  have htrace : WordTrace (prefixWord ++ tailWord_790914) baseStart_790914 baseEnd_790914 := by
    simpa [prefixWord, tailWord_790914, baseEnd_790914] using wordTrace_append hprefix tailTrace_790914
  have hstable : (prefixWord ++ tailWord_790914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790914).length < 2 ^ (prefixWord ++ tailWord_790914).sum := by decide
  have hdescent : baseEnd_790914 < baseStart_790914 := by decide
  rcases family_descends (prefixWord ++ tailWord_790914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790936 : List Nat := [2, 1, 2, 5, 1, 1, 2, 6]
def baseStart_790936 : Nat := 118140960795 + 790936 * 2 ^ 59
def prefixEnd_790936 : Nat := 4983230072969 + 3 ^ 40 * 790936 * 2
def baseEnd_790936 : Nat := 120334914057665983100017

theorem tailTrace_790936 : CollatzResearch.WordTrace tailWord_790936 prefixEnd_790936 120334914057665983100017 := by
  unfold tailWord_790936
  simp only [CollatzResearch.WordTrace]
  refine ⟨14423902931290713979776331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19231870575054285306368441 14423902931290713979776331)
  ·
    refine ⟨21635854396936070969664497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14423902931290713979776331 21635854396936070969664497)
    ·
      refine ⟨16226890797702053227248373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21635854396936070969664497 16226890797702053227248373)
      ·
        refine ⟨1521271012284567490054535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16226890797702053227248373 1521271012284567490054535)
        ·
          refine ⟨2281906518426851235081803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521271012284567490054535 2281906518426851235081803)
          ·
            refine ⟨3422859777640276852622705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2281906518426851235081803 3422859777640276852622705)
            ·
              refine ⟨2567144833230207639467029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3422859777640276852622705 2567144833230207639467029)
              ·
                refine ⟨120334914057665983100017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2567144833230207639467029 120334914057665983100017)
                ·
                  rfl

theorem cell20_790936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_790936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790936 prefixEnd_790936 := by exact prefixLift 790936
  have htrace : WordTrace (prefixWord ++ tailWord_790936) baseStart_790936 baseEnd_790936 := by
    simpa [prefixWord, tailWord_790936, baseEnd_790936] using wordTrace_append hprefix tailTrace_790936
  have hstable : (prefixWord ++ tailWord_790936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790936).length < 2 ^ (prefixWord ++ tailWord_790936).sum := by decide
  have hdescent : baseEnd_790936 < baseStart_790936 := by decide
  rcases family_descends (prefixWord ++ tailWord_790936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790946 : List Nat := [3, 3, 1, 2, 1, 1, 2, 5, 2]
def baseStart_790946 : Nat := 118140960795 + 790946 * 2 ^ 59
def prefixEnd_790946 : Nat := 4983230072969 + 3 ^ 40 * 790946 * 2
def baseEnd_790946 : Nat := 361009306445482358966677

theorem tailTrace_790946 : CollatzResearch.WordTrace tailWord_790946 prefixEnd_790946 361009306445482358966677 := by
  unfold tailWord_790946
  simp only [CollatzResearch.WordTrace]
  refine ⟨7212042648136299916854173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19232113728363466444944461 7212042648136299916854173)
  ·
    refine ⟨2704515993051112468820315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7212042648136299916854173 2704515993051112468820315)
    ·
      refine ⟨4056773989576668703230473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2704515993051112468820315 4056773989576668703230473)
      ·
        refine ⟨3042580492182501527422855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4056773989576668703230473 3042580492182501527422855)
        ·
          refine ⟨4563870738273752291134283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3042580492182501527422855 4563870738273752291134283)
          ·
            refine ⟨6845806107410628436701425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4563870738273752291134283 6845806107410628436701425)
            ·
              refine ⟨5134354580557971327526069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6845806107410628436701425 5134354580557971327526069)
              ·
                refine ⟨481345741927309811955569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5134354580557971327526069 481345741927309811955569)
                ·
                  refine ⟨361009306445482358966677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 481345741927309811955569 361009306445482358966677)
                  ·
                    rfl

theorem cell20_790946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_790946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790946 prefixEnd_790946 := by exact prefixLift 790946
  have htrace : WordTrace (prefixWord ++ tailWord_790946) baseStart_790946 baseEnd_790946 := by
    simpa [prefixWord, tailWord_790946, baseEnd_790946] using wordTrace_append hprefix tailTrace_790946
  have hstable : (prefixWord ++ tailWord_790946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790946).length < 2 ^ (prefixWord ++ tailWord_790946).sum := by decide
  have hdescent : baseEnd_790946 < baseStart_790946 := by decide
  rcases family_descends (prefixWord ++ tailWord_790946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790974 : List Nat := [4, 2, 1, 1, 1, 1, 5, 5]
def baseStart_790974 : Nat := 118140960795 + 790974 * 2 ^ 59
def prefixEnd_790974 : Nat := 4983230072969 + 3 ^ 40 * 790974 * 2
def baseEnd_790974 : Nat := 120340695469479568677743

theorem tailTrace_790974 : CollatzResearch.WordTrace tailWord_790974 prefixEnd_790974 120340695469479568677743 := by
  unfold tailWord_790974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3606148979555470056179497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19232794557629173632957317 3606148979555470056179497)
  ·
    refine ⟨2704611734666602542134623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3606148979555470056179497 2704611734666602542134623)
    ·
      refine ⟨4056917601999903813201935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2704611734666602542134623 4056917601999903813201935)
      ·
        refine ⟨6085376402999855719802903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4056917601999903813201935 6085376402999855719802903)
        ·
          refine ⟨9128064604499783579704355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6085376402999855719802903 9128064604499783579704355)
          ·
            refine ⟨13692096906749675369556533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9128064604499783579704355 13692096906749675369556533)
            ·
              refine ⟨1283634085007782065895925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13692096906749675369556533 1283634085007782065895925)
              ·
                refine ⟨120340695469479568677743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1283634085007782065895925 120340695469479568677743)
                ·
                  rfl

theorem cell20_790974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_790974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790974 prefixEnd_790974 := by exact prefixLift 790974
  have htrace : WordTrace (prefixWord ++ tailWord_790974) baseStart_790974 baseEnd_790974 := by
    simpa [prefixWord, tailWord_790974, baseEnd_790974] using wordTrace_append hprefix tailTrace_790974
  have hstable : (prefixWord ++ tailWord_790974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790974).length < 2 ^ (prefixWord ++ tailWord_790974).sum := by decide
  have hdescent : baseEnd_790974 < baseStart_790974 := by decide
  rcases family_descends (prefixWord ++ tailWord_790974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790998 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_790998 : Nat := 118140960795 + 790998 * 2 ^ 59
def prefixEnd_790998 : Nat := 4983230072969 + 3 ^ 40 * 790998 * 2
def baseEnd_790998 : Nat := 361033040662401289233131

theorem tailTrace_790998 : CollatzResearch.WordTrace tailWord_790998 prefixEnd_790998 361033040662401289233131 := by
  unfold tailWord_790998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1803129199272300784269353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19233378125571208365539765 1803129199272300784269353)
  ·
    refine ⟨1352346899454225588202015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1803129199272300784269353 1352346899454225588202015)
    ·
      refine ⟨2028520349181338382303023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1352346899454225588202015 2028520349181338382303023)
      ·
        refine ⟨3042780523772007573454535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2028520349181338382303023 3042780523772007573454535)
        ·
          refine ⟨4564170785658011360181803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3042780523772007573454535 4564170785658011360181803)
          ·
            refine ⟨6846256178487017040272705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4564170785658011360181803 6846256178487017040272705)
            ·
              refine ⟨5134692133865262780204529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6846256178487017040272705 5134692133865262780204529)
              ·
                refine ⟨3851019100398947085153397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5134692133865262780204529 3851019100398947085153397)
                ·
                  refine ⟨361033040662401289233131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3851019100398947085153397 361033040662401289233131)
                  ·
                    rfl

theorem cell20_790998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_790998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_790998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_790998 prefixEnd_790998 := by exact prefixLift 790998
  have htrace : WordTrace (prefixWord ++ tailWord_790998) baseStart_790998 baseEnd_790998 := by
    simpa [prefixWord, tailWord_790998, baseEnd_790998] using wordTrace_append hprefix tailTrace_790998
  have hstable : (prefixWord ++ tailWord_790998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790998).length < 2 ^ (prefixWord ++ tailWord_790998).sum := by decide
  have hdescent : baseEnd_790998 < baseStart_790998 := by decide
  rcases family_descends (prefixWord ++ tailWord_790998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791022 : List Nat := [4, 1, 2, 1, 2, 2, 2, 4, 2]
def baseStart_791022 : Nat := 118140960795 + 791022 * 2 ^ 59
def prefixEnd_791022 : Nat := 4983230072969 + 3 ^ 40 * 791022 * 2
def baseEnd_791022 : Nat := 361043994916363872433033

theorem tailTrace_791022 : CollatzResearch.WordTrace tailWord_791022 prefixEnd_791022 361043994916363872433033 := by
  unfold tailWord_791022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3606367817533733080897915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19233961693513243098122213 3606367817533733080897915)
  ·
    refine ⟨5409551726300599621346873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3606367817533733080897915 5409551726300599621346873)
    ·
      refine ⟨4057163794725449716010155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5409551726300599621346873 4057163794725449716010155)
      ·
        refine ⟨6085745692088174574015233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4057163794725449716010155 6085745692088174574015233)
        ·
          refine ⟨4564309269066130930511425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6085745692088174574015233 4564309269066130930511425)
          ·
            refine ⟨3423231951799598197883569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4564309269066130930511425 3423231951799598197883569)
            ·
              refine ⟨2567423963849698648412677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3423231951799598197883569 2567423963849698648412677)
              ·
                refine ⟨481391993221818496577377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2567423963849698648412677 481391993221818496577377)
                ·
                  refine ⟨361043994916363872433033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 481391993221818496577377 361043994916363872433033)
                  ·
                    rfl

theorem cell20_791022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_791022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791022 prefixEnd_791022 := by exact prefixLift 791022
  have htrace : WordTrace (prefixWord ++ tailWord_791022) baseStart_791022 baseEnd_791022 := by
    simpa [prefixWord, tailWord_791022, baseEnd_791022] using wordTrace_append hprefix tailTrace_791022
  have hstable : (prefixWord ++ tailWord_791022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791022).length < 2 ^ (prefixWord ++ tailWord_791022).sum := by decide
  have hdescent : baseEnd_791022 < baseStart_791022 := by decide
  rcases family_descends (prefixWord ++ tailWord_791022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791053 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 5]
def baseStart_791053 : Nat := 118140960795 + 791053 * 2 ^ 59
def prefixEnd_791053 : Nat := 4983230072969 + 3 ^ 40 * 791053 * 2
def baseEnd_791053 : Nat := 361058144161065542399573

theorem tailTrace_791053 : CollatzResearch.WordTrace tailWord_791053 prefixEnd_791053 361058144161065542399573 := by
  unfold tailWord_791053
  simp only [CollatzResearch.WordTrace]
  refine ⟨28852073203157556941561813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19234715468771704627707875 28852073203157556941561813)
  ·
    refine ⟨676220465699005240817855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 28852073203157556941561813 676220465699005240817855)
    ·
      refine ⟨1014330698548507861226783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 676220465699005240817855 1014330698548507861226783)
      ·
        refine ⟨1521496047822761791840175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1014330698548507861226783 1521496047822761791840175)
        ·
          refine ⟨2282244071734142687760263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521496047822761791840175 2282244071734142687760263)
          ·
            refine ⟨3423366107601214031640395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2282244071734142687760263 3423366107601214031640395)
            ·
              refine ⟨5135049161401821047460593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3423366107601214031640395 5135049161401821047460593)
              ·
                refine ⟨3851286871051365785595445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5135049161401821047460593 3851286871051365785595445)
                ·
                  refine ⟨361058144161065542399573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3851286871051365785595445 361058144161065542399573)
                  ·
                    rfl

theorem cell20_791053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_791053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791053 prefixEnd_791053 := by exact prefixLift 791053
  have htrace : WordTrace (prefixWord ++ tailWord_791053) baseStart_791053 baseEnd_791053 := by
    simpa [prefixWord, tailWord_791053, baseEnd_791053] using wordTrace_append hprefix tailTrace_791053
  have hstable : (prefixWord ++ tailWord_791053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791053).length < 2 ^ (prefixWord ++ tailWord_791053).sum := by decide
  have hdescent : baseEnd_791053 < baseStart_791053 := by decide
  rcases family_descends (prefixWord ++ tailWord_791053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791095 : List Nat := [1, 1, 3, 1, 2, 3, 3, 3, 3]
def baseStart_791095 : Nat := 118140960795 + 791095 * 2 ^ 59
def prefixEnd_791095 : Nat := 4983230072969 + 3 ^ 40 * 791095 * 2
def baseEnd_791095 : Nat := 361077314105500062999401

theorem tailTrace_791095 : CollatzResearch.WordTrace tailWord_791095 prefixEnd_791095 361077314105500062999401 := by
  unfold tailWord_791095
  simp only [CollatzResearch.WordTrace]
  refine ⟨28853605069005398114590739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19235736712670265409727159 28853605069005398114590739)
  ·
    refine ⟨43280407603508097171886109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28853605069005398114590739 43280407603508097171886109)
    ·
      refine ⟨16230152851315536439457291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43280407603508097171886109 16230152851315536439457291)
      ·
        refine ⟨24345229276973304659185937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16230152851315536439457291 24345229276973304659185937)
        ·
          refine ⟨18258921957729978494389453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24345229276973304659185937 18258921957729978494389453)
          ·
            refine ⟨6847095734148741935396045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18258921957729978494389453 6847095734148741935396045)
            ·
              refine ⟨2567660900305778225773517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6847095734148741935396045 2567660900305778225773517)
              ·
                refine ⟨962872837614666834665069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2567660900305778225773517 962872837614666834665069)
                ·
                  refine ⟨361077314105500062999401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 962872837614666834665069 361077314105500062999401)
                  ·
                    rfl

theorem cell20_791095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 3, 3].length) (baseStart_791095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791095 prefixEnd_791095 := by exact prefixLift 791095
  have htrace : WordTrace (prefixWord ++ tailWord_791095) baseStart_791095 baseEnd_791095 := by
    simpa [prefixWord, tailWord_791095, baseEnd_791095] using wordTrace_append hprefix tailTrace_791095
  have hstable : (prefixWord ++ tailWord_791095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791095).length < 2 ^ (prefixWord ++ tailWord_791095).sum := by decide
  have hdescent : baseEnd_791095 < baseStart_791095 := by decide
  rcases family_descends (prefixWord ++ tailWord_791095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791109 : List Nat := [1, 3, 1, 1, 1, 5, 2, 6]
def baseStart_791109 : Nat := 118140960795 + 791109 * 2 ^ 59
def prefixEnd_791109 : Nat := 4983230072969 + 3 ^ 40 * 791109 * 2
def baseEnd_791109 : Nat := 120361234695659412177559

theorem tailTrace_791109 : CollatzResearch.WordTrace tailWord_791109 prefixEnd_791109 120361234695659412177559 := by
  unfold tailWord_791109
  simp only [CollatzResearch.WordTrace]
  refine ⟨28854115690954678505600381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19236077127303119003733587 28854115690954678505600381)
  ·
    refine ⟨10820293384108004439600143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28854115690954678505600381 10820293384108004439600143)
    ·
      refine ⟨16230440076162006659400215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10820293384108004439600143 16230440076162006659400215)
      ·
        refine ⟨24345660114243009989100323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16230440076162006659400215 24345660114243009989100323)
        ·
          refine ⟨36518490171364514983650485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24345660114243009989100323 36518490171364514983650485)
          ·
            refine ⟨3423608453565423279717233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36518490171364514983650485 3423608453565423279717233)
            ·
              refine ⟨2567706340174067459787925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3423608453565423279717233 2567706340174067459787925)
              ·
                refine ⟨120361234695659412177559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2567706340174067459787925 120361234695659412177559)
                ·
                  rfl

theorem cell20_791109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 6].length) (baseStart_791109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791109 prefixEnd_791109 := by exact prefixLift 791109
  have htrace : WordTrace (prefixWord ++ tailWord_791109) baseStart_791109 baseEnd_791109 := by
    simpa [prefixWord, tailWord_791109, baseEnd_791109] using wordTrace_append hprefix tailTrace_791109
  have hstable : (prefixWord ++ tailWord_791109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791109).length < 2 ^ (prefixWord ++ tailWord_791109).sum := by decide
  have hdescent : baseEnd_791109 < baseStart_791109 := by decide
  rcases family_descends (prefixWord ++ tailWord_791109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791126 : List Nat := [5, 2, 2, 11]
def baseStart_791126 : Nat := 118140960795 + 791126 * 2 ^ 59
def prefixEnd_791126 : Nat := 4983230072969 + 3 ^ 40 * 791126 * 2
def baseEnd_791126 : Nat := 1485973100206591493687

theorem tailTrace_791126 : CollatzResearch.WordTrace tailWord_791126 prefixEnd_791126 1485973100206591493687 := by
  unfold tailWord_791126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1803420983243318150560577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19236490487928726939312821 1803420983243318150560577)
  ·
    refine ⟨1352565737432488612920433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1803420983243318150560577 1352565737432488612920433)
    ·
      refine ⟨1014424303074366459690325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1352565737432488612920433 1014424303074366459690325)
      ·
        refine ⟨1485973100206591493687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1014424303074366459690325 1485973100206591493687)
        ·
          rfl

theorem cell20_791126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 11].length) (baseStart_791126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791126 prefixEnd_791126 := by exact prefixLift 791126
  have htrace : WordTrace (prefixWord ++ tailWord_791126) baseStart_791126 baseEnd_791126 := by
    simpa [prefixWord, tailWord_791126, baseEnd_791126] using wordTrace_append hprefix tailTrace_791126
  have hstable : (prefixWord ++ tailWord_791126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791126).length < 2 ^ (prefixWord ++ tailWord_791126).sum := by decide
  have hdescent : baseEnd_791126 < baseStart_791126 := by decide
  rcases family_descends (prefixWord ++ tailWord_791126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791132 : List Nat := [2, 2, 4, 1, 3, 2, 2, 2, 2]
def baseStart_791132 : Nat := 118140960795 + 791132 * 2 ^ 59
def prefixEnd_791132 : Nat := 4983230072969 + 3 ^ 40 * 791132 * 2
def baseEnd_791132 : Nat := 361094201913692378765917

theorem tailTrace_791132 : CollatzResearch.WordTrace tailWord_791132 prefixEnd_791132 361094201913692378765917 := by
  unfold tailWord_791132
  simp only [CollatzResearch.WordTrace]
  refine ⟨14427477284935676716843825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19236636379914235622458433 14427477284935676716843825)
  ·
    refine ⟨10820607963701757537632869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14427477284935676716843825 10820607963701757537632869)
    ·
      refine ⟨2028863993194079538306163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10820607963701757537632869 2028863993194079538306163)
      ·
        refine ⟨3043295989791119307459245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2028863993194079538306163 3043295989791119307459245)
        ·
          refine ⟨1141235996171669740297217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3043295989791119307459245 1141235996171669740297217)
          ·
            refine ⟨855926997128752305222913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1141235996171669740297217 855926997128752305222913)
            ·
              refine ⟨641945247846564228917185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 855926997128752305222913 641945247846564228917185)
              ·
                refine ⟨481458935884923171687889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 641945247846564228917185 481458935884923171687889)
                ·
                  refine ⟨361094201913692378765917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 481458935884923171687889 361094201913692378765917)
                  ·
                    rfl

theorem cell20_791132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_791132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791132 prefixEnd_791132 := by exact prefixLift 791132
  have htrace : WordTrace (prefixWord ++ tailWord_791132) baseStart_791132 baseEnd_791132 := by
    simpa [prefixWord, tailWord_791132, baseEnd_791132] using wordTrace_append hprefix tailTrace_791132
  have hstable : (prefixWord ++ tailWord_791132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791132).length < 2 ^ (prefixWord ++ tailWord_791132).sum := by decide
  have hdescent : baseEnd_791132 < baseStart_791132 := by decide
  rcases family_descends (prefixWord ++ tailWord_791132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791136 : List Nat := [2, 1, 1, 3, 2, 1, 6, 2, 2]
def baseStart_791136 : Nat := 118140960795 + 791136 * 2 ^ 59
def prefixEnd_791136 : Nat := 4983230072969 + 3 ^ 40 * 791136 * 2
def baseEnd_791136 : Nat := 361096027622686142632567

theorem tailTrace_791136 : CollatzResearch.WordTrace tailWord_791136 prefixEnd_791136 361096027622686142632567 := by
  unfold tailWord_791136
  simp only [CollatzResearch.WordTrace]
  refine ⟨14427550230928431058416631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19236733641237908077888841 14427550230928431058416631)
  ·
    refine ⟨21641325346392646587624947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14427550230928431058416631 21641325346392646587624947)
    ·
      refine ⟨32461988019588969881437421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21641325346392646587624947 32461988019588969881437421)
      ·
        refine ⟨12173245507345863705539033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32461988019588969881437421 12173245507345863705539033)
        ·
          refine ⟨9129934130509397779154275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12173245507345863705539033 9129934130509397779154275)
          ·
            refine ⟨13694901195764096668731413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9129934130509397779154275 13694901195764096668731413)
            ·
              refine ⟨641948493551442031346785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13694901195764096668731413 641948493551442031346785)
              ·
                refine ⟨481461370163581523510089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 641948493551442031346785 481461370163581523510089)
                ·
                  refine ⟨361096027622686142632567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 481461370163581523510089 361096027622686142632567)
                  ·
                    rfl

theorem cell20_791136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 2].length) (baseStart_791136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791136 prefixEnd_791136 := by exact prefixLift 791136
  have htrace : WordTrace (prefixWord ++ tailWord_791136) baseStart_791136 baseEnd_791136 := by
    simpa [prefixWord, tailWord_791136, baseEnd_791136] using wordTrace_append hprefix tailTrace_791136
  have hstable : (prefixWord ++ tailWord_791136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791136).length < 2 ^ (prefixWord ++ tailWord_791136).sum := by decide
  have hdescent : baseEnd_791136 < baseStart_791136 := by decide
  rcases family_descends (prefixWord ++ tailWord_791136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791140 : List Nat := [2, 3, 1, 1, 2, 2, 2, 3, 4]
def baseStart_791140 : Nat := 118140960795 + 791140 * 2 ^ 59
def prefixEnd_791140 : Nat := 4983230072969 + 3 ^ 40 * 791140 * 2
def baseEnd_791140 : Nat := 361097853331679906499217

theorem tailTrace_791140 : CollatzResearch.WordTrace tailWord_791140 prefixEnd_791140 361097853331679906499217 := by
  unfold tailWord_791140
  simp only [CollatzResearch.WordTrace]
  refine ⟨14427623176921185399989437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19236830902561580533319249 14427623176921185399989437)
  ·
    refine ⟨5410358691345444524996039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14427623176921185399989437 5410358691345444524996039)
    ·
      refine ⟨8115538037018166787494059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5410358691345444524996039 8115538037018166787494059)
      ·
        refine ⟨12173307055527250181241089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8115538037018166787494059 12173307055527250181241089)
        ·
          refine ⟨9129980291645437635930817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12173307055527250181241089 9129980291645437635930817)
          ·
            refine ⟨6847485218734078226948113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9129980291645437635930817 6847485218734078226948113)
            ·
              refine ⟨5135613914050558670211085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6847485218734078226948113 5135613914050558670211085)
              ·
                refine ⟨1925855217768959501329157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5135613914050558670211085 1925855217768959501329157)
                ·
                  refine ⟨361097853331679906499217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1925855217768959501329157 361097853331679906499217)
                  ·
                    rfl

theorem cell20_791140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_791140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791140 prefixEnd_791140 := by exact prefixLift 791140
  have htrace : WordTrace (prefixWord ++ tailWord_791140) baseStart_791140 baseEnd_791140 := by
    simpa [prefixWord, tailWord_791140, baseEnd_791140] using wordTrace_append hprefix tailTrace_791140
  have hstable : (prefixWord ++ tailWord_791140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791140).length < 2 ^ (prefixWord ++ tailWord_791140).sum := by decide
  have hdescent : baseEnd_791140 < baseStart_791140 := by decide
  rcases family_descends (prefixWord ++ tailWord_791140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791150 : List Nat := [4, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_791150 : Nat := 118140960795 + 791150 * 2 ^ 59
def prefixEnd_791150 : Nat := 4983230072969 + 3 ^ 40 * 791150 * 2
def baseEnd_791150 : Nat := 361102417604164316165843

theorem tailTrace_791150 : CollatzResearch.WordTrace tailWord_791150 prefixEnd_791150 361102417604164316165843 := by
  unfold tailWord_791150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3606951385475767813480363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19237074055870761671895269 3606951385475767813480363)
  ·
    refine ⟨5410427078213651720220545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3606951385475767813480363 5410427078213651720220545)
    ·
      refine ⟨4057820308660238790165409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5410427078213651720220545 4057820308660238790165409)
      ·
        refine ⟨3043365231495179092624057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4057820308660238790165409 3043365231495179092624057)
        ·
          refine ⟨2282523923621384319468043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3043365231495179092624057 2282523923621384319468043)
          ·
            refine ⟨3423785885432076479202065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2282523923621384319468043 3423785885432076479202065)
            ·
              refine ⟨2567839414074057359401549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3423785885432076479202065 2567839414074057359401549)
              ·
                refine ⟨962939780277771509775581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2567839414074057359401549 962939780277771509775581)
                ·
                  refine ⟨361102417604164316165843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 962939780277771509775581 361102417604164316165843)
                  ·
                    rfl

theorem cell20_791150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_791150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791150 prefixEnd_791150 := by exact prefixLift 791150
  have htrace : WordTrace (prefixWord ++ tailWord_791150) baseStart_791150 baseEnd_791150 := by
    simpa [prefixWord, tailWord_791150, baseEnd_791150] using wordTrace_append hprefix tailTrace_791150
  have hstable : (prefixWord ++ tailWord_791150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791150).length < 2 ^ (prefixWord ++ tailWord_791150).sum := by decide
  have hdescent : baseEnd_791150 < baseStart_791150 := by decide
  rcases family_descends (prefixWord ++ tailWord_791150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791188 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 5]
def baseStart_791188 : Nat := 118140960795 + 791188 * 2 ^ 59
def prefixEnd_791188 : Nat := 4983230072969 + 3 ^ 40 * 791188 * 2
def baseEnd_791188 : Nat := 361119761839605072899021

theorem tailTrace_791188 : CollatzResearch.WordTrace tailWord_791188 prefixEnd_791188 361119761839605072899021 := by
  unfold tailWord_791188
  simp only [CollatzResearch.WordTrace]
  refine ⟨14428498528834237498863109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19237998038445649998484145 14428498528834237498863109)
  ·
    refine ⟨2705343474156419531036833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14428498528834237498863109 2705343474156419531036833)
    ·
      refine ⟨2029007605617314648277625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2705343474156419531036833 2029007605617314648277625)
      ·
        refine ⟨1521755704212985986208219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2029007605617314648277625 1521755704212985986208219)
        ·
          refine ⟨2282633556319478979312329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521755704212985986208219 2282633556319478979312329)
          ·
            refine ⟨1711975167239609234484247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2282633556319478979312329 1711975167239609234484247)
            ·
              refine ⟨2567962750859413851726371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711975167239609234484247 2567962750859413851726371)
              ·
                refine ⟨3851944126289120777589557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2567962750859413851726371 3851944126289120777589557)
                ·
                  refine ⟨361119761839605072899021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3851944126289120777589557 361119761839605072899021)
                  ·
                    rfl

theorem cell20_791188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_791188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791188 prefixEnd_791188 := by exact prefixLift 791188
  have htrace : WordTrace (prefixWord ++ tailWord_791188) baseStart_791188 baseEnd_791188 := by
    simpa [prefixWord, tailWord_791188, baseEnd_791188] using wordTrace_append hprefix tailTrace_791188
  have hstable : (prefixWord ++ tailWord_791188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791188).length < 2 ^ (prefixWord ++ tailWord_791188).sum := by decide
  have hdescent : baseEnd_791188 < baseStart_791188 := by decide
  rcases family_descends (prefixWord ++ tailWord_791188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791250 : List Nat := [3, 2, 2, 2, 3, 2, 1, 1, 4]
def baseStart_791250 : Nat := 118140960795 + 791250 * 2 ^ 59
def prefixEnd_791250 : Nat := 4983230072969 + 3 ^ 40 * 791250 * 2
def baseEnd_791250 : Nat := 361148060329008412832101

theorem tailTrace_791250 : CollatzResearch.WordTrace tailWord_791250 prefixEnd_791250 361148060329008412832101 := by
  unfold tailWord_791250
  simp only [CollatzResearch.WordTrace]
  refine ⟨7214814595860964896620801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19239505588962573057655469 7214814595860964896620801)
  ·
    refine ⟨5411110946895723672465601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7214814595860964896620801 5411110946895723672465601)
    ·
      refine ⟨4058333210171792754349201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5411110946895723672465601 4058333210171792754349201)
      ·
        refine ⟨3043749907628844565761901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4058333210171792754349201 3043749907628844565761901)
        ·
          refine ⟨1141406215360816712160713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3043749907628844565761901 1141406215360816712160713)
          ·
            refine ⟨856054661520612534120535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1141406215360816712160713 856054661520612534120535)
            ·
              refine ⟨1284081992280918801180803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856054661520612534120535 1284081992280918801180803)
              ·
                refine ⟨1926122988421378201771205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1284081992280918801180803 1926122988421378201771205)
                ·
                  refine ⟨361148060329008412832101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1926122988421378201771205 361148060329008412832101)
                  ·
                    rfl

theorem cell20_791250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_791250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791250 prefixEnd_791250 := by exact prefixLift 791250
  have htrace : WordTrace (prefixWord ++ tailWord_791250) baseStart_791250 baseEnd_791250 := by
    simpa [prefixWord, tailWord_791250, baseEnd_791250] using wordTrace_append hprefix tailTrace_791250
  have hstable : (prefixWord ++ tailWord_791250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791250).length < 2 ^ (prefixWord ++ tailWord_791250).sum := by decide
  have hdescent : baseEnd_791250 < baseStart_791250 := by decide
  rcases family_descends (prefixWord ++ tailWord_791250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791260 : List Nat := [2, 2, 5, 1, 1, 3, 2, 1, 3]
def baseStart_791260 : Nat := 118140960795 + 791260 * 2 ^ 59
def prefixEnd_791260 : Nat := 4983230072969 + 3 ^ 40 * 791260 * 2
def baseEnd_791260 : Nat := 361152624601492822498727

theorem tailTrace_791260 : CollatzResearch.WordTrace tailWord_791260 prefixEnd_791260 361152624601492822498727 := by
  unfold tailWord_791260
  simp only [CollatzResearch.WordTrace]
  refine ⟨14429811556703815647173617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19239748742271754196231489 14429811556703815647173617)
  ·
    refine ⟨10822358667527861735380213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14429811556703815647173617 10822358667527861735380213)
    ·
      refine ⟨1014596125080737037691895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10822358667527861735380213 1014596125080737037691895)
      ·
        refine ⟨1521894187621105556537843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1014596125080737037691895 1521894187621105556537843)
        ·
          refine ⟨2282841281431658334806765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521894187621105556537843 2282841281431658334806765)
          ·
            refine ⟨856065480536871875552537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2282841281431658334806765 856065480536871875552537)
            ·
              refine ⟨642049110402653906664403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 856065480536871875552537 642049110402653906664403)
              ·
                refine ⟨963073665603980859996605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642049110402653906664403 963073665603980859996605)
                ·
                  refine ⟨361152624601492822498727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 963073665603980859996605 361152624601492822498727)
                  ·
                    rfl

theorem cell20_791260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 2, 1, 3].length) (baseStart_791260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791260 prefixEnd_791260 := by exact prefixLift 791260
  have htrace : WordTrace (prefixWord ++ tailWord_791260) baseStart_791260 baseEnd_791260 := by
    simpa [prefixWord, tailWord_791260, baseEnd_791260] using wordTrace_append hprefix tailTrace_791260
  have hstable : (prefixWord ++ tailWord_791260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791260).length < 2 ^ (prefixWord ++ tailWord_791260).sum := by decide
  have hdescent : baseEnd_791260 < baseStart_791260 := by decide
  rcases family_descends (prefixWord ++ tailWord_791260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791275 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 6]
def baseStart_791275 : Nat := 118140960795 + 791275 * 2 ^ 59
def prefixEnd_791275 : Nat := 4983230072969 + 3 ^ 40 * 791275 * 2
def baseEnd_791275 : Nat := 361159471010219436998665

theorem tailTrace_791275 : CollatzResearch.WordTrace tailWord_791275 prefixEnd_791275 361159471010219436998665 := by
  unfold tailWord_791275
  simp only [CollatzResearch.WordTrace]
  refine ⟨28860170208353288856143279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19240113472235525904095519 28860170208353288856143279)
  ·
    refine ⟨43290255312529933284214919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28860170208353288856143279 43290255312529933284214919)
    ·
      refine ⟨64935382968794899926322379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43290255312529933284214919 64935382968794899926322379)
      ·
        refine ⟨97403074453192349889483569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64935382968794899926322379 97403074453192349889483569)
        ·
          refine ⟨73052305839894262417112677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97403074453192349889483569 73052305839894262417112677)
          ·
            refine ⟨13697307344980174203208627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73052305839894262417112677 13697307344980174203208627)
            ·
              refine ⟨20545961017470261304812941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13697307344980174203208627 20545961017470261304812941)
              ·
                refine ⟨7704735381551347989304853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20545961017470261304812941 7704735381551347989304853)
                ·
                  refine ⟨361159471010219436998665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7704735381551347989304853 361159471010219436998665)
                  ·
                    rfl

theorem cell20_791275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_791275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791275 prefixEnd_791275 := by exact prefixLift 791275
  have htrace : WordTrace (prefixWord ++ tailWord_791275) baseStart_791275 baseEnd_791275 := by
    simpa [prefixWord, tailWord_791275, baseEnd_791275] using wordTrace_append hprefix tailTrace_791275
  have hstable : (prefixWord ++ tailWord_791275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791275).length < 2 ^ (prefixWord ++ tailWord_791275).sum := by decide
  have hdescent : baseEnd_791275 < baseStart_791275 := by decide
  rcases family_descends (prefixWord ++ tailWord_791275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791330 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_791330 : Nat := 118140960795 + 791330 * 2 ^ 59
def prefixEnd_791330 : Nat := 4983230072969 + 3 ^ 40 * 791330 * 2
def baseEnd_791330 : Nat := 361184574508883690165107

theorem tailTrace_791330 : CollatzResearch.WordTrace tailWord_791330 prefixEnd_791330 361184574508883690165107 := by
  unfold tailWord_791330
  simp only [CollatzResearch.WordTrace]
  refine ⟨7215544055788508312348861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19241450815436022166263629 7215544055788508312348861)
  ·
    refine ⟨2705829020920690617130823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7215544055788508312348861 2705829020920690617130823)
    ·
      refine ⟨4058743531381035925696235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2705829020920690617130823 4058743531381035925696235)
      ·
        refine ⟨6088115297071553888544353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4058743531381035925696235 6088115297071553888544353)
        ·
          refine ⟨4566086472803665416408265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6088115297071553888544353 4566086472803665416408265)
          ·
            refine ⟨3424564854602749062306199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4566086472803665416408265 3424564854602749062306199)
            ·
              refine ⟨5136847281904123593459299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3424564854602749062306199 5136847281904123593459299)
              ·
                refine ⟨7705270922856185390188949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5136847281904123593459299 7705270922856185390188949)
                ·
                  refine ⟨361184574508883690165107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7705270922856185390188949 361184574508883690165107)
                  ·
                    rfl

theorem cell20_791330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_791330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791330 prefixEnd_791330 := by exact prefixLift 791330
  have htrace : WordTrace (prefixWord ++ tailWord_791330) baseStart_791330 baseEnd_791330 := by
    simpa [prefixWord, tailWord_791330, baseEnd_791330] using wordTrace_append hprefix tailTrace_791330
  have hstable : (prefixWord ++ tailWord_791330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791330).length < 2 ^ (prefixWord ++ tailWord_791330).sum := by decide
  have hdescent : baseEnd_791330 < baseStart_791330 := by decide
  rcases family_descends (prefixWord ++ tailWord_791330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791347 : List Nat := [1, 1, 1, 2, 6, 1, 1, 5, 2]
def baseStart_791347 : Nat := 118140960795 + 791347 * 2 ^ 59
def prefixEnd_791347 : Nat := 4983230072969 + 3 ^ 40 * 791347 * 2
def baseEnd_791347 : Nat := 361192333772107186598371

theorem tailTrace_791347 : CollatzResearch.WordTrace tailWord_791347 prefixEnd_791347 361192333772107186598371 := by
  unfold tailWord_791347
  simp only [CollatzResearch.WordTrace]
  refine ⟨28862796264092445152764295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19241864176061630101842863 28862796264092445152764295)
  ·
    refine ⟨43294194396138667729146443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28862796264092445152764295 43294194396138667729146443)
    ·
      refine ⟨64941291594208001593719665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43294194396138667729146443 64941291594208001593719665)
      ·
        refine ⟨48705968695656001195289749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64941291594208001593719665 48705968695656001195289749)
        ·
          refine ⟨2283092282608875056029207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48705968695656001195289749 2283092282608875056029207)
          ·
            refine ⟨3424638423913312584043811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2283092282608875056029207 3424638423913312584043811)
            ·
              refine ⟨5136957635869968876065717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3424638423913312584043811 5136957635869968876065717)
              ·
                refine ⟨481589778362809582131161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5136957635869968876065717 481589778362809582131161)
                ·
                  refine ⟨361192333772107186598371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 481589778362809582131161 361192333772107186598371)
                  ·
                    rfl

theorem cell20_791347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 5, 2].length) (baseStart_791347 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791347 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791347 prefixEnd_791347 := by exact prefixLift 791347
  have htrace : WordTrace (prefixWord ++ tailWord_791347) baseStart_791347 baseEnd_791347 := by
    simpa [prefixWord, tailWord_791347, baseEnd_791347] using wordTrace_append hprefix tailTrace_791347
  have hstable : (prefixWord ++ tailWord_791347).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791347).length < 2 ^ (prefixWord ++ tailWord_791347).sum := by decide
  have hdescent : baseEnd_791347 < baseStart_791347 := by decide
  rcases family_descends (prefixWord ++ tailWord_791347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791351 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 6]
def baseStart_791351 : Nat := 118140960795 + 791351 * 2 ^ 59
def prefixEnd_791351 : Nat := 4983230072969 + 3 ^ 40 * 791351 * 2
def baseEnd_791351 : Nat := 361194159481100950465021

theorem tailTrace_791351 : CollatzResearch.WordTrace tailWord_791351 prefixEnd_791351 361194159481100950465021 := by
  unfold tailWord_791351
  simp only [CollatzResearch.WordTrace]
  refine ⟨28862942156077953835909907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19241961437385302557273271 28862942156077953835909907)
  ·
    refine ⟨43294413234116930753864861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28862942156077953835909907 43294413234116930753864861)
    ·
      refine ⟨16235404962793849032699323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43294413234116930753864861 16235404962793849032699323)
      ·
        refine ⟨24353107444190773549048985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16235404962793849032699323 24353107444190773549048985)
        ·
          refine ⟨18264830583143080161786739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24353107444190773549048985 18264830583143080161786739)
          ·
            refine ⟨27397245874714620242680109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18264830583143080161786739 27397245874714620242680109)
            ·
              refine ⟨10273967203017982591005041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27397245874714620242680109 10273967203017982591005041)
              ·
                refine ⟨7705475402263486943253781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10273967203017982591005041 7705475402263486943253781)
                ·
                  refine ⟨361194159481100950465021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7705475402263486943253781 361194159481100950465021)
                  ·
                    rfl

theorem cell20_791351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_791351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791351 prefixEnd_791351 := by exact prefixLift 791351
  have htrace : WordTrace (prefixWord ++ tailWord_791351) baseStart_791351 baseEnd_791351 := by
    simpa [prefixWord, tailWord_791351, baseEnd_791351] using wordTrace_append hprefix tailTrace_791351
  have hstable : (prefixWord ++ tailWord_791351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791351).length < 2 ^ (prefixWord ++ tailWord_791351).sum := by decide
  have hdescent : baseEnd_791351 < baseStart_791351 := by decide
  rcases family_descends (prefixWord ++ tailWord_791351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791357 : List Nat := [1, 4, 1, 4, 2, 2, 1, 2, 3]
def baseStart_791357 : Nat := 118140960795 + 791357 * 2 ^ 59
def prefixEnd_791357 : Nat := 4983230072969 + 3 ^ 40 * 791357 * 2
def baseEnd_791357 : Nat := 361196898044591596264997

theorem tailTrace_791357 : CollatzResearch.WordTrace tailWord_791357 prefixEnd_791357 361196898044591596264997 := by
  unfold tailWord_791357
  simp only [CollatzResearch.WordTrace]
  refine ⟨28863160994056216860628325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19242107329370811240418883 28863160994056216860628325)
  ·
    refine ⟨5411842686385540661367811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28863160994056216860628325 5411842686385540661367811)
    ·
      refine ⟨8117764029578310992051717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5411842686385540661367811 8117764029578310992051717)
      ·
        refine ⟨1522080755545933311009697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8117764029578310992051717 1522080755545933311009697)
        ·
          refine ⟨1141560566659449983257273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1522080755545933311009697 1141560566659449983257273)
          ·
            refine ⟨856170424994587487442955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1141560566659449983257273 856170424994587487442955)
            ·
              refine ⟨1284255637491881231164433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856170424994587487442955 1284255637491881231164433)
              ·
                refine ⟨963191728118910923373325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1284255637491881231164433 963191728118910923373325)
                ·
                  refine ⟨361196898044591596264997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 963191728118910923373325 361196898044591596264997)
                  ·
                    rfl

theorem cell20_791357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_791357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791357 prefixEnd_791357 := by exact prefixLift 791357
  have htrace : WordTrace (prefixWord ++ tailWord_791357) baseStart_791357 baseEnd_791357 := by
    simpa [prefixWord, tailWord_791357, baseEnd_791357] using wordTrace_append hprefix tailTrace_791357
  have hstable : (prefixWord ++ tailWord_791357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791357).length < 2 ^ (prefixWord ++ tailWord_791357).sum := by decide
  have hdescent : baseEnd_791357 < baseStart_791357 := by decide
  rcases family_descends (prefixWord ++ tailWord_791357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791368 : List Nat := [2, 1, 3, 1, 1, 3, 4, 1, 4]
def baseStart_791368 : Nat := 118140960795 + 791368 * 2 ^ 59
def prefixEnd_791368 : Nat := 4983230072969 + 3 ^ 40 * 791368 * 2
def baseEnd_791368 : Nat := 361201918744324446898285

theorem tailTrace_791368 : CollatzResearch.WordTrace tailWord_791368 prefixEnd_791368 361201918744324446898285 := by
  unfold tailWord_791368
  simp only [CollatzResearch.WordTrace]
  refine ⟨14431781098508182869639379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19242374798010910492852505 14431781098508182869639379)
  ·
    refine ⟨21647671647762274304459069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14431781098508182869639379 21647671647762274304459069)
    ·
      refine ⟨8117876867910852864172151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21647671647762274304459069 8117876867910852864172151)
      ·
        refine ⟨12176815301866279296258227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8117876867910852864172151 12176815301866279296258227)
        ·
          refine ⟨18265222952799418944387341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12176815301866279296258227 18265222952799418944387341)
          ·
            refine ⟨6849458607299782104145253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18265222952799418944387341 6849458607299782104145253)
            ·
              refine ⟨1284273488868709144527235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6849458607299782104145253 1284273488868709144527235)
              ·
                refine ⟨1926410233303063716790853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1284273488868709144527235 1926410233303063716790853)
                ·
                  refine ⟨361201918744324446898285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1926410233303063716790853 361201918744324446898285)
                  ·
                    rfl

theorem cell20_791368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_791368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791368 prefixEnd_791368 := by exact prefixLift 791368
  have htrace : WordTrace (prefixWord ++ tailWord_791368) baseStart_791368 baseEnd_791368 := by
    simpa [prefixWord, tailWord_791368, baseEnd_791368] using wordTrace_append hprefix tailTrace_791368
  have hstable : (prefixWord ++ tailWord_791368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791368).length < 2 ^ (prefixWord ++ tailWord_791368).sum := by decide
  have hdescent : baseEnd_791368 < baseStart_791368 := by decide
  rcases family_descends (prefixWord ++ tailWord_791368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791378 : List Nat := [3, 2, 2, 1, 1, 2, 5, 1, 3]
def baseStart_791378 : Nat := 118140960795 + 791378 * 2 ^ 59
def prefixEnd_791378 : Nat := 4983230072969 + 3 ^ 40 * 791378 * 2
def baseEnd_791378 : Nat := 361206483016808856564911

theorem tailTrace_791378 : CollatzResearch.WordTrace tailWord_791378 prefixEnd_791378 361206483016808856564911 := by
  unfold tailWord_791378
  simp only [CollatzResearch.WordTrace]
  refine ⟨7215981731745034361785697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19242617951320091631428525 7215981731745034361785697)
  ·
    refine ⟨5411986298808775771339273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7215981731745034361785697 5411986298808775771339273)
    ·
      refine ⟨4058989724106581828504455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5411986298808775771339273 4058989724106581828504455)
      ·
        refine ⟨6088484586159872742756683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4058989724106581828504455 6088484586159872742756683)
        ·
          refine ⟨9132726879239809114135025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6088484586159872742756683 9132726879239809114135025)
          ·
            refine ⟨6849545159429856835601269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9132726879239809114135025 6849545159429856835601269)
            ·
              refine ⟨642144858696549078337619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6849545159429856835601269 642144858696549078337619)
              ·
                refine ⟨963217288044823617506429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642144858696549078337619 963217288044823617506429)
                ·
                  refine ⟨361206483016808856564911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 963217288044823617506429 361206483016808856564911)
                  ·
                    rfl

theorem cell20_791378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_791378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791378 prefixEnd_791378 := by exact prefixLift 791378
  have htrace : WordTrace (prefixWord ++ tailWord_791378) baseStart_791378 baseEnd_791378 := by
    simpa [prefixWord, tailWord_791378, baseEnd_791378] using wordTrace_append hprefix tailTrace_791378
  have hstable : (prefixWord ++ tailWord_791378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791378).length < 2 ^ (prefixWord ++ tailWord_791378).sum := by decide
  have hdescent : baseEnd_791378 < baseStart_791378 := by decide
  rcases family_descends (prefixWord ++ tailWord_791378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791413 : List Nat := [1, 3, 4, 1, 1, 2, 8]
def baseStart_791413 : Nat := 118140960795 + 791413 * 2 ^ 59
def prefixEnd_791413 : Nat := 4983230072969 + 3 ^ 40 * 791413 * 2
def baseEnd_791413 : Nat := 40135828663389365599789

theorem tailTrace_791413 : CollatzResearch.WordTrace tailWord_791413 prefixEnd_791413 40135828663389365599789 := by
  unfold tailWord_791413
  simp only [CollatzResearch.WordTrace]
  refine ⟨28865203481853338424666893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19243468987902225616444595 28865203481853338424666893)
  ·
    refine ⟨10824451305695001909250085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28865203481853338424666893 10824451305695001909250085)
    ·
      refine ⟨2029584619817812857984391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10824451305695001909250085 2029584619817812857984391)
      ·
        refine ⟨3044376929726719286976587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2029584619817812857984391 3044376929726719286976587)
        ·
          refine ⟨4566565394590078930464881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3044376929726719286976587 4566565394590078930464881)
          ·
            refine ⟨3424924045942559197848661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4566565394590078930464881 3424924045942559197848661)
            ·
              refine ⟨40135828663389365599789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3424924045942559197848661 40135828663389365599789)
              ·
                rfl

theorem cell20_791413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 8].length) (baseStart_791413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791413 prefixEnd_791413 := by exact prefixLift 791413
  have htrace : WordTrace (prefixWord ++ tailWord_791413) baseStart_791413 baseEnd_791413 := by
    simpa [prefixWord, tailWord_791413, baseEnd_791413] using wordTrace_append hprefix tailTrace_791413
  have hstable : (prefixWord ++ tailWord_791413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791413).length < 2 ^ (prefixWord ++ tailWord_791413).sum := by decide
  have hdescent : baseEnd_791413 < baseStart_791413 := by decide
  rcases family_descends (prefixWord ++ tailWord_791413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791426 : List Nat := [3, 4, 2, 2, 1, 1, 2, 5]
def baseStart_791426 : Nat := 118140960795 + 791426 * 2 ^ 59
def prefixEnd_791426 : Nat := 4983230072969 + 3 ^ 40 * 791426 * 2
def baseEnd_791426 : Nat := 120409463841578007654905

theorem tailTrace_791426 : CollatzResearch.WordTrace tailWord_791426 prefixEnd_791426 120409463841578007654905 := by
  unfold tailWord_791426
  simp only [CollatzResearch.WordTrace]
  refine ⟨7216419407701560411222533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19243785087204161096593421 7216419407701560411222533)
  ·
    refine ⟨1353078638944042577104225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7216419407701560411222533 1353078638944042577104225)
    ·
      refine ⟨1014808979208031932828169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1353078638944042577104225 1014808979208031932828169)
      ·
        refine ⟨761106734406023949621127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1014808979208031932828169 761106734406023949621127)
        ·
          refine ⟨1141660101609035924431691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 761106734406023949621127 1141660101609035924431691)
          ·
            refine ⟨1712490152413553886647537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1141660101609035924431691 1712490152413553886647537)
            ·
              refine ⟨1284367614310165414985653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1712490152413553886647537 1284367614310165414985653)
              ·
                refine ⟨120409463841578007654905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1284367614310165414985653 120409463841578007654905)
                ·
                  rfl

theorem cell20_791426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_791426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791426 prefixEnd_791426 := by exact prefixLift 791426
  have htrace : WordTrace (prefixWord ++ tailWord_791426) baseStart_791426 baseEnd_791426 := by
    simpa [prefixWord, tailWord_791426, baseEnd_791426] using wordTrace_append hprefix tailTrace_791426
  have hstable : (prefixWord ++ tailWord_791426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791426).length < 2 ^ (prefixWord ++ tailWord_791426).sum := by decide
  have hdescent : baseEnd_791426 < baseStart_791426 := by decide
  rcases family_descends (prefixWord ++ tailWord_791426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791444 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 6]
def baseStart_791444 : Nat := 118140960795 + 791444 * 2 ^ 59
def prefixEnd_791444 : Nat := 4983230072969 + 3 ^ 40 * 791444 * 2
def baseEnd_791444 : Nat := 361236607215205960364641

theorem tailTrace_791444 : CollatzResearch.WordTrace tailWord_791444 prefixEnd_791444 361236607215205960364641 := by
  unfold tailWord_791444
  simp only [CollatzResearch.WordTrace]
  refine ⟨14433167072370515359522693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19244222763160687146030257 14433167072370515359522693)
  ·
    refine ⟨2706218826069471629910505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14433167072370515359522693 2706218826069471629910505)
    ·
      refine ⟨2029664119552103722432879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2706218826069471629910505 2029664119552103722432879)
      ·
        refine ⟨3044496179328155583649319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2029664119552103722432879 3044496179328155583649319)
        ·
          refine ⟨4566744268992233375473979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3044496179328155583649319 4566744268992233375473979)
          ·
            refine ⟨6850116403488350063210969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4566744268992233375473979 6850116403488350063210969)
            ·
              refine ⟨5137587302616262547408227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6850116403488350063210969 5137587302616262547408227)
              ·
                refine ⟨7706380953924393821112341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5137587302616262547408227 7706380953924393821112341)
                ·
                  refine ⟨361236607215205960364641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7706380953924393821112341 361236607215205960364641)
                  ·
                    rfl

theorem cell20_791444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_791444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791444 prefixEnd_791444 := by exact prefixLift 791444
  have htrace : WordTrace (prefixWord ++ tailWord_791444) baseStart_791444 baseEnd_791444 := by
    simpa [prefixWord, tailWord_791444, baseEnd_791444] using wordTrace_append hprefix tailTrace_791444
  have hstable : (prefixWord ++ tailWord_791444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791444).length < 2 ^ (prefixWord ++ tailWord_791444).sum := by decide
  have hdescent : baseEnd_791444 < baseStart_791444 := by decide
  rcases family_descends (prefixWord ++ tailWord_791444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791485 : List Nat := [1, 4, 1, 2, 5, 1, 1, 5]
def baseStart_791485 : Nat := 118140960795 + 791485 * 2 ^ 59
def prefixEnd_791485 : Nat := 4983230072969 + 3 ^ 40 * 791485 * 2
def baseEnd_791485 : Nat := 120418440244130679999269

theorem tailTrace_791485 : CollatzResearch.WordTrace tailWord_791485 prefixEnd_791485 120418440244130679999269 := by
  unfold tailWord_791485
  simp only [CollatzResearch.WordTrace]
  refine ⟨28867829537592494721287909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19245219691728329814191939 28867829537592494721287909)
  ·
    refine ⟨5412718038298592760241483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28867829537592494721287909 5412718038298592760241483)
    ·
      refine ⟨8119077057447889140362225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5412718038298592760241483 8119077057447889140362225)
      ·
        refine ⟨6089307793085916855271669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8119077057447889140362225 6089307793085916855271669)
        ·
          refine ⟨570872605601804705181719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6089307793085916855271669 570872605601804705181719)
          ·
            refine ⟨856308908402707057772579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570872605601804705181719 856308908402707057772579)
            ·
              refine ⟨1284463362604060586658869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856308908402707057772579 1284463362604060586658869)
              ·
                refine ⟨120418440244130679999269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1284463362604060586658869 120418440244130679999269)
                ·
                  rfl

theorem cell20_791485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 1, 5].length) (baseStart_791485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791485 prefixEnd_791485 := by exact prefixLift 791485
  have htrace : WordTrace (prefixWord ++ tailWord_791485) baseStart_791485 baseEnd_791485 := by
    simpa [prefixWord, tailWord_791485, baseEnd_791485] using wordTrace_append hprefix tailTrace_791485
  have hstable : (prefixWord ++ tailWord_791485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791485).length < 2 ^ (prefixWord ++ tailWord_791485).sum := by decide
  have hdescent : baseEnd_791485 < baseStart_791485 := by decide
  rcases family_descends (prefixWord ++ tailWord_791485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791503 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 6]
def baseStart_791503 : Nat := 118140960795 + 791503 * 2 ^ 59
def prefixEnd_791503 : Nat := 4983230072969 + 3 ^ 40 * 791503 * 2
def baseEnd_791503 : Nat := 361263536422863977397733

theorem tailTrace_791503 : CollatzResearch.WordTrace tailWord_791503 prefixEnd_791503 361263536422863977397733 := by
  unfold tailWord_791503
  simp only [CollatzResearch.WordTrace]
  refine ⟨28868486051527283795443163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19245657367684855863628775 28868486051527283795443163)
  ·
    refine ⟨43302729077290925693164745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28868486051527283795443163 43302729077290925693164745)
    ·
      refine ⟨32477046807968194269873559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43302729077290925693164745 32477046807968194269873559)
      ·
        refine ⟨48715570211952291404810339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32477046807968194269873559 48715570211952291404810339)
        ·
          refine ⟨73073355317928437107215509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48715570211952291404810339 73073355317928437107215509)
          ·
            refine ⟨3425313530527895489400727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73073355317928437107215509 3425313530527895489400727)
            ·
              refine ⟨5137970295791843234101091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3425313530527895489400727 5137970295791843234101091)
              ·
                refine ⟨7706955443687764851151637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5137970295791843234101091 7706955443687764851151637)
                ·
                  refine ⟨361263536422863977397733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7706955443687764851151637 361263536422863977397733)
                  ·
                    rfl

theorem cell20_791503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_791503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791503 prefixEnd_791503 := by exact prefixLift 791503
  have htrace : WordTrace (prefixWord ++ tailWord_791503) baseStart_791503 baseEnd_791503 := by
    simpa [prefixWord, tailWord_791503, baseEnd_791503] using wordTrace_append hprefix tailTrace_791503
  have hstable : (prefixWord ++ tailWord_791503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791503).length < 2 ^ (prefixWord ++ tailWord_791503).sum := by decide
  have hdescent : baseEnd_791503 < baseStart_791503 := by decide
  rcases family_descends (prefixWord ++ tailWord_791503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791527 : List Nat := [1, 1, 5, 2, 2, 2, 7]
def baseStart_791527 : Nat := 118140960795 + 791527 * 2 ^ 59
def prefixEnd_791527 : Nat := 4983230072969 + 3 ^ 40 * 791527 * 2
def baseEnd_791527 : Nat := 40141610075202951177515

theorem tailTrace_791527 : CollatzResearch.WordTrace tailWord_791527 prefixEnd_791527 40141610075202951177515 := by
  unfold tailWord_791527
  simp only [CollatzResearch.WordTrace]
  refine ⟨28869361403440335894316835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19246240935626890596211223 28869361403440335894316835)
  ·
    refine ⟨43304042105160503841475253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28869361403440335894316835 43304042105160503841475253)
    ·
      refine ⟨4059753947358797235138305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43304042105160503841475253 4059753947358797235138305)
      ·
        refine ⟨3044815460519097926353729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4059753947358797235138305 3044815460519097926353729)
        ·
          refine ⟨2283611595389323444765297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3044815460519097926353729 2283611595389323444765297)
          ·
            refine ⟨1712708696541992583573973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2283611595389323444765297 1712708696541992583573973)
            ·
              refine ⟨40141610075202951177515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1712708696541992583573973 40141610075202951177515)
              ·
                rfl

theorem cell20_791527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 7].length) (baseStart_791527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791527 prefixEnd_791527 := by exact prefixLift 791527
  have htrace : WordTrace (prefixWord ++ tailWord_791527) baseStart_791527 baseEnd_791527 := by
    simpa [prefixWord, tailWord_791527, baseEnd_791527] using wordTrace_append hprefix tailTrace_791527
  have hstable : (prefixWord ++ tailWord_791527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791527).length < 2 ^ (prefixWord ++ tailWord_791527).sum := by decide
  have hdescent : baseEnd_791527 < baseStart_791527 := by decide
  rcases family_descends (prefixWord ++ tailWord_791527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791530 : List Nat := [3, 1, 3, 1, 2, 4, 1, 2, 3]
def baseStart_791530 : Nat := 118140960795 + 791530 * 2 ^ 59
def prefixEnd_791530 : Nat := 4983230072969 + 3 ^ 40 * 791530 * 2
def baseEnd_791530 : Nat := 361275859958571883497623

theorem tailTrace_791530 : CollatzResearch.WordTrace tailWord_791530 prefixEnd_791530 361275859958571883497623 := by
  unfold tailWord_791530
  simp only [CollatzResearch.WordTrace]
  refine ⟨7217367705607366851669011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19246313881619644937784029 7217367705607366851669011)
  ·
    refine ⟨10826051558411050277503517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7217367705607366851669011 10826051558411050277503517)
    ·
      refine ⟨4059769334404143854063819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10826051558411050277503517 4059769334404143854063819)
      ·
        refine ⟨6089654001606215781095729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4059769334404143854063819 6089654001606215781095729)
        ·
          refine ⟨4567240501204661835821797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6089654001606215781095729 4567240501204661835821797)
          ·
            refine ⟨856357593975874094216587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4567240501204661835821797 856357593975874094216587)
            ·
              refine ⟨1284536390963811141324881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856357593975874094216587 1284536390963811141324881)
              ·
                refine ⟨963402293222858355993661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1284536390963811141324881 963402293222858355993661)
                ·
                  refine ⟨361275859958571883497623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 963402293222858355993661 361275859958571883497623)
                  ·
                    rfl

theorem cell20_791530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 2, 3].length) (baseStart_791530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791530 prefixEnd_791530 := by exact prefixLift 791530
  have htrace : WordTrace (prefixWord ++ tailWord_791530) baseStart_791530 baseEnd_791530 := by
    simpa [prefixWord, tailWord_791530, baseEnd_791530] using wordTrace_append hprefix tailTrace_791530
  have hstable : (prefixWord ++ tailWord_791530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791530).length < 2 ^ (prefixWord ++ tailWord_791530).sum := by decide
  have hdescent : baseEnd_791530 < baseStart_791530 := by decide
  rcases family_descends (prefixWord ++ tailWord_791530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791537 : List Nat := [1, 2, 2, 2, 4, 1, 2, 4, 2]
def baseStart_791537 : Nat := 118140960795 + 791537 * 2 ^ 59
def prefixEnd_791537 : Nat := 4983230072969 + 3 ^ 40 * 791537 * 2
def baseEnd_791537 : Nat := 361279054949310970264261

theorem tailTrace_791537 : CollatzResearch.WordTrace tailWord_791537 prefixEnd_791537 361279054949310970264261 := by
  unfold tailWord_791537
  simp only [CollatzResearch.WordTrace]
  refine ⟨28869726133404107602180865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19246484088936071734787243 28869726133404107602180865)
  ·
    refine ⟨21652294600053080701635649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28869726133404107602180865 21652294600053080701635649)
    ·
      refine ⟨16239220950039810526226737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21652294600053080701635649 16239220950039810526226737)
      ·
        refine ⟨12179415712529857894670053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16239220950039810526226737 12179415712529857894670053)
        ·
          refine ⟨2283640446099348355250635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12179415712529857894670053 2283640446099348355250635)
          ·
            refine ⟨3425460669149022532875953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2283640446099348355250635 3425460669149022532875953)
            ·
              refine ⟨2569095501861766899656965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3425460669149022532875953 2569095501861766899656965)
              ·
                refine ⟨481705406599081293685681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2569095501861766899656965 481705406599081293685681)
                ·
                  refine ⟨361279054949310970264261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 481705406599081293685681 361279054949310970264261)
                  ·
                    rfl

theorem cell20_791537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 2].length) (baseStart_791537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791537 prefixEnd_791537 := by exact prefixLift 791537
  have htrace : WordTrace (prefixWord ++ tailWord_791537) baseStart_791537 baseEnd_791537 := by
    simpa [prefixWord, tailWord_791537, baseEnd_791537] using wordTrace_append hprefix tailTrace_791537
  have hstable : (prefixWord ++ tailWord_791537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791537).length < 2 ^ (prefixWord ++ tailWord_791537).sum := by decide
  have hdescent : baseEnd_791537 < baseStart_791537 := by decide
  rcases family_descends (prefixWord ++ tailWord_791537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791606 : List Nat := [5, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_791606 : Nat := 118140960795 + 791606 * 2 ^ 59
def prefixEnd_791606 : Nat := 4983230072969 + 3 ^ 40 * 791606 * 2
def baseEnd_791606 : Nat := 361310548429453396963979

theorem tailTrace_791606 : CollatzResearch.WordTrace tailWord_791606 prefixEnd_791606 361310548429453396963979 := by
  unfold tailWord_791606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1804515173134633274152667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19248161846769421590961781 1804515173134633274152667)
  ·
    refine ⟨2706772759701949911229001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1804515173134633274152667 2706772759701949911229001)
    ·
      refine ⟨2030079569776462433421751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2706772759701949911229001 2030079569776462433421751)
      ·
        refine ⟨3045119354664693650132627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2030079569776462433421751 3045119354664693650132627)
        ·
          refine ⟨4567679031997040475198941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3045119354664693650132627 4567679031997040475198941)
          ·
            refine ⟨1712879636998890178199603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4567679031997040475198941 1712879636998890178199603)
            ·
              refine ⟨2569319455498335267299405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1712879636998890178199603 2569319455498335267299405)
              ·
                refine ⟨963494795811875725237277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2569319455498335267299405 963494795811875725237277)
                ·
                  refine ⟨361310548429453396963979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 963494795811875725237277 361310548429453396963979)
                  ·
                    rfl

theorem cell20_791606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_791606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791606 prefixEnd_791606 := by exact prefixLift 791606
  have htrace : WordTrace (prefixWord ++ tailWord_791606) baseStart_791606 baseEnd_791606 := by
    simpa [prefixWord, tailWord_791606, baseEnd_791606] using wordTrace_append hprefix tailTrace_791606
  have hstable : (prefixWord ++ tailWord_791606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791606).length < 2 ^ (prefixWord ++ tailWord_791606).sum := by decide
  have hdescent : baseEnd_791606 < baseStart_791606 := by decide
  rcases family_descends (prefixWord ++ tailWord_791606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791624 : List Nat := [2, 1, 3, 1, 1, 1, 3, 8]
def baseStart_791624 : Nat := 118140960795 + 791624 * 2 ^ 59
def prefixEnd_791624 : Nat := 4983230072969 + 3 ^ 40 * 791624 * 2
def baseEnd_791624 : Nat := 120439588039975111454635

theorem tailTrace_791624 : CollatzResearch.WordTrace tailWord_791624 prefixEnd_791624 120439588039975111454635 := by
  unfold tailWord_791624
  simp only [CollatzResearch.WordTrace]
  refine ⟨14436449642044460730298963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19248599522725947640398617 14436449642044460730298963)
  ·
    refine ⟨21654674463066691095448445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14436449642044460730298963 21654674463066691095448445)
    ·
      refine ⟨8120502923650009160793167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21654674463066691095448445 8120502923650009160793167)
      ·
        refine ⟨12180754385475013741189751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8120502923650009160793167 12180754385475013741189751)
        ·
          refine ⟨18271131578212520611784627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12180754385475013741189751 18271131578212520611784627)
          ·
            refine ⟨27406697367318780917676941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18271131578212520611784627 27406697367318780917676941)
            ·
              refine ⟨10277511512744542844128853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27406697367318780917676941 10277511512744542844128853)
              ·
                refine ⟨120439588039975111454635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10277511512744542844128853 120439588039975111454635)
                ·
                  rfl

theorem cell20_791624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_791624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791624 prefixEnd_791624 := by exact prefixLift 791624
  have htrace : WordTrace (prefixWord ++ tailWord_791624) baseStart_791624 baseEnd_791624 := by
    simpa [prefixWord, tailWord_791624, baseEnd_791624] using wordTrace_append hprefix tailTrace_791624
  have hstable : (prefixWord ++ tailWord_791624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791624).length < 2 ^ (prefixWord ++ tailWord_791624).sum := by decide
  have hdescent : baseEnd_791624 < baseStart_791624 := by decide
  rcases family_descends (prefixWord ++ tailWord_791624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791658 : List Nat := [3, 1, 3, 2, 2, 3, 1, 5]
def baseStart_791658 : Nat := 118140960795 + 791658 * 2 ^ 59
def prefixEnd_791658 : Nat := 4983230072969 + 3 ^ 40 * 791658 * 2
def baseEnd_791658 : Nat := 120444760882124109076811

theorem tailTrace_791658 : CollatzResearch.WordTrace tailWord_791658 prefixEnd_791658 120444760882124109076811 := by
  unfold tailWord_791658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7218534841491436316833907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19249426243977163511557085 7218534841491436316833907)
  ·
    refine ⟨10827802262237154475250861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7218534841491436316833907 10827802262237154475250861)
    ·
      refine ⟨4060425848338932928219073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10827802262237154475250861 4060425848338932928219073)
      ·
        refine ⟨3045319386254199696164305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4060425848338932928219073 3045319386254199696164305)
        ·
          refine ⟨2283989539690649772123229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3045319386254199696164305 2283989539690649772123229)
          ·
            refine ⟨856496077383993664546211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2283989539690649772123229 856496077383993664546211)
            ·
              refine ⟨1284744116075990496819317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856496077383993664546211 1284744116075990496819317)
              ·
                refine ⟨120444760882124109076811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1284744116075990496819317 120444760882124109076811)
                ·
                  rfl

theorem cell20_791658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_791658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791658 prefixEnd_791658 := by exact prefixLift 791658
  have htrace : WordTrace (prefixWord ++ tailWord_791658) baseStart_791658 baseEnd_791658 := by
    simpa [prefixWord, tailWord_791658, baseEnd_791658] using wordTrace_append hprefix tailTrace_791658
  have hstable : (prefixWord ++ tailWord_791658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791658).length < 2 ^ (prefixWord ++ tailWord_791658).sum := by decide
  have hdescent : baseEnd_791658 < baseStart_791658 := by decide
  rcases family_descends (prefixWord ++ tailWord_791658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791689 : List Nat := [1, 2, 1, 1, 4, 4, 2, 3, 2]
def baseStart_791689 : Nat := 118140960795 + 791689 * 2 ^ 59
def prefixEnd_791689 : Nat := 4983230072969 + 3 ^ 40 * 791689 * 2
def baseEnd_791689 : Nat := 361348431891073997196973

theorem tailTrace_791689 : CollatzResearch.WordTrace tailWord_791689 prefixEnd_791689 361348431891073997196973 := by
  unfold tailWord_791689
  simp only [CollatzResearch.WordTrace]
  refine ⟨28875270028853437561714121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19250180019235625041142747 28875270028853437561714121)
  ·
    refine ⟨21656452521640078171285591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28875270028853437561714121 21656452521640078171285591)
    ·
      refine ⟨32484678782460117256928387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21656452521640078171285591 32484678782460117256928387)
      ·
        refine ⟨48727018173690175885392581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32484678782460117256928387 48727018173690175885392581)
        ·
          refine ⟨9136315907566907978511109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48727018173690175885392581 9136315907566907978511109)
          ·
            refine ⟨1713059232668795245970833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9136315907566907978511109 1713059232668795245970833)
            ·
              refine ⟨1284794424501596434478125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1713059232668795245970833 1284794424501596434478125)
              ·
                refine ⟨481797909188098662929297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1284794424501596434478125 481797909188098662929297)
                ·
                  refine ⟨361348431891073997196973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 481797909188098662929297 361348431891073997196973)
                  ·
                    rfl

theorem cell20_791689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 2].length) (baseStart_791689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791689 prefixEnd_791689 := by exact prefixLift 791689
  have htrace : WordTrace (prefixWord ++ tailWord_791689) baseStart_791689 baseEnd_791689 := by
    simpa [prefixWord, tailWord_791689, baseEnd_791689] using wordTrace_append hprefix tailTrace_791689
  have hstable : (prefixWord ++ tailWord_791689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791689).length < 2 ^ (prefixWord ++ tailWord_791689).sum := by decide
  have hdescent : baseEnd_791689 < baseStart_791689 := by decide
  rcases family_descends (prefixWord ++ tailWord_791689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791703 : List Nat := [1, 1, 3, 3, 3, 1, 3, 2, 3]
def baseStart_791703 : Nat := 118140960795 + 791703 * 2 ^ 59
def prefixEnd_791703 : Nat := 4983230072969 + 3 ^ 40 * 791703 * 2
def baseEnd_791703 : Nat := 361354821872552170730249

theorem tailTrace_791703 : CollatzResearch.WordTrace tailWord_791703 prefixEnd_791703 361354821872552170730249 := by
  unfold tailWord_791703
  simp only [CollatzResearch.WordTrace]
  refine ⟨28875780650802717952723763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19250520433868478635149175 28875780650802717952723763)
  ·
    refine ⟨43313670976204076929085645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28875780650802717952723763 43313670976204076929085645)
    ·
      refine ⟨16242626616076528848407117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43313670976204076929085645 16242626616076528848407117)
      ·
        refine ⟨6090984981028698318152669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16242626616076528848407117 6090984981028698318152669)
        ·
          refine ⟨2284119367885761869307251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6090984981028698318152669 2284119367885761869307251)
          ·
            refine ⟨3426179051828642803960877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2284119367885761869307251 3426179051828642803960877)
            ·
              refine ⟨1284817144435741051485329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3426179051828642803960877 1284817144435741051485329)
              ·
                refine ⟨963612858326805788613997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1284817144435741051485329 963612858326805788613997)
                ·
                  refine ⟨361354821872552170730249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 963612858326805788613997 361354821872552170730249)
                  ·
                    rfl

theorem cell20_791703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 3].length) (baseStart_791703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791703 prefixEnd_791703 := by exact prefixLift 791703
  have htrace : WordTrace (prefixWord ++ tailWord_791703) baseStart_791703 baseEnd_791703 := by
    simpa [prefixWord, tailWord_791703, baseEnd_791703] using wordTrace_append hprefix tailTrace_791703
  have hstable : (prefixWord ++ tailWord_791703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791703).length < 2 ^ (prefixWord ++ tailWord_791703).sum := by decide
  have hdescent : baseEnd_791703 < baseStart_791703 := by decide
  rcases family_descends (prefixWord ++ tailWord_791703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791731 : List Nat := [1, 1, 1, 2, 3, 2, 4, 2, 4]
def baseStart_791731 : Nat := 118140960795 + 791731 * 2 ^ 59
def prefixEnd_791731 : Nat := 4983230072969 + 3 ^ 40 * 791731 * 2
def baseEnd_791731 : Nat := 361367601835508517796801

theorem tailTrace_791731 : CollatzResearch.WordTrace tailWord_791731 prefixEnd_791731 361367601835508517796801 := by
  unfold tailWord_791731
  simp only [CollatzResearch.WordTrace]
  refine ⟨28876801894701278734743047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19251201263134185823162031 28876801894701278734743047)
  ·
    refine ⟨43315202842051918102114571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28876801894701278734743047 43315202842051918102114571)
    ·
      refine ⟨64972804263077877153171857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43315202842051918102114571 64972804263077877153171857)
      ·
        refine ⟨48729603197308407864878893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64972804263077877153171857 48729603197308407864878893)
        ·
          refine ⟨18273601198990652949329585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48729603197308407864878893 18273601198990652949329585)
          ·
            refine ⟨13705200899242989711997189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18273601198990652949329585 13705200899242989711997189)
            ·
              refine ⟨2569725168608060570999473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13705200899242989711997189 2569725168608060570999473)
              ·
                refine ⟨1927293876456045428249605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2569725168608060570999473 1927293876456045428249605)
                ·
                  refine ⟨361367601835508517796801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1927293876456045428249605 361367601835508517796801)
                  ·
                    rfl

theorem cell20_791731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_791731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791731 prefixEnd_791731 := by exact prefixLift 791731
  have htrace : WordTrace (prefixWord ++ tailWord_791731) baseStart_791731 baseEnd_791731 := by
    simpa [prefixWord, tailWord_791731, baseEnd_791731] using wordTrace_append hprefix tailTrace_791731
  have hstable : (prefixWord ++ tailWord_791731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791731).length < 2 ^ (prefixWord ++ tailWord_791731).sum := by decide
  have hdescent : baseEnd_791731 < baseStart_791731 := by decide
  rcases family_descends (prefixWord ++ tailWord_791731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791744 : List Nat := [2, 1, 1, 2, 6, 2, 1, 3, 2]
def baseStart_791744 : Nat := 118140960795 + 791744 * 2 ^ 59
def prefixEnd_791744 : Nat := 4983230072969 + 3 ^ 40 * 791744 * 2
def baseEnd_791744 : Nat := 361373535389738250363415

theorem tailTrace_791744 : CollatzResearch.WordTrace tailWord_791744 prefixEnd_791744 361373535389738250363415 := by
  unfold tailWord_791744
  simp only [CollatzResearch.WordTrace]
  refine ⟨14438638021827090977483143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19251517362436121303310857 14438638021827090977483143)
  ·
    refine ⟨21657957032740636466224715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14438638021827090977483143 21657957032740636466224715)
    ·
      refine ⟨32486935549110954699337073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21657957032740636466224715 32486935549110954699337073)
      ·
        refine ⟨24365201661833216024502805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32486935549110954699337073 24365201661833216024502805)
        ·
          refine ⟨1142118827898432001148569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24365201661833216024502805 1142118827898432001148569)
          ·
            refine ⟨856589120923824000861427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1142118827898432001148569 856589120923824000861427)
            ·
              refine ⟨1284883681385736001292141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856589120923824000861427 1284883681385736001292141)
              ·
                refine ⟨481831380519651000484553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1284883681385736001292141 481831380519651000484553)
                ·
                  refine ⟨361373535389738250363415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 481831380519651000484553 361373535389738250363415)
                  ·
                    rfl

theorem cell20_791744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3, 2].length) (baseStart_791744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791744 prefixEnd_791744 := by exact prefixLift 791744
  have htrace : WordTrace (prefixWord ++ tailWord_791744) baseStart_791744 baseEnd_791744 := by
    simpa [prefixWord, tailWord_791744, baseEnd_791744] using wordTrace_append hprefix tailTrace_791744
  have hstable : (prefixWord ++ tailWord_791744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791744).length < 2 ^ (prefixWord ++ tailWord_791744).sum := by decide
  have hdescent : baseEnd_791744 < baseStart_791744 := by decide
  rcases family_descends (prefixWord ++ tailWord_791744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791762 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_791762 : Nat := 118140960795 + 791762 * 2 ^ 59
def prefixEnd_791762 : Nat := 4983230072969 + 3 ^ 40 * 791762 * 2
def baseEnd_791762 : Nat := 361381751080210187763341

theorem tailTrace_791762 : CollatzResearch.WordTrace tailWord_791762 prefixEnd_791762 361381751080210187763341 := by
  unfold tailWord_791762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7219483139397242757280385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19251955038392647352747693 7219483139397242757280385)
  ·
    refine ⟨5414612354547932067960289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7219483139397242757280385 5414612354547932067960289)
    ·
      refine ⟨4060959265910949050970217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5414612354547932067960289 4060959265910949050970217)
      ·
        refine ⟨3045719449433211788227663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4060959265910949050970217 3045719449433211788227663)
        ·
          refine ⟨4568579174149817682341495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3045719449433211788227663 4568579174149817682341495)
          ·
            refine ⟨6852868761224726523512243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4568579174149817682341495 6852868761224726523512243)
            ·
              refine ⟨10279303141837089785268365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6852868761224726523512243 10279303141837089785268365)
              ·
                refine ⟨3854738678188908669475637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10279303141837089785268365 3854738678188908669475637)
                ·
                  refine ⟨361381751080210187763341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3854738678188908669475637 361381751080210187763341)
                  ·
                    rfl

theorem cell20_791762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_791762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791762 prefixEnd_791762 := by exact prefixLift 791762
  have htrace : WordTrace (prefixWord ++ tailWord_791762) baseStart_791762 baseEnd_791762 := by
    simpa [prefixWord, tailWord_791762, baseEnd_791762] using wordTrace_append hprefix tailTrace_791762
  have hstable : (prefixWord ++ tailWord_791762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791762).length < 2 ^ (prefixWord ++ tailWord_791762).sum := by decide
  have hdescent : baseEnd_791762 < baseStart_791762 := by decide
  rcases family_descends (prefixWord ++ tailWord_791762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791765 : List Nat := [1, 3, 2, 4, 1, 3, 1, 1, 4]
def baseStart_791765 : Nat := 118140960795 + 791765 * 2 ^ 59
def prefixEnd_791765 : Nat := 4983230072969 + 3 ^ 40 * 791765 * 2
def baseEnd_791765 : Nat := 361383120361955510663329

theorem tailTrace_791765 : CollatzResearch.WordTrace tailWord_791765 prefixEnd_791765 361383120361955510663329 := by
  unfold tailWord_791765
  simp only [CollatzResearch.WordTrace]
  refine ⟨28878041976578102541480749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19252027984385401694320499 28878041976578102541480749)
  ·
    refine ⟨10829265741216788453055281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28878041976578102541480749 10829265741216788453055281)
    ·
      refine ⟨8121949305912591339791461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10829265741216788453055281 8121949305912591339791461)
      ·
        refine ⟨1522865494858610876210899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8121949305912591339791461 1522865494858610876210899)
        ·
          refine ⟨2284298242287916314316349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1522865494858610876210899 2284298242287916314316349)
          ·
            refine ⟨856611840857968617868631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2284298242287916314316349 856611840857968617868631)
            ·
              refine ⟨1284917761286952926802947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856611840857968617868631 1284917761286952926802947)
              ·
                refine ⟨1927376641930429390204421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1284917761286952926802947 1927376641930429390204421)
                ·
                  refine ⟨361383120361955510663329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1927376641930429390204421 361383120361955510663329)
                  ·
                    rfl

theorem cell20_791765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_791765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791765 prefixEnd_791765 := by exact prefixLift 791765
  have htrace : WordTrace (prefixWord ++ tailWord_791765) baseStart_791765 baseEnd_791765 := by
    simpa [prefixWord, tailWord_791765, baseEnd_791765] using wordTrace_append hprefix tailTrace_791765
  have hstable : (prefixWord ++ tailWord_791765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791765).length < 2 ^ (prefixWord ++ tailWord_791765).sum := by decide
  have hdescent : baseEnd_791765 < baseStart_791765 := by decide
  rcases family_descends (prefixWord ++ tailWord_791765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791776 : List Nat := [2, 1, 1, 3, 1, 4, 1, 7]
def baseStart_791776 : Nat := 118140960795 + 791776 * 2 ^ 59
def prefixEnd_791776 : Nat := 4983230072969 + 3 ^ 40 * 791776 * 2
def baseEnd_791776 : Nat := 120462713687229453765539

theorem tailTrace_791776 : CollatzResearch.WordTrace tailWord_791776 prefixEnd_791776 120462713687229453765539 := by
  unfold tailWord_791776
  simp only [CollatzResearch.WordTrace]
  refine ⟨14439221589769125710065591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19252295453025500946754121 14439221589769125710065591)
  ·
    refine ⟨21658832384653688565098387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14439221589769125710065591 21658832384653688565098387)
    ·
      refine ⟨32488248576980532847647581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21658832384653688565098387 32488248576980532847647581)
      ·
        refine ⟨12183093216367699817867843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32488248576980532847647581 12183093216367699817867843)
        ·
          refine ⟨18274639824551549726801765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12183093216367699817867843 18274639824551549726801765)
          ·
            refine ⟨3426494967103415573775331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18274639824551549726801765 3426494967103415573775331)
            ·
              refine ⟨5139742450655123360662997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3426494967103415573775331 5139742450655123360662997)
              ·
                refine ⟨120462713687229453765539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5139742450655123360662997 120462713687229453765539)
                ·
                  rfl

theorem cell20_791776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_791776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791776 prefixEnd_791776 := by exact prefixLift 791776
  have htrace : WordTrace (prefixWord ++ tailWord_791776) baseStart_791776 baseEnd_791776 := by
    simpa [prefixWord, tailWord_791776, baseEnd_791776] using wordTrace_append hprefix tailTrace_791776
  have hstable : (prefixWord ++ tailWord_791776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791776).length < 2 ^ (prefixWord ++ tailWord_791776).sum := by decide
  have hdescent : baseEnd_791776 < baseStart_791776 := by decide
  rcases family_descends (prefixWord ++ tailWord_791776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791810 : List Nat := [3, 4, 1, 1, 4, 7]
def baseStart_791810 : Nat := 118140960795 + 791810 * 2 ^ 59
def prefixEnd_791810 : Nat := 4983230072969 + 3 ^ 40 * 791810 * 2
def baseEnd_791810 : Nat := 13385320725486494598635

theorem tailTrace_791810 : CollatzResearch.WordTrace tailWord_791810 prefixEnd_791810 13385320725486494598635 := by
  unfold tailWord_791810
  simp only [CollatzResearch.WordTrace]
  refine ⟨7219920815353768806717221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19253122174276716817912589 7219920815353768806717221)
  ·
    refine ⟨1353735152878831651259479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7219920815353768806717221 1353735152878831651259479)
    ·
      refine ⟨2030602729318247476889219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1353735152878831651259479 2030602729318247476889219)
      ·
        refine ⟨3045904093977371215333829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2030602729318247476889219 3045904093977371215333829)
        ·
          refine ⟨571107017620757102875093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3045904093977371215333829 571107017620757102875093)
          ·
            refine ⟨13385320725486494598635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 571107017620757102875093 13385320725486494598635)
            ·
              rfl

theorem cell20_791810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 7].length) (baseStart_791810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791810 prefixEnd_791810 := by exact prefixLift 791810
  have htrace : WordTrace (prefixWord ++ tailWord_791810) baseStart_791810 baseEnd_791810 := by
    simpa [prefixWord, tailWord_791810, baseEnd_791810] using wordTrace_append hprefix tailTrace_791810
  have hstable : (prefixWord ++ tailWord_791810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791810).length < 2 ^ (prefixWord ++ tailWord_791810).sum := by decide
  have hdescent : baseEnd_791810 < baseStart_791810 := by decide
  rcases family_descends (prefixWord ++ tailWord_791810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791820 : List Nat := [2, 2, 1, 2, 2, 5, 2, 2, 2]
def baseStart_791820 : Nat := 118140960795 + 791820 * 2 ^ 59
def prefixEnd_791820 : Nat := 4983230072969 + 3 ^ 40 * 791820 * 2
def baseEnd_791820 : Nat := 361408223860619763829771

theorem tailTrace_791820 : CollatzResearch.WordTrace tailWord_791820 prefixEnd_791820 361408223860619763829771 := by
  unfold tailWord_791820
  simp only [CollatzResearch.WordTrace]
  refine ⟨14440023995689423467366457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19253365327585897956488609 14440023995689423467366457)
  ·
    refine ⟨10830017996767067600524843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14440023995689423467366457 10830017996767067600524843)
    ·
      refine ⟨16245026995150601400787265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10830017996767067600524843 16245026995150601400787265)
      ·
        refine ⟨12183770246362951050590449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16245026995150601400787265 12183770246362951050590449)
        ·
          refine ⟨9137827684772213287942837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12183770246362951050590449 9137827684772213287942837)
          ·
            refine ⟨856671345447394995744641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9137827684772213287942837 856671345447394995744641)
            ·
              refine ⟨642503509085546246808481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 856671345447394995744641 642503509085546246808481)
              ·
                refine ⟨481877631814159685106361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 642503509085546246808481 481877631814159685106361)
                ·
                  refine ⟨361408223860619763829771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 481877631814159685106361 361408223860619763829771)
                  ·
                    rfl

theorem cell20_791820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 2].length) (baseStart_791820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791820 prefixEnd_791820 := by exact prefixLift 791820
  have htrace : WordTrace (prefixWord ++ tailWord_791820) baseStart_791820 baseEnd_791820 := by
    simpa [prefixWord, tailWord_791820, baseEnd_791820] using wordTrace_append hprefix tailTrace_791820
  have hstable : (prefixWord ++ tailWord_791820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791820).length < 2 ^ (prefixWord ++ tailWord_791820).sum := by decide
  have hdescent : baseEnd_791820 < baseStart_791820 := by decide
  rcases family_descends (prefixWord ++ tailWord_791820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791845 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 6]
def baseStart_791845 : Nat := 118140960795 + 791845 * 2 ^ 59
def prefixEnd_791845 : Nat := 4983230072969 + 3 ^ 40 * 791845 * 2
def baseEnd_791845 : Nat := 361419634541830787996335

theorem tailTrace_791845 : CollatzResearch.WordTrace tailWord_791845 prefixEnd_791845 361419634541830787996335 := by
  unfold tailWord_791845
  simp only [CollatzResearch.WordTrace]
  refine ⟨28880959816288276204392989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19253973210858850802928659 28880959816288276204392989)
  ·
    refine ⟨10830359931108103576647371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28880959816288276204392989 10830359931108103576647371)
    ·
      refine ⟨16245539896662155364971057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10830359931108103576647371 16245539896662155364971057)
      ·
        refine ⟨12184154922496616523728293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16245539896662155364971057 12184154922496616523728293)
        ·
          refine ⟨2284529047968115598199055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12184154922496616523728293 2284529047968115598199055)
          ·
            refine ⟨3426793571952173397298583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2284529047968115598199055 3426793571952173397298583)
            ·
              refine ⟨5140190357928260095947875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3426793571952173397298583 5140190357928260095947875)
              ·
                refine ⟨7710285536892390143921813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5140190357928260095947875 7710285536892390143921813)
                ·
                  refine ⟨361419634541830787996335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7710285536892390143921813 361419634541830787996335)
                  ·
                    rfl

theorem cell20_791845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_791845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791845 prefixEnd_791845 := by exact prefixLift 791845
  have htrace : WordTrace (prefixWord ++ tailWord_791845) baseStart_791845 baseEnd_791845 := by
    simpa [prefixWord, tailWord_791845, baseEnd_791845] using wordTrace_append hprefix tailTrace_791845
  have hstable : (prefixWord ++ tailWord_791845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791845).length < 2 ^ (prefixWord ++ tailWord_791845).sum := by decide
  have hdescent : baseEnd_791845 < baseStart_791845 := by decide
  rcases family_descends (prefixWord ++ tailWord_791845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791848 : List Nat := [2, 1, 5, 1, 2, 2, 3, 4]
def baseStart_791848 : Nat := 118140960795 + 791848 * 2 ^ 59
def prefixEnd_791848 : Nat := 4983230072969 + 3 ^ 40 * 791848 * 2
def baseEnd_791848 : Nat := 120473667941192036965441

theorem tailTrace_791848 : CollatzResearch.WordTrace tailWord_791848 prefixEnd_791848 120473667941192036965441 := by
  unfold tailWord_791848
  simp only [CollatzResearch.WordTrace]
  refine ⟨14440534617638703858376099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19254046156851605144501465 14440534617638703858376099)
  ·
    refine ⟨21660801926458055787564149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14440534617638703858376099 21660801926458055787564149)
    ·
      refine ⟨2030700180605442730084139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21660801926458055787564149 2030700180605442730084139)
      ·
        refine ⟨3046050270908164095126209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2030700180605442730084139 3046050270908164095126209)
        ·
          refine ⟨2284537703181123071344657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3046050270908164095126209 2284537703181123071344657)
          ·
            refine ⟨1713403277385842303508493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2284537703181123071344657 1713403277385842303508493)
            ·
              refine ⟨642526229019690863815685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1713403277385842303508493 642526229019690863815685)
              ·
                refine ⟨120473667941192036965441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 642526229019690863815685 120473667941192036965441)
                ·
                  rfl

theorem cell20_791848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 4].length) (baseStart_791848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791848 prefixEnd_791848 := by exact prefixLift 791848
  have htrace : WordTrace (prefixWord ++ tailWord_791848) baseStart_791848 baseEnd_791848 := by
    simpa [prefixWord, tailWord_791848, baseEnd_791848] using wordTrace_append hprefix tailTrace_791848
  have hstable : (prefixWord ++ tailWord_791848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791848).length < 2 ^ (prefixWord ++ tailWord_791848).sum := by decide
  have hdescent : baseEnd_791848 < baseStart_791848 := by decide
  rcases family_descends (prefixWord ++ tailWord_791848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791890 : List Nat := [3, 2, 2, 1, 1, 1, 1, 9]
def baseStart_791890 : Nat := 118140960795 + 791890 * 2 ^ 59
def prefixEnd_791890 : Nat := 4983230072969 + 3 ^ 40 * 791890 * 2
def baseEnd_791890 : Nat := 120480057922670210498717

theorem tailTrace_791890 : CollatzResearch.WordTrace tailWord_791890 prefixEnd_791890 120480057922670210498717 := by
  unfold tailWord_791890
  simp only [CollatzResearch.WordTrace]
  refine ⟨7220650275281312222445281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19255067400750165926520749 7220650275281312222445281)
  ·
    refine ⟨5415487706460984166833961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7220650275281312222445281 5415487706460984166833961)
    ·
      refine ⟨4061615779845738125125471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5415487706460984166833961 4061615779845738125125471)
      ·
        refine ⟨6092423669768607187688207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4061615779845738125125471 6092423669768607187688207)
        ·
          refine ⟨9138635504652910781532311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6092423669768607187688207 9138635504652910781532311)
          ·
            refine ⟨13707953256979366172298467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9138635504652910781532311 13707953256979366172298467)
            ·
              refine ⟨20561929885469049258447701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13707953256979366172298467 20561929885469049258447701)
              ·
                refine ⟨120480057922670210498717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20561929885469049258447701 120480057922670210498717)
                ·
                  rfl

theorem cell20_791890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_791890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791890 prefixEnd_791890 := by exact prefixLift 791890
  have htrace : WordTrace (prefixWord ++ tailWord_791890) baseStart_791890 baseEnd_791890 := by
    simpa [prefixWord, tailWord_791890, baseEnd_791890] using wordTrace_append hprefix tailTrace_791890
  have hstable : (prefixWord ++ tailWord_791890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791890).length < 2 ^ (prefixWord ++ tailWord_791890).sum := by decide
  have hdescent : baseEnd_791890 < baseStart_791890 := by decide
  rcases family_descends (prefixWord ++ tailWord_791890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791907 : List Nat := [1, 1, 1, 5, 2, 2, 4, 4]
def baseStart_791907 : Nat := 118140960795 + 791907 * 2 ^ 59
def prefixEnd_791907 : Nat := 4983230072969 + 3 ^ 40 * 791907 * 2
def baseEnd_791907 : Nat := 120482644343744709309805

theorem tailTrace_791907 : CollatzResearch.WordTrace tailWord_791907 prefixEnd_791907 120482644343744709309805 := by
  unfold tailWord_791907
  simp only [CollatzResearch.WordTrace]
  refine ⟨28883221142063660793149975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19255480761375773862099983 28883221142063660793149975)
  ·
    refine ⟨43324831713095491189724963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28883221142063660793149975 43324831713095491189724963)
    ·
      refine ⟨64987247569643236784587445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43324831713095491189724963 64987247569643236784587445)
      ·
        refine ⟨6092554459654053448555073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64987247569643236784587445 6092554459654053448555073)
        ·
          refine ⟨4569415844740540086416305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6092554459654053448555073 4569415844740540086416305)
          ·
            refine ⟨3427061883555405064812229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4569415844740540086416305 3427061883555405064812229)
            ·
              refine ⟨642574103166638449652293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3427061883555405064812229 642574103166638449652293)
              ·
                refine ⟨120482644343744709309805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 642574103166638449652293 120482644343744709309805)
                ·
                  rfl

theorem cell20_791907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 4, 4].length) (baseStart_791907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791907 prefixEnd_791907 := by exact prefixLift 791907
  have htrace : WordTrace (prefixWord ++ tailWord_791907) baseStart_791907 baseEnd_791907 := by
    simpa [prefixWord, tailWord_791907, baseEnd_791907] using wordTrace_append hprefix tailTrace_791907
  have hstable : (prefixWord ++ tailWord_791907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791907).length < 2 ^ (prefixWord ++ tailWord_791907).sum := by decide
  have hdescent : baseEnd_791907 < baseStart_791907 := by decide
  rcases family_descends (prefixWord ++ tailWord_791907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791917 : List Nat := [1, 5, 1, 1, 1, 3, 3, 3, 2]
def baseStart_791917 : Nat := 118140960795 + 791917 * 2 ^ 59
def prefixEnd_791917 : Nat := 4983230072969 + 3 ^ 40 * 791917 * 2
def baseEnd_791917 : Nat := 361452497303718537596041

theorem tailTrace_791917 : CollatzResearch.WordTrace tailWord_791917 prefixEnd_791917 361452497303718537596041 := by
  unfold tailWord_791917
  simp only [CollatzResearch.WordTrace]
  refine ⟨28883585872027432501014005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19255723914684955000676003 28883585872027432501014005)
  ·
    refine ⟨2707836175502571796970063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28883585872027432501014005 2707836175502571796970063)
    ·
      refine ⟨4061754263253857695455095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2707836175502571796970063 4061754263253857695455095)
      ·
        refine ⟨6092631394880786543182643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4061754263253857695455095 6092631394880786543182643)
        ·
          refine ⟨9138947092321179814773965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6092631394880786543182643 9138947092321179814773965)
          ·
            refine ⟨3427105159620442430540237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9138947092321179814773965 3427105159620442430540237)
            ·
              refine ⟨1285164434857665911452589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3427105159620442430540237 1285164434857665911452589)
              ·
                refine ⟨481936663071624716794721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1285164434857665911452589 481936663071624716794721)
                ·
                  refine ⟨361452497303718537596041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 481936663071624716794721 361452497303718537596041)
                  ·
                    rfl

theorem cell20_791917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_791917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791917 prefixEnd_791917 := by exact prefixLift 791917
  have htrace : WordTrace (prefixWord ++ tailWord_791917) baseStart_791917 baseEnd_791917 := by
    simpa [prefixWord, tailWord_791917, baseEnd_791917] using wordTrace_append hprefix tailTrace_791917
  have hstable : (prefixWord ++ tailWord_791917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791917).length < 2 ^ (prefixWord ++ tailWord_791917).sum := by decide
  have hdescent : baseEnd_791917 < baseStart_791917 := by decide
  rcases family_descends (prefixWord ++ tailWord_791917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791945 : List Nat := [1, 2, 1, 1, 7, 1, 2, 5]
def baseStart_791945 : Nat := 118140960795 + 791945 * 2 ^ 59
def prefixEnd_791945 : Nat := 4983230072969 + 3 ^ 40 * 791945 * 2
def baseEnd_791945 : Nat := 120488425755558294887531

theorem tailTrace_791945 : CollatzResearch.WordTrace tailWord_791945 prefixEnd_791945 120488425755558294887531 := by
  unfold tailWord_791945
  simp only [CollatzResearch.WordTrace]
  refine ⟨28884607115925993283033289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19256404743950662188688859 28884607115925993283033289)
  ·
    refine ⟨21663455336944494962274967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28884607115925993283033289 21663455336944494962274967)
    ·
      refine ⟨32495183005416742443412451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21663455336944494962274967 32495183005416742443412451)
      ·
        refine ⟨48742774508125113665118677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32495183005416742443412451 48742774508125113665118677)
        ·
          refine ⟨1142408777534182351526219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 48742774508125113665118677 1142408777534182351526219)
          ·
            refine ⟨1713613166301273527289329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142408777534182351526219 1713613166301273527289329)
            ·
              refine ⟨1285209874725955145466997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1713613166301273527289329 1285209874725955145466997)
              ·
                refine ⟨120488425755558294887531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1285209874725955145466997 120488425755558294887531)
                ·
                  rfl

theorem cell20_791945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 5].length) (baseStart_791945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791945 prefixEnd_791945 := by exact prefixLift 791945
  have htrace : WordTrace (prefixWord ++ tailWord_791945) baseStart_791945 baseEnd_791945 := by
    simpa [prefixWord, tailWord_791945, baseEnd_791945] using wordTrace_append hprefix tailTrace_791945
  have hstable : (prefixWord ++ tailWord_791945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791945).length < 2 ^ (prefixWord ++ tailWord_791945).sum := by decide
  have hdescent : baseEnd_791945 < baseStart_791945 := by decide
  rcases family_descends (prefixWord ++ tailWord_791945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791973 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 5]
def baseStart_791973 : Nat := 118140960795 + 791973 * 2 ^ 59
def prefixEnd_791973 : Nat := 4983230072969 + 3 ^ 40 * 791973 * 2
def baseEnd_791973 : Nat := 361478057229631231729145

theorem tailTrace_791973 : CollatzResearch.WordTrace tailWord_791973 prefixEnd_791973 361478057229631231729145 := by
  unfold tailWord_791973
  simp only [CollatzResearch.WordTrace]
  refine ⟨28885628359824554065052573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19257085573216369376701715 28885628359824554065052573)
  ·
    refine ⟨10832110634934207774394715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28885628359824554065052573 10832110634934207774394715)
    ·
      refine ⟨16248165952401311661592073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10832110634934207774394715 16248165952401311661592073)
      ·
        refine ⟨12186124464300983746194055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16248165952401311661592073 12186124464300983746194055)
        ·
          refine ⟨18279186696451475619291083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12186124464300983746194055 18279186696451475619291083)
          ·
            refine ⟨27418780044677213428936625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18279186696451475619291083 27418780044677213428936625)
            ·
              refine ⟨20564085033507910071702469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27418780044677213428936625 20564085033507910071702469)
              ·
                refine ⟨3855765943782733138444213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20564085033507910071702469 3855765943782733138444213)
                ·
                  refine ⟨361478057229631231729145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3855765943782733138444213 361478057229631231729145)
                  ·
                    rfl

theorem cell20_791973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_791973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791973 prefixEnd_791973 := by exact prefixLift 791973
  have htrace : WordTrace (prefixWord ++ tailWord_791973) baseStart_791973 baseEnd_791973 := by
    simpa [prefixWord, tailWord_791973, baseEnd_791973] using wordTrace_append hprefix tailTrace_791973
  have hstable : (prefixWord ++ tailWord_791973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791973).length < 2 ^ (prefixWord ++ tailWord_791973).sum := by decide
  have hdescent : baseEnd_791973 < baseStart_791973 := by decide
  rcases family_descends (prefixWord ++ tailWord_791973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791993 : List Nat := [1, 2, 1, 4, 4, 1, 1, 4, 2]
def baseStart_791993 : Nat := 118140960795 + 791993 * 2 ^ 59
def prefixEnd_791993 : Nat := 4983230072969 + 3 ^ 40 * 791993 * 2
def baseEnd_791993 : Nat := 361487185774600051062397

theorem tailTrace_791993 : CollatzResearch.WordTrace tailWord_791993 prefixEnd_791993 361487185774600051062397 := by
  unfold tailWord_791993
  simp only [CollatzResearch.WordTrace]
  refine ⟨28886357819752097480780633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19257571879834731653853755 28886357819752097480780633)
  ·
    refine ⟨21664768364814073110585475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28886357819752097480780633 21664768364814073110585475)
    ·
      refine ⟨32497152547221109665878213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21664768364814073110585475 32497152547221109665878213)
      ·
        refine ⟨6093216102603958062352165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32497152547221109665878213 6093216102603958062352165)
        ·
          refine ⟨1142478019238242136691031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6093216102603958062352165 1142478019238242136691031)
          ·
            refine ⟨1713717028857363205036547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142478019238242136691031 1713717028857363205036547)
            ·
              refine ⟨2570575543286044807554821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1713717028857363205036547 2570575543286044807554821)
              ·
                refine ⟨481982914366133401416529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2570575543286044807554821 481982914366133401416529)
                ·
                  refine ⟨361487185774600051062397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 481982914366133401416529 361487185774600051062397)
                  ·
                    rfl

theorem cell20_791993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 2].length) (baseStart_791993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791993 prefixEnd_791993 := by exact prefixLift 791993
  have htrace : WordTrace (prefixWord ++ tailWord_791993) baseStart_791993 baseEnd_791993 := by
    simpa [prefixWord, tailWord_791993, baseEnd_791993] using wordTrace_append hprefix tailTrace_791993
  have hstable : (prefixWord ++ tailWord_791993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791993).length < 2 ^ (prefixWord ++ tailWord_791993).sum := by decide
  have hdescent : baseEnd_791993 < baseStart_791993 := by decide
  rcases family_descends (prefixWord ++ tailWord_791993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791997 : List Nat := [1, 4, 1, 2, 2, 1, 2, 3, 4]
def baseStart_791997 : Nat := 118140960795 + 791997 * 2 ^ 59
def prefixEnd_791997 : Nat := 4983230072969 + 3 ^ 40 * 791997 * 2
def baseEnd_791997 : Nat := 361489011483593814929047

theorem tailTrace_791997 : CollatzResearch.WordTrace tailWord_791997 prefixEnd_791997 361489011483593814929047 := by
  unfold tailWord_791997
  simp only [CollatzResearch.WordTrace]
  refine ⟨28886503711737606163926245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19257669141158404109284163 28886503711737606163926245)
  ·
    refine ⟨5416219445950801155736171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28886503711737606163926245 5416219445950801155736171)
    ·
      refine ⟨8124329168926201733604257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5416219445950801155736171 8124329168926201733604257)
      ·
        refine ⟨6093246876694651300203193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8124329168926201733604257 6093246876694651300203193)
        ·
          refine ⟨4569935157520988475152395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6093246876694651300203193 4569935157520988475152395)
          ·
            refine ⟨6854902736281482712728593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4569935157520988475152395 6854902736281482712728593)
            ·
              refine ⟨5141177052211112034546445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6854902736281482712728593 5141177052211112034546445)
              ·
                refine ⟨1927941394579167012954917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5141177052211112034546445 1927941394579167012954917)
                ·
                  refine ⟨361489011483593814929047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1927941394579167012954917 361489011483593814929047)
                  ·
                    rfl

theorem cell20_791997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_791997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_791997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_791997 prefixEnd_791997 := by exact prefixLift 791997
  have htrace : WordTrace (prefixWord ++ tailWord_791997) baseStart_791997 baseEnd_791997 := by
    simpa [prefixWord, tailWord_791997, baseEnd_791997] using wordTrace_append hprefix tailTrace_791997
  have hstable : (prefixWord ++ tailWord_791997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791997).length < 2 ^ (prefixWord ++ tailWord_791997).sum := by decide
  have hdescent : baseEnd_791997 < baseStart_791997 := by decide
  rcases family_descends (prefixWord ++ tailWord_791997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792021 : List Nat := [1, 3, 2, 3, 1, 1, 5, 4]
def baseStart_792021 : Nat := 118140960795 + 792021 * 2 ^ 59
def prefixEnd_792021 : Nat := 4983230072969 + 3 ^ 40 * 792021 * 2
def baseEnd_792021 : Nat := 120499988579185466042983

theorem tailTrace_792021 : CollatzResearch.WordTrace tailWord_792021 prefixEnd_792021 120499988579185466042983 := by
  unfold tailWord_792021
  simp only [CollatzResearch.WordTrace]
  refine ⟨28887379063650658262799917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19258252709100438841866611 28887379063650658262799917)
  ·
    refine ⟨10832767148868996848549969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28887379063650658262799917 10832767148868996848549969)
    ·
      refine ⟨8124575361651747636412477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10832767148868996848549969 8124575361651747636412477)
      ·
        refine ⟨3046715760619405363654679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8124575361651747636412477 3046715760619405363654679)
        ·
          refine ⟨4570073640929108045482019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3046715760619405363654679 4570073640929108045482019)
          ·
            refine ⟨6855110461393662068223029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4570073640929108045482019 6855110461393662068223029)
            ·
              refine ⟨642666605755655818895909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6855110461393662068223029 642666605755655818895909)
              ·
                refine ⟨120499988579185466042983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 642666605755655818895909 120499988579185466042983)
                ·
                  rfl

theorem cell20_792021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 4].length) (baseStart_792021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792021 prefixEnd_792021 := by exact prefixLift 792021
  have htrace : WordTrace (prefixWord ++ tailWord_792021) baseStart_792021 baseEnd_792021 := by
    simpa [prefixWord, tailWord_792021, baseEnd_792021] using wordTrace_append hprefix tailTrace_792021
  have hstable : (prefixWord ++ tailWord_792021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792021).length < 2 ^ (prefixWord ++ tailWord_792021).sum := by decide
  have hdescent : baseEnd_792021 < baseStart_792021 := by decide
  rcases family_descends (prefixWord ++ tailWord_792021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792045 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 5]
def baseStart_792045 : Nat := 118140960795 + 792045 * 2 ^ 59
def prefixEnd_792045 : Nat := 4983230072969 + 3 ^ 40 * 792045 * 2
def baseEnd_792045 : Nat := 361510919991518981328851

theorem tailTrace_792045 : CollatzResearch.WordTrace tailWord_792045 prefixEnd_792045 361510919991518981328851 := by
  unfold tailWord_792045
  simp only [CollatzResearch.WordTrace]
  refine ⟨28888254415563710361673589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19258836277042473574449059 28888254415563710361673589)
  ·
    refine ⟨2708273851459097846406899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28888254415563710361673589 2708273851459097846406899)
    ·
      refine ⟨4062410777188646769610349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2708273851459097846406899 4062410777188646769610349)
      ·
        refine ⟨1523404041445742538603881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4062410777188646769610349 1523404041445742538603881)
        ·
          refine ⟨1142553031084306903952911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1523404041445742538603881 1142553031084306903952911)
          ·
            refine ⟨1713829546626460355929367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142553031084306903952911 1713829546626460355929367)
            ·
              refine ⟨2570744319939690533894051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1713829546626460355929367 2570744319939690533894051)
              ·
                refine ⟨3856116479909535800841077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2570744319939690533894051 3856116479909535800841077)
                ·
                  refine ⟨361510919991518981328851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3856116479909535800841077 361510919991518981328851)
                  ·
                    rfl

theorem cell20_792045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_792045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792045 prefixEnd_792045 := by exact prefixLift 792045
  have htrace : WordTrace (prefixWord ++ tailWord_792045) baseStart_792045 baseEnd_792045 := by
    simpa [prefixWord, tailWord_792045, baseEnd_792045] using wordTrace_append hprefix tailTrace_792045
  have hstable : (prefixWord ++ tailWord_792045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792045).length < 2 ^ (prefixWord ++ tailWord_792045).sum := by decide
  have hdescent : baseEnd_792045 < baseStart_792045 := by decide
  rcases family_descends (prefixWord ++ tailWord_792045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792076 : List Nat := [2, 2, 1, 2, 5, 2, 2, 4]
def baseStart_792076 : Nat := 118140960795 + 792076 * 2 ^ 59
def prefixEnd_792076 : Nat := 4983230072969 + 3 ^ 40 * 792076 * 2
def baseEnd_792076 : Nat := 120508356412073550431797

theorem tailTrace_792076 : CollatzResearch.WordTrace tailWord_792076 prefixEnd_792076 120508356412073550431797 := by
  unfold tailWord_792076
  simp only [CollatzResearch.WordTrace]
  refine ⟨14444692539225701328026041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19259590052300935104034721 14444692539225701328026041)
  ·
    refine ⟨10833519404419275996019531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14444692539225701328026041 10833519404419275996019531)
    ·
      refine ⟨16250279106628913994029297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10833519404419275996019531 16250279106628913994029297)
      ·
        refine ⟨12187709329971685495521973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16250279106628913994029297 12187709329971685495521973)
        ·
          refine ⟨1142597749684845515205185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12187709329971685495521973 1142597749684845515205185)
          ·
            refine ⟨856948312263634136403889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1142597749684845515205185 856948312263634136403889)
            ·
              refine ⟨642711234197725602302917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 856948312263634136403889 642711234197725602302917)
              ·
                refine ⟨120508356412073550431797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 642711234197725602302917 120508356412073550431797)
                ·
                  rfl

theorem cell20_792076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_792076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792076 prefixEnd_792076 := by exact prefixLift 792076
  have htrace : WordTrace (prefixWord ++ tailWord_792076) baseStart_792076 baseEnd_792076 := by
    simpa [prefixWord, tailWord_792076, baseEnd_792076] using wordTrace_append hprefix tailTrace_792076
  have hstable : (prefixWord ++ tailWord_792076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792076).length < 2 ^ (prefixWord ++ tailWord_792076).sum := by decide
  have hdescent : baseEnd_792076 < baseStart_792076 := by decide
  rcases family_descends (prefixWord ++ tailWord_792076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792121 : List Nat := [1, 2, 1, 5, 1, 2, 4, 1, 3]
def baseStart_792121 : Nat := 118140960795 + 792121 * 2 ^ 59
def prefixEnd_792121 : Nat := 4983230072969 + 3 ^ 40 * 792121 * 2
def baseEnd_792121 : Nat := 361545608462400494795207

theorem tailTrace_792121 : CollatzResearch.WordTrace tailWord_792121 prefixEnd_792121 361545608462400494795207 := by
  unfold tailWord_792121
  simp only [CollatzResearch.WordTrace]
  refine ⟨28891026363288375341440217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19260684242192250227626811 28891026363288375341440217)
  ·
    refine ⟨21668269772466281506080163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28891026363288375341440217 21668269772466281506080163)
    ·
      refine ⟨32502404658699422259120245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21668269772466281506080163 32502404658699422259120245)
      ·
        refine ⟨3047100436753070836792523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32502404658699422259120245 3047100436753070836792523)
        ·
          refine ⟨4570650655129606255188785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3047100436753070836792523 4570650655129606255188785)
          ·
            refine ⟨3427987991347204691391589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4570650655129606255188785 3427987991347204691391589)
            ·
              refine ⟨642747748377600879635923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3427987991347204691391589 642747748377600879635923)
              ·
                refine ⟨964121622566401319453885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642747748377600879635923 964121622566401319453885)
                ·
                  refine ⟨361545608462400494795207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 964121622566401319453885 361545608462400494795207)
                  ·
                    rfl

theorem cell20_792121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 4, 1, 3].length) (baseStart_792121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792121 prefixEnd_792121 := by exact prefixLift 792121
  have htrace : WordTrace (prefixWord ++ tailWord_792121) baseStart_792121 baseEnd_792121 := by
    simpa [prefixWord, tailWord_792121, baseEnd_792121] using wordTrace_append hprefix tailTrace_792121
  have hstable : (prefixWord ++ tailWord_792121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792121).length < 2 ^ (prefixWord ++ tailWord_792121).sum := by decide
  have hdescent : baseEnd_792121 < baseStart_792121 := by decide
  rcases family_descends (prefixWord ++ tailWord_792121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792156 : List Nat := [2, 2, 4, 1, 2, 9]
def baseStart_792156 : Nat := 118140960795 + 792156 * 2 ^ 59
def prefixEnd_792156 : Nat := 4983230072969 + 3 ^ 40 * 792156 * 2
def baseEnd_792156 : Nat := 13391169756151701060311

theorem tailTrace_792156 : CollatzResearch.WordTrace tailWord_792156 prefixEnd_792156 13391169756151701060311 := by
  unfold tailWord_792156
  simp only [CollatzResearch.WordTrace]
  refine ⟨14446151459080788159482161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19261535278774384212642881 14446151459080788159482161)
  ·
    refine ⟨10834613594310591119611621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14446151459080788159482161 10834613594310591119611621)
    ·
      refine ⟨2031490048933235834927179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10834613594310591119611621 2031490048933235834927179)
      ·
        refine ⟨3047235073399853752390769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2031490048933235834927179 3047235073399853752390769)
        ·
          refine ⟨2285426305049890314293077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3047235073399853752390769 2285426305049890314293077)
          ·
            refine ⟨13391169756151701060311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2285426305049890314293077 13391169756151701060311)
            ·
              rfl

theorem cell20_792156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 9].length) (baseStart_792156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792156 prefixEnd_792156 := by exact prefixLift 792156
  have htrace : WordTrace (prefixWord ++ tailWord_792156) baseStart_792156 baseEnd_792156 := by
    simpa [prefixWord, tailWord_792156, baseEnd_792156] using wordTrace_append hprefix tailTrace_792156
  have hstable : (prefixWord ++ tailWord_792156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792156).length < 2 ^ (prefixWord ++ tailWord_792156).sum := by decide
  have hdescent : baseEnd_792156 < baseStart_792156 := by decide
  rcases family_descends (prefixWord ++ tailWord_792156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792200 : List Nat := [2, 1, 3, 5, 1, 1, 2, 3, 2]
def baseStart_792200 : Nat := 118140960795 + 792200 * 2 ^ 59
def prefixEnd_792200 : Nat := 4983230072969 + 3 ^ 40 * 792200 * 2
def baseEnd_792200 : Nat := 361581666215027331161551

theorem tailTrace_792200 : CollatzResearch.WordTrace tailWord_792200 prefixEnd_792200 361581666215027331161551 := by
  unfold tailWord_792200
  simp only [CollatzResearch.WordTrace]
  refine ⟨14446953865001085916783027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19262605153334781222377369 14446953865001085916783027)
  ·
    refine ⟨21670430797501628875174541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14446953865001085916783027 21670430797501628875174541)
    ·
      refine ⟨8126411549063110828190453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21670430797501628875174541 8126411549063110828190453)
      ·
        refine ⟨761851082724666640142855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8126411549063110828190453 761851082724666640142855)
        ·
          refine ⟨1142776624086999960214283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 761851082724666640142855 1142776624086999960214283)
          ·
            refine ⟨1714164936130499940321425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142776624086999960214283 1714164936130499940321425)
            ·
              refine ⟨1285623702097874955241069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1714164936130499940321425 1285623702097874955241069)
              ·
                refine ⟨482108888286703108215401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1285623702097874955241069 482108888286703108215401)
                ·
                  refine ⟨361581666215027331161551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482108888286703108215401 361581666215027331161551)
                  ·
                    rfl

theorem cell20_792200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 3, 2].length) (baseStart_792200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792200 prefixEnd_792200 := by exact prefixLift 792200
  have htrace : WordTrace (prefixWord ++ tailWord_792200) baseStart_792200 baseEnd_792200 := by
    simpa [prefixWord, tailWord_792200, baseEnd_792200] using wordTrace_append hprefix tailTrace_792200
  have hstable : (prefixWord ++ tailWord_792200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792200).length < 2 ^ (prefixWord ++ tailWord_792200).sum := by decide
  have hdescent : baseEnd_792200 < baseStart_792200 := by decide
  rcases family_descends (prefixWord ++ tailWord_792200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792204 : List Nat := [2, 2, 1, 2, 1, 1, 6, 3, 2]
def baseStart_792204 : Nat := 118140960795 + 792204 * 2 ^ 59
def prefixEnd_792204 : Nat := 4983230072969 + 3 ^ 40 * 792204 * 2
def baseEnd_792204 : Nat := 361583491924021095028201

theorem tailTrace_792204 : CollatzResearch.WordTrace tailWord_792204 prefixEnd_792204 361583491924021095028201 := by
  unfold tailWord_792204
  simp only [CollatzResearch.WordTrace]
  refine ⟨14447026810993840258355833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19262702414658453677807777 14447026810993840258355833)
  ·
    refine ⟨10835270108245380193766875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14447026810993840258355833 10835270108245380193766875)
    ·
      refine ⟨16252905162368070290650313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10835270108245380193766875 16252905162368070290650313)
      ·
        refine ⟨12189678871776052717987735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16252905162368070290650313 12189678871776052717987735)
        ·
          refine ⟨18284518307664079076981603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12189678871776052717987735 18284518307664079076981603)
          ·
            refine ⟨27426777461496118615472405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18284518307664079076981603 27426777461496118615472405)
            ·
              refine ⟨1285630193507630560100269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27426777461496118615472405 1285630193507630560100269)
              ·
                refine ⟨482111322565361460037601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1285630193507630560100269 482111322565361460037601)
                ·
                  refine ⟨361583491924021095028201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482111322565361460037601 361583491924021095028201)
                  ·
                    rfl

theorem cell20_792204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_792204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792204 prefixEnd_792204 := by exact prefixLift 792204
  have htrace : WordTrace (prefixWord ++ tailWord_792204) baseStart_792204 baseEnd_792204 := by
    simpa [prefixWord, tailWord_792204, baseEnd_792204] using wordTrace_append hprefix tailTrace_792204
  have hstable : (prefixWord ++ tailWord_792204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792204).length < 2 ^ (prefixWord ++ tailWord_792204).sum := by decide
  have hdescent : baseEnd_792204 < baseStart_792204 := by decide
  rcases family_descends (prefixWord ++ tailWord_792204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792225 : List Nat := [1, 2, 3, 3, 2, 1, 1, 3, 4]
def baseStart_792225 : Nat := 118140960795 + 792225 * 2 ^ 59
def prefixEnd_792225 : Nat := 4983230072969 + 3 ^ 40 * 792225 * 2
def baseEnd_792225 : Nat := 361593076896238355328115

theorem tailTrace_792225 : CollatzResearch.WordTrace tailWord_792225 prefixEnd_792225 361593076896238355328115 := by
  unfold tailWord_792225
  simp only [CollatzResearch.WordTrace]
  refine ⟨28894819554911601103226129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19263213036607734068817419 28894819554911601103226129)
  ·
    refine ⟨21671114666183700827419597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28894819554911601103226129 21671114666183700827419597)
    ·
      refine ⟨8126667999818887810282349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21671114666183700827419597 8126667999818887810282349)
      ·
        refine ⟨3047500499932082928855881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8126667999818887810282349 3047500499932082928855881)
        ·
          refine ⟨2285625374949062196641911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3047500499932082928855881 2285625374949062196641911)
          ·
            refine ⟨3428438062423593294962867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2285625374949062196641911 3428438062423593294962867)
            ·
              refine ⟨5142657093635389942444301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3428438062423593294962867 5142657093635389942444301)
              ·
                refine ⟨1928496410113271228416613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5142657093635389942444301 1928496410113271228416613)
                ·
                  refine ⟨361593076896238355328115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1928496410113271228416613 361593076896238355328115)
                  ·
                    rfl

theorem cell20_792225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_792225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792225 prefixEnd_792225 := by exact prefixLift 792225
  have htrace : WordTrace (prefixWord ++ tailWord_792225) baseStart_792225 baseEnd_792225 := by
    simpa [prefixWord, tailWord_792225, baseEnd_792225] using wordTrace_append hprefix tailTrace_792225
  have hstable : (prefixWord ++ tailWord_792225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792225).length < 2 ^ (prefixWord ++ tailWord_792225).sum := by decide
  have hdescent : baseEnd_792225 < baseStart_792225 := by decide
  rcases family_descends (prefixWord ++ tailWord_792225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792245 : List Nat := [1, 3, 3, 3, 3, 1, 2, 4]
def baseStart_792245 : Nat := 118140960795 + 792245 * 2 ^ 59
def prefixEnd_792245 : Nat := 4983230072969 + 3 ^ 40 * 792245 * 2
def baseEnd_792245 : Nat := 120534068480402391553789

theorem tailTrace_792245 : CollatzResearch.WordTrace tailWord_792245 prefixEnd_792245 120534068480402391553789 := by
  unfold tailWord_792245
  simp only [CollatzResearch.WordTrace]
  refine ⟨28895549014839144518954189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19263699343226096345969459 28895549014839144518954189)
  ·
    refine ⟨10835830880564679194607821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28895549014839144518954189 10835830880564679194607821)
    ·
      refine ⟨4063436580211754697977933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10835830880564679194607821 4063436580211754697977933)
      ·
        refine ⟨1523788717579408011741725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4063436580211754697977933 1523788717579408011741725)
        ·
          refine ⟨571420769092278004403147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1523788717579408011741725 571420769092278004403147)
          ·
            refine ⟨857131153638417006604721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571420769092278004403147 857131153638417006604721)
            ·
              refine ⟨642848365228812754953541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 857131153638417006604721 642848365228812754953541)
              ·
                refine ⟨120534068480402391553789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 642848365228812754953541 120534068480402391553789)
                ·
                  rfl

theorem cell20_792245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 2, 4].length) (baseStart_792245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792245 prefixEnd_792245 := by exact prefixLift 792245
  have htrace : WordTrace (prefixWord ++ tailWord_792245) baseStart_792245 baseEnd_792245 := by
    simpa [prefixWord, tailWord_792245, baseEnd_792245] using wordTrace_append hprefix tailTrace_792245
  have hstable : (prefixWord ++ tailWord_792245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792245).length < 2 ^ (prefixWord ++ tailWord_792245).sum := by decide
  have hdescent : baseEnd_792245 < baseStart_792245 := by decide
  rcases family_descends (prefixWord ++ tailWord_792245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792276 : List Nat := [2, 4, 1, 3, 1, 2, 3, 2, 2]
def baseStart_792276 : Nat := 118140960795 + 792276 * 2 ^ 59
def prefixEnd_792276 : Nat := 4983230072969 + 3 ^ 40 * 792276 * 2
def baseEnd_792276 : Nat := 361616354685908844627907

theorem tailTrace_792276 : CollatzResearch.WordTrace tailWord_792276 prefixEnd_792276 361616354685908844627907 := by
  unfold tailWord_792276
  simp only [CollatzResearch.WordTrace]
  refine ⟨14448339838863418406666341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19264453118484557875555121 14448339838863418406666341)
  ·
    refine ⟨2709063719786890951249939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14448339838863418406666341 2709063719786890951249939)
    ·
      refine ⟨4063595579680336426874909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2709063719786890951249939 4063595579680336426874909)
      ·
        refine ⟨1523848342380126160078091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4063595579680336426874909 1523848342380126160078091)
        ·
          refine ⟨2285772513570189240117137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1523848342380126160078091 2285772513570189240117137)
          ·
            refine ⟨1714329385177641930087853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2285772513570189240117137 1714329385177641930087853)
            ·
              refine ⟨642873519441615723782945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1714329385177641930087853 642873519441615723782945)
              ·
                refine ⟨482155139581211792837209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 642873519441615723782945 482155139581211792837209)
                ·
                  refine ⟨361616354685908844627907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482155139581211792837209 361616354685908844627907)
                  ·
                    rfl

theorem cell20_792276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_792276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792276 prefixEnd_792276 := by exact prefixLift 792276
  have htrace : WordTrace (prefixWord ++ tailWord_792276) baseStart_792276 baseEnd_792276 := by
    simpa [prefixWord, tailWord_792276, baseEnd_792276] using wordTrace_append hprefix tailTrace_792276
  have hstable : (prefixWord ++ tailWord_792276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792276).length < 2 ^ (prefixWord ++ tailWord_792276).sum := by decide
  have hdescent : baseEnd_792276 < baseStart_792276 := by decide
  rcases family_descends (prefixWord ++ tailWord_792276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792346 : List Nat := [3, 1, 1, 3, 2, 2, 3, 5]
def baseStart_792346 : Nat := 118140960795 + 792346 * 2 ^ 59
def prefixEnd_792346 : Nat := 4983230072969 + 3 ^ 40 * 792346 * 2
def baseEnd_792346 : Nat := 120549434864433237431429

theorem tailTrace_792346 : CollatzResearch.WordTrace tailWord_792346 prefixEnd_792346 120549434864433237431429 := by
  unfold tailWord_792346
  simp only [CollatzResearch.WordTrace]
  refine ⟨7224808196868309692095223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19266155191648825845587261 7224808196868309692095223)
  ·
    refine ⟨10837212295302464538142835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7224808196868309692095223 10837212295302464538142835)
    ·
      refine ⟨16255818442953696807214253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10837212295302464538142835 16255818442953696807214253)
      ·
        refine ⟨6095931916107636302705345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16255818442953696807214253 6095931916107636302705345)
        ·
          refine ⟨4571948937080727227029009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6095931916107636302705345 4571948937080727227029009)
          ·
            refine ⟨3428961702810545420271757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4571948937080727227029009 3428961702810545420271757)
            ·
              refine ⟨1285860638553954532601909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3428961702810545420271757 1285860638553954532601909)
              ·
                refine ⟨120549434864433237431429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1285860638553954532601909 120549434864433237431429)
                ·
                  rfl

theorem cell20_792346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_792346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792346 prefixEnd_792346 := by exact prefixLift 792346
  have htrace : WordTrace (prefixWord ++ tailWord_792346) baseStart_792346 baseEnd_792346 := by
    simpa [prefixWord, tailWord_792346, baseEnd_792346] using wordTrace_append hprefix tailTrace_792346
  have hstable : (prefixWord ++ tailWord_792346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792346).length < 2 ^ (prefixWord ++ tailWord_792346).sum := by decide
  have hdescent : baseEnd_792346 < baseStart_792346 := by decide
  rcases family_descends (prefixWord ++ tailWord_792346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792373 : List Nat := [1, 3, 3, 1, 4, 1, 2, 3, 2]
def baseStart_792373 : Nat := 118140960795 + 792373 * 2 ^ 59
def prefixEnd_792373 : Nat := 4983230072969 + 3 ^ 40 * 792373 * 2
def baseEnd_792373 : Nat := 361660628129007618394177

theorem tailTrace_792373 : CollatzResearch.WordTrace tailWord_792373 prefixEnd_792373 361660628129007618394177 := by
  unfold tailWord_792373
  simp only [CollatzResearch.WordTrace]
  refine ⟨28900217558375422379613773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19266811705583614919742515 28900217558375422379613773)
  ·
    refine ⟨10837581584390783392355165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28900217558375422379613773 10837581584390783392355165)
    ·
      refine ⟨4064093094146543772133187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10837581584390783392355165 4064093094146543772133187)
      ·
        refine ⟨6096139641219815658199781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4064093094146543772133187 6096139641219815658199781)
        ·
          refine ⟨1143026182728715435912459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6096139641219815658199781 1143026182728715435912459)
          ·
            refine ⟨1714539274093073153868689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1143026182728715435912459 1714539274093073153868689)
            ·
              refine ⟨1285904455569804865401517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1714539274093073153868689 1285904455569804865401517)
              ·
                refine ⟨482214170838676824525569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1285904455569804865401517 482214170838676824525569)
                ·
                  refine ⟨361660628129007618394177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482214170838676824525569 361660628129007618394177)
                  ·
                    rfl

theorem cell20_792373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 3, 2].length) (baseStart_792373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792373 prefixEnd_792373 := by exact prefixLift 792373
  have htrace : WordTrace (prefixWord ++ tailWord_792373) baseStart_792373 baseEnd_792373 := by
    simpa [prefixWord, tailWord_792373, baseEnd_792373] using wordTrace_append hprefix tailTrace_792373
  have hstable : (prefixWord ++ tailWord_792373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792373).length < 2 ^ (prefixWord ++ tailWord_792373).sum := by decide
  have hdescent : baseEnd_792373 < baseStart_792373 := by decide
  rcases family_descends (prefixWord ++ tailWord_792373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792390 : List Nat := [6, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_792390 : Nat := 118140960795 + 792390 * 2 ^ 59
def prefixEnd_792390 : Nat := 4983230072969 + 3 ^ 40 * 792390 * 2
def baseEnd_792390 : Nat := 361668387392231114827441

theorem tailTrace_792390 : CollatzResearch.WordTrace tailWord_792390 prefixEnd_792390 361668387392231114827441 := by
  unfold tailWord_792390
  simp only [CollatzResearch.WordTrace]
  refine ⟨903151174978557321343207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19267225066209222855321749 903151174978557321343207)
  ·
    refine ⟨1354726762467835982014811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 903151174978557321343207 1354726762467835982014811)
    ·
      refine ⟨2032090143701753973022217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1354726762467835982014811 2032090143701753973022217)
      ·
        refine ⟨1524067607776315479766663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2032090143701753973022217 1524067607776315479766663)
        ·
          refine ⟨2286101411664473219649995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524067607776315479766663 2286101411664473219649995)
          ·
            refine ⟨3429152117496709829474993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2286101411664473219649995 3429152117496709829474993)
            ·
              refine ⟨2571864088122532372106245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3429152117496709829474993 2571864088122532372106245)
              ·
                refine ⟨482224516522974819769921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2571864088122532372106245 482224516522974819769921)
                ·
                  refine ⟨361668387392231114827441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482224516522974819769921 361668387392231114827441)
                  ·
                    rfl

theorem cell20_792390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_792390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792390 prefixEnd_792390 := by exact prefixLift 792390
  have htrace : WordTrace (prefixWord ++ tailWord_792390) baseStart_792390 baseEnd_792390 := by
    simpa [prefixWord, tailWord_792390, baseEnd_792390] using wordTrace_append hprefix tailTrace_792390
  have hstable : (prefixWord ++ tailWord_792390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792390).length < 2 ^ (prefixWord ++ tailWord_792390).sum := by decide
  have hdescent : baseEnd_792390 < baseStart_792390 := by decide
  rcases family_descends (prefixWord ++ tailWord_792390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792418 : List Nat := [3, 3, 2, 1, 2, 3, 2, 4]
def baseStart_792418 : Nat := 118140960795 + 792418 * 2 ^ 59
def prefixEnd_792418 : Nat := 4983230072969 + 3 ^ 40 * 792418 * 2
def baseEnd_792418 : Nat := 120560389118395820631331

theorem tailTrace_792418 : CollatzResearch.WordTrace tailWord_792418 prefixEnd_792418 120560389118395820631331 := by
  unfold tailWord_792418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7225464710803098766250477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19267905895474930043334605 7225464710803098766250477)
  ·
    refine ⟨2709549266551162037343929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7225464710803098766250477 2709549266551162037343929)
    ·
      refine ⟨2032161949913371528007947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2709549266551162037343929 2032161949913371528007947)
      ·
        refine ⟨3048242924870057292011921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2032161949913371528007947 3048242924870057292011921)
        ·
          refine ⟨2286182193652542969008941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3048242924870057292011921 2286182193652542969008941)
          ·
            refine ⟨857318322619703613378353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2286182193652542969008941 857318322619703613378353)
            ·
              refine ⟨642988741964777710033765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 857318322619703613378353 642988741964777710033765)
              ·
                refine ⟨120560389118395820631331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 642988741964777710033765 120560389118395820631331)
                ·
                  rfl

theorem cell20_792418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_792418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792418 prefixEnd_792418 := by exact prefixLift 792418
  have htrace : WordTrace (prefixWord ++ tailWord_792418) baseStart_792418 baseEnd_792418 := by
    simpa [prefixWord, tailWord_792418, baseEnd_792418] using wordTrace_append hprefix tailTrace_792418
  have hstable : (prefixWord ++ tailWord_792418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792418).length < 2 ^ (prefixWord ++ tailWord_792418).sum := by decide
  have hdescent : baseEnd_792418 < baseStart_792418 := by decide
  rcases family_descends (prefixWord ++ tailWord_792418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792429 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 5]
def baseStart_792429 : Nat := 118140960795 + 792429 * 2 ^ 59
def prefixEnd_792429 : Nat := 4983230072969 + 3 ^ 40 * 792429 * 2
def baseEnd_792429 : Nat := 361686188054920312527281

theorem tailTrace_792429 : CollatzResearch.WordTrace tailWord_792429 prefixEnd_792429 361686188054920312527281 := by
  unfold tailWord_792429
  simp only [CollatzResearch.WordTrace]
  refine ⟨28902260046172543943652341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19268173364115029295768227 28902260046172543943652341)
  ·
    refine ⟨2709586879328675994717407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28902260046172543943652341 2709586879328675994717407)
    ·
      refine ⟨4064380318993013992076111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2709586879328675994717407 4064380318993013992076111)
      ·
        refine ⟨6096570478489520988114167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4064380318993013992076111 6096570478489520988114167)
        ·
          refine ⟨9144855717734281482171251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6096570478489520988114167 9144855717734281482171251)
          ·
            refine ⟨13717283576601422223256877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9144855717734281482171251 13717283576601422223256877)
            ·
              refine ⟨5143981341225533333721329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13717283576601422223256877 5143981341225533333721329)
              ·
                refine ⟨3857986005919150000290997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5143981341225533333721329 3857986005919150000290997)
                ·
                  refine ⟨361686188054920312527281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3857986005919150000290997 361686188054920312527281)
                  ·
                    rfl

theorem cell20_792429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_792429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792429 prefixEnd_792429 := by exact prefixLift 792429
  have htrace : WordTrace (prefixWord ++ tailWord_792429) baseStart_792429 baseEnd_792429 := by
    simpa [prefixWord, tailWord_792429, baseEnd_792429] using wordTrace_append hprefix tailTrace_792429
  have hstable : (prefixWord ++ tailWord_792429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792429).length < 2 ^ (prefixWord ++ tailWord_792429).sum := by decide
  have hdescent : baseEnd_792429 < baseStart_792429 := by decide
  rcases family_descends (prefixWord ++ tailWord_792429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792449 : List Nat := [1, 2, 4, 4, 1, 2, 1, 1, 4]
def baseStart_792449 : Nat := 118140960795 + 792449 * 2 ^ 59
def prefixEnd_792449 : Nat := 4983230072969 + 3 ^ 40 * 792449 * 2
def baseEnd_792449 : Nat := 361695316599889131860533

theorem tailTrace_792449 : CollatzResearch.WordTrace tailWord_792449 prefixEnd_792449 361695316599889131860533 := by
  unfold tailWord_792449
  simp only [CollatzResearch.WordTrace]
  refine ⟨28902989506100087359380401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19268659670733391572920267 28902989506100087359380401)
  ·
    refine ⟨21677242129575065519535301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28902989506100087359380401 21677242129575065519535301)
    ·
      refine ⟨4064482899295324784912869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21677242129575065519535301 4064482899295324784912869)
      ·
        refine ⟨762090543617873397171163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4064482899295324784912869 762090543617873397171163)
        ·
          refine ⟨1143135815426810095756745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762090543617873397171163 1143135815426810095756745)
          ·
            refine ⟨857351861570107571817559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1143135815426810095756745 857351861570107571817559)
            ·
              refine ⟨1286027792355161357726339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857351861570107571817559 1286027792355161357726339)
              ·
                refine ⟨1929041688532742036589509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1286027792355161357726339 1929041688532742036589509)
                ·
                  refine ⟨361695316599889131860533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1929041688532742036589509 361695316599889131860533)
                  ·
                    rfl

theorem cell20_792449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 4].length) (baseStart_792449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792449 prefixEnd_792449 := by exact prefixLift 792449
  have htrace : WordTrace (prefixWord ++ tailWord_792449) baseStart_792449 baseEnd_792449 := by
    simpa [prefixWord, tailWord_792449, baseEnd_792449] using wordTrace_append hprefix tailTrace_792449
  have hstable : (prefixWord ++ tailWord_792449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792449).length < 2 ^ (prefixWord ++ tailWord_792449).sum := by decide
  have hdescent : baseEnd_792449 < baseStart_792449 := by decide
  rcases family_descends (prefixWord ++ tailWord_792449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792494 : List Nat := [4, 1, 5, 1, 1, 8]
def baseStart_792494 : Nat := 118140960795 + 792494 * 2 ^ 59
def prefixEnd_792494 : Nat := 4983230072969 + 3 ^ 40 * 792494 * 2
def baseEnd_792494 : Nat := 13396883549113665754087

theorem tailTrace_792494 : CollatzResearch.WordTrace tailWord_792494 prefixEnd_792494 13396883549113665754087 := by
  unfold tailWord_792494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3613078848867132505596067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19269753860624706696512357 3613078848867132505596067)
  ·
    refine ⟨5419618273300698758394101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3613078848867132505596067 5419618273300698758394101)
    ·
      refine ⟨508089213121940508599447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5419618273300698758394101 508089213121940508599447)
      ·
        refine ⟨762133819682910762899171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508089213121940508599447 762133819682910762899171)
        ·
          refine ⟨1143200729524366144348757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762133819682910762899171 1143200729524366144348757)
          ·
            refine ⟨13396883549113665754087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1143200729524366144348757 13396883549113665754087)
            ·
              rfl

theorem cell20_792494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 8].length) (baseStart_792494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792494 prefixEnd_792494 := by exact prefixLift 792494
  have htrace : WordTrace (prefixWord ++ tailWord_792494) baseStart_792494 baseEnd_792494 := by
    simpa [prefixWord, tailWord_792494, baseEnd_792494] using wordTrace_append hprefix tailTrace_792494
  have hstable : (prefixWord ++ tailWord_792494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792494).length < 2 ^ (prefixWord ++ tailWord_792494).sum := by decide
  have hdescent : baseEnd_792494 < baseStart_792494 := by decide
  rcases family_descends (prefixWord ++ tailWord_792494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792500 : List Nat := [2, 5, 2, 1, 3, 1, 2, 2, 2]
def baseStart_792500 : Nat := 118140960795 + 792500 * 2 ^ 59
def prefixEnd_792500 : Nat := 4983230072969 + 3 ^ 40 * 792500 * 2
def baseEnd_792500 : Nat := 361718594389559621160325

theorem tailTrace_792500 : CollatzResearch.WordTrace tailWord_792500 prefixEnd_792500 361718594389559621160325 := by
  unfold tailWord_792500
  simp only [CollatzResearch.WordTrace]
  refine ⟨14452424814457661534743477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19269899752610215379657969 14452424814457661534743477)
  ·
    refine ⟨1354914826355405768882201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14452424814457661534743477 1354914826355405768882201)
    ·
      refine ⟨1016186119766554326661651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1354914826355405768882201 1016186119766554326661651)
      ·
        refine ⟨1524279179649831489992477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016186119766554326661651 1524279179649831489992477)
        ·
          refine ⟨571604692368686808747179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1524279179649831489992477 571604692368686808747179)
          ·
            refine ⟨857407038553030213120769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571604692368686808747179 857407038553030213120769)
            ·
              refine ⟨643055278914772659840577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 857407038553030213120769 643055278914772659840577)
              ·
                refine ⟨482291459186079494880433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 643055278914772659840577 482291459186079494880433)
                ·
                  refine ⟨361718594389559621160325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482291459186079494880433 361718594389559621160325)
                  ·
                    rfl

theorem cell20_792500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_792500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792500 prefixEnd_792500 := by exact prefixLift 792500
  have htrace : WordTrace (prefixWord ++ tailWord_792500) baseStart_792500 baseEnd_792500 := by
    simpa [prefixWord, tailWord_792500, baseEnd_792500] using wordTrace_append hprefix tailTrace_792500
  have hstable : (prefixWord ++ tailWord_792500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792500).length < 2 ^ (prefixWord ++ tailWord_792500).sum := by decide
  have hdescent : baseEnd_792500 < baseStart_792500 := by decide
  rcases family_descends (prefixWord ++ tailWord_792500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792512 : List Nat := [2, 1, 1, 2, 3, 2, 2, 3, 4]
def baseStart_792512 : Nat := 118140960795 + 792512 * 2 ^ 59
def prefixEnd_792512 : Nat := 4983230072969 + 3 ^ 40 * 792512 * 2
def baseEnd_792512 : Nat := 361724071516540912760275

theorem tailTrace_792512 : CollatzResearch.WordTrace tailWord_792512 prefixEnd_792512 361724071516540912760275 := by
  unfold tailWord_792512
  simp only [CollatzResearch.WordTrace]
  refine ⟨14452643652435924559461895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19270191536581232745949193 14452643652435924559461895)
  ·
    refine ⟨21678965478653886839192843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14452643652435924559461895 21678965478653886839192843)
    ·
      refine ⟨32518448217980830258789265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21678965478653886839192843 32518448217980830258789265)
      ·
        refine ⟨24388836163485622694091949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32518448217980830258789265 24388836163485622694091949)
        ·
          refine ⟨9145813561307108510284481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24388836163485622694091949 9145813561307108510284481)
          ·
            refine ⟨6859360170980331382713361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9145813561307108510284481 6859360170980331382713361)
            ·
              refine ⟨5144520128235248537035021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6859360170980331382713361 5144520128235248537035021)
              ·
                refine ⟨1929195048088218201388133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5144520128235248537035021 1929195048088218201388133)
                ·
                  refine ⟨361724071516540912760275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1929195048088218201388133 361724071516540912760275)
                  ·
                    rfl

theorem cell20_792512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_792512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792512 prefixEnd_792512 := by exact prefixLift 792512
  have htrace : WordTrace (prefixWord ++ tailWord_792512) baseStart_792512 baseEnd_792512 := by
    simpa [prefixWord, tailWord_792512, baseEnd_792512] using wordTrace_append hprefix tailTrace_792512
  have hstable : (prefixWord ++ tailWord_792512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792512).length < 2 ^ (prefixWord ++ tailWord_792512).sum := by decide
  have hdescent : baseEnd_792512 < baseStart_792512 := by decide
  rcases family_descends (prefixWord ++ tailWord_792512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792536 : List Nat := [2, 1, 2, 2, 2, 2, 5, 4]
def baseStart_792536 : Nat := 118140960795 + 792536 * 2 ^ 59
def prefixEnd_792536 : Nat := 4983230072969 + 3 ^ 40 * 792536 * 2
def baseEnd_792536 : Nat := 120578341923501165320059

theorem tailTrace_792536 : CollatzResearch.WordTrace tailWord_792536 prefixEnd_792536 120578341923501165320059 := by
  unfold tailWord_792536
  simp only [CollatzResearch.WordTrace]
  refine ⟨14453081328392450608898731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19270775104523267478531641 14453081328392450608898731)
  ·
    refine ⟨21679621992588675913348097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14453081328392450608898731 21679621992588675913348097)
    ·
      refine ⟨16259716494441506935011073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21679621992588675913348097 16259716494441506935011073)
      ·
        refine ⟨12194787370831130201258305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16259716494441506935011073 12194787370831130201258305)
        ·
          refine ⟨9146090528123347650943729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12194787370831130201258305 9146090528123347650943729)
          ·
            refine ⟨6859567896092510738207797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9146090528123347650943729 6859567896092510738207797)
            ·
              refine ⟨643084490258672881706981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6859567896092510738207797 643084490258672881706981)
              ·
                refine ⟨120578341923501165320059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 643084490258672881706981 120578341923501165320059)
                ·
                  rfl

theorem cell20_792536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_792536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792536 prefixEnd_792536 := by exact prefixLift 792536
  have htrace : WordTrace (prefixWord ++ tailWord_792536) baseStart_792536 baseEnd_792536 := by
    simpa [prefixWord, tailWord_792536, baseEnd_792536] using wordTrace_append hprefix tailTrace_792536
  have hstable : (prefixWord ++ tailWord_792536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792536).length < 2 ^ (prefixWord ++ tailWord_792536).sum := by decide
  have hdescent : baseEnd_792536 < baseStart_792536 := by decide
  rcases family_descends (prefixWord ++ tailWord_792536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792588 : List Nat := [2, 2, 1, 2, 3, 1, 1, 4, 4]
def baseStart_792588 : Nat := 118140960795 + 792588 * 2 ^ 59
def prefixEnd_792588 : Nat := 4983230072969 + 3 ^ 40 * 792588 * 2
def baseEnd_792588 : Nat := 361758759987422426226631

theorem tailTrace_792588 : CollatzResearch.WordTrace tailWord_792588 prefixEnd_792588 361758759987422426226631 := by
  unfold tailWord_792588
  simp only [CollatzResearch.WordTrace]
  refine ⟨14454029626298257049345209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19272039501731009399126945 14454029626298257049345209)
  ·
    refine ⟨10840522219723692787008907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14454029626298257049345209 10840522219723692787008907)
    ·
      refine ⟨16260783329585539180513361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10840522219723692787008907 16260783329585539180513361)
      ·
        refine ⟨12195587497189154385385021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16260783329585539180513361 12195587497189154385385021)
        ·
          refine ⟨4573345311445932894519383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12195587497189154385385021 4573345311445932894519383)
          ·
            refine ⟨6860017967168899341779075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4573345311445932894519383 6860017967168899341779075)
            ·
              refine ⟨10290026950753349012668613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6860017967168899341779075 10290026950753349012668613)
              ·
                refine ⟨1929380053266252939875365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10290026950753349012668613 1929380053266252939875365)
                ·
                  refine ⟨361758759987422426226631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1929380053266252939875365 361758759987422426226631)
                  ·
                    rfl

theorem cell20_792588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_792588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792588 prefixEnd_792588 := by exact prefixLift 792588
  have htrace : WordTrace (prefixWord ++ tailWord_792588) baseStart_792588 baseEnd_792588 := by
    simpa [prefixWord, tailWord_792588, baseEnd_792588] using wordTrace_append hprefix tailTrace_792588
  have hstable : (prefixWord ++ tailWord_792588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792588).length < 2 ^ (prefixWord ++ tailWord_792588).sum := by decide
  have hdescent : baseEnd_792588 < baseStart_792588 := by decide
  rcases family_descends (prefixWord ++ tailWord_792588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792622 : List Nat := [4, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_792622 : Nat := 118140960795 + 792622 * 2 ^ 59
def prefixEnd_792622 : Nat := 4983230072969 + 3 ^ 40 * 792622 * 2
def baseEnd_792622 : Nat := 361774278513869419093159

theorem tailTrace_792622 : CollatzResearch.WordTrace tailWord_792622 prefixEnd_792622 361774278513869419093159 := by
  unfold tailWord_792622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3613662416809167238178515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19272866222982225270285413 3613662416809167238178515)
  ·
    refine ⟨5420493625213750857267773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3613662416809167238178515 5420493625213750857267773)
    ·
      refine ⟨2032685109455156571475415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5420493625213750857267773 2032685109455156571475415)
      ·
        refine ⟨3049027664182734857213123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2032685109455156571475415 3049027664182734857213123)
        ·
          refine ⟨4573541496274102285819685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3049027664182734857213123 4573541496274102285819685)
          ·
            refine ⟨857539030551394178591191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4573541496274102285819685 857539030551394178591191)
            ·
              refine ⟨1286308545827091267886787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857539030551394178591191 1286308545827091267886787)
              ·
                refine ⟨1929462818740636901830181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1286308545827091267886787 1929462818740636901830181)
                ·
                  refine ⟨361774278513869419093159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1929462818740636901830181 361774278513869419093159)
                  ·
                    rfl

theorem cell20_792622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_792622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792622 prefixEnd_792622 := by exact prefixLift 792622
  have htrace : WordTrace (prefixWord ++ tailWord_792622) baseStart_792622 baseEnd_792622 := by
    simpa [prefixWord, tailWord_792622, baseEnd_792622] using wordTrace_append hprefix tailTrace_792622
  have hstable : (prefixWord ++ tailWord_792622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792622).length < 2 ^ (prefixWord ++ tailWord_792622).sum := by decide
  have hdescent : baseEnd_792622 < baseStart_792622 := by decide
  rcases family_descends (prefixWord ++ tailWord_792622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792632 : List Nat := [2, 1, 2, 1, 7, 1, 2, 1, 3]
def baseStart_792632 : Nat := 118140960795 + 792632 * 2 ^ 59
def prefixEnd_792632 : Nat := 4983230072969 + 3 ^ 40 * 792632 * 2
def baseEnd_792632 : Nat := 361778842786353828759785

theorem tailTrace_792632 : CollatzResearch.WordTrace tailWord_792632 prefixEnd_792632 361778842786353828759785 := by
  unfold tailWord_792632
  simp only [CollatzResearch.WordTrace]
  refine ⟨14454832032218554806646075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19273109376291406408861433 14454832032218554806646075)
  ·
    refine ⟨21682248048327832209969113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14454832032218554806646075 21682248048327832209969113)
    ·
      refine ⟨16261686036245874157476835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21682248048327832209969113 16261686036245874157476835)
      ·
        refine ⟨24392529054368811236215253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16261686036245874157476835 24392529054368811236215253)
        ·
          refine ⟨571699899711769013348795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 24392529054368811236215253 571699899711769013348795)
          ·
            refine ⟨857549849567653520023193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571699899711769013348795 857549849567653520023193)
            ·
              refine ⟨643162387175740140017395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 857549849567653520023193 643162387175740140017395)
              ·
                refine ⟨964743580763610210026093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643162387175740140017395 964743580763610210026093)
                ·
                  refine ⟨361778842786353828759785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 964743580763610210026093 361778842786353828759785)
                  ·
                    rfl

theorem cell20_792632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 3].length) (baseStart_792632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792632 prefixEnd_792632 := by exact prefixLift 792632
  have htrace : WordTrace (prefixWord ++ tailWord_792632) baseStart_792632 baseEnd_792632 := by
    simpa [prefixWord, tailWord_792632, baseEnd_792632] using wordTrace_append hprefix tailTrace_792632
  have hstable : (prefixWord ++ tailWord_792632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792632).length < 2 ^ (prefixWord ++ tailWord_792632).sum := by decide
  have hdescent : baseEnd_792632 < baseStart_792632 := by decide
  rcases family_descends (prefixWord ++ tailWord_792632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792677 : List Nat := [1, 3, 1, 3, 2, 4, 2, 2, 2]
def baseStart_792677 : Nat := 118140960795 + 792677 * 2 ^ 59
def prefixEnd_792677 : Nat := 4983230072969 + 3 ^ 40 * 792677 * 2
def baseEnd_792677 : Nat := 361799382012533672259601

theorem tailTrace_792677 : CollatzResearch.WordTrace tailWord_792677 prefixEnd_792677 361799382012533672259601 := by
  unfold tailWord_792677
  simp only [CollatzResearch.WordTrace]
  refine ⟨28911305349274082298680285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19274203566182721532453523 28911305349274082298680285)
  ·
    refine ⟨10841739505977780862005107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28911305349274082298680285 10841739505977780862005107)
    ·
      refine ⟨16262609258966671293007661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10841739505977780862005107 16262609258966671293007661)
      ·
        refine ⟨6098478472112501734877873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16262609258966671293007661 6098478472112501734877873)
        ·
          refine ⟨4573858854084376301158405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6098478472112501734877873 4573858854084376301158405)
          ·
            refine ⟨857598535140820556467201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4573858854084376301158405 857598535140820556467201)
            ·
              refine ⟨643198901355615417350401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 857598535140820556467201 643198901355615417350401)
              ·
                refine ⟨482399176016711563012801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 643198901355615417350401 482399176016711563012801)
                ·
                  refine ⟨361799382012533672259601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482399176016711563012801 361799382012533672259601)
                  ·
                    rfl

theorem cell20_792677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_792677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792677 prefixEnd_792677 := by exact prefixLift 792677
  have htrace : WordTrace (prefixWord ++ tailWord_792677) baseStart_792677 baseEnd_792677 := by
    simpa [prefixWord, tailWord_792677, baseEnd_792677] using wordTrace_append hprefix tailTrace_792677
  have hstable : (prefixWord ++ tailWord_792677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792677).length < 2 ^ (prefixWord ++ tailWord_792677).sum := by decide
  have hdescent : baseEnd_792677 < baseStart_792677 := by decide
  rcases family_descends (prefixWord ++ tailWord_792677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792681 : List Nat := [1, 2, 1, 1, 1, 5, 3, 4, 2]
def baseStart_792681 : Nat := 118140960795 + 792681 * 2 ^ 59
def prefixEnd_792681 : Nat := 4983230072969 + 3 ^ 40 * 792681 * 2
def baseEnd_792681 : Nat := 361801207721527436126251

theorem tailTrace_792681 : CollatzResearch.WordTrace tailWord_792681 prefixEnd_792681 361801207721527436126251 := by
  unfold tailWord_792681
  simp only [CollatzResearch.WordTrace]
  refine ⟨28911451241259590981825897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19274300827506393987883931 28911451241259590981825897)
  ·
    refine ⟨21683588430944693236369423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28911451241259590981825897 21683588430944693236369423)
    ·
      refine ⟨32525382646417039854554135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21683588430944693236369423 32525382646417039854554135)
      ·
        refine ⟨48788073969625559781831203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32525382646417039854554135 48788073969625559781831203)
        ·
          refine ⟨73182110954438339672746805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48788073969625559781831203 73182110954438339672746805)
          ·
            refine ⟨6860822901978594344320013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73182110954438339672746805 6860822901978594344320013)
            ·
              refine ⟨2572808588241972879120005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6860822901978594344320013 2572808588241972879120005)
              ·
                refine ⟨482401610295369914835001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2572808588241972879120005 482401610295369914835001)
                ·
                  refine ⟨361801207721527436126251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482401610295369914835001 361801207721527436126251)
                  ·
                    rfl

theorem cell20_792681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 2].length) (baseStart_792681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792681 prefixEnd_792681 := by exact prefixLift 792681
  have htrace : WordTrace (prefixWord ++ tailWord_792681) baseStart_792681 baseEnd_792681 := by
    simpa [prefixWord, tailWord_792681, baseEnd_792681] using wordTrace_append hprefix tailTrace_792681
  have hstable : (prefixWord ++ tailWord_792681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792681).length < 2 ^ (prefixWord ++ tailWord_792681).sum := by decide
  have hdescent : baseEnd_792681 < baseStart_792681 := by decide
  rcases family_descends (prefixWord ++ tailWord_792681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792688 : List Nat := [2, 1, 1, 1, 5, 4, 1, 5]
def baseStart_792688 : Nat := 118140960795 + 792688 * 2 ^ 59
def prefixEnd_792688 : Nat := 4983230072969 + 3 ^ 40 * 792688 * 2
def baseEnd_792688 : Nat := 120601467570755507630963

theorem tailTrace_792688 : CollatzResearch.WordTrace tailWord_792688 prefixEnd_792688 120601467570755507630963 := by
  unfold tailWord_792688
  simp only [CollatzResearch.WordTrace]
  refine ⟨14455853276117115588665359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19274471034822820784887145 14455853276117115588665359)
  ·
    refine ⟨21683779914175673382998039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14455853276117115588665359 21683779914175673382998039)
    ·
      refine ⟨32525669871263510074497059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21683779914175673382998039 32525669871263510074497059)
      ·
        refine ⟨48788504806895265111745589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32525669871263510074497059 48788504806895265111745589)
        ·
          refine ⟨4573922325646431104226149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48788504806895265111745589 4573922325646431104226149)
          ·
            refine ⟨857610436058705832042403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4573922325646431104226149 857610436058705832042403)
            ·
              refine ⟨1286415654088058748063605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857610436058705832042403 1286415654088058748063605)
              ·
                refine ⟨120601467570755507630963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1286415654088058748063605 120601467570755507630963)
                ·
                  rfl

theorem cell20_792688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_792688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792688 prefixEnd_792688 := by exact prefixLift 792688
  have htrace : WordTrace (prefixWord ++ tailWord_792688) baseStart_792688 baseEnd_792688 := by
    simpa [prefixWord, tailWord_792688, baseEnd_792688] using wordTrace_append hprefix tailTrace_792688
  have hstable : (prefixWord ++ tailWord_792688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792688).length < 2 ^ (prefixWord ++ tailWord_792688).sum := by decide
  have hdescent : baseEnd_792688 < baseStart_792688 := by decide
  rcases family_descends (prefixWord ++ tailWord_792688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792695 : List Nat := [1, 1, 3, 1, 1, 5, 2, 3, 3]
def baseStart_792695 : Nat := 118140960795 + 792695 * 2 ^ 59
def prefixEnd_792695 : Nat := 4983230072969 + 3 ^ 40 * 792695 * 2
def baseEnd_792695 : Nat := 361807597703005609659527

theorem tailTrace_792695 : CollatzResearch.WordTrace tailWord_792695 prefixEnd_792695 361807597703005609659527 := by
  unfold tailWord_792695
  simp only [CollatzResearch.WordTrace]
  refine ⟨28911961863208871372835539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19274641242139247581890359 28911961863208871372835539)
  ·
    refine ⟨43367942794813307059253309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28911961863208871372835539 43367942794813307059253309)
    ·
      refine ⟨16262978548054990147219991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43367942794813307059253309 16262978548054990147219991)
      ·
        refine ⟨24394467822082485220829987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16262978548054990147219991 24394467822082485220829987)
        ·
          refine ⟨36591701733123727831244981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24394467822082485220829987 36591701733123727831244981)
          ·
            refine ⟨3430472037480349484179217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36591701733123727831244981 3430472037480349484179217)
            ·
              refine ⟨2572854028110262113134413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3430472037480349484179217 2572854028110262113134413)
              ·
                refine ⟨964820260541348292425405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2572854028110262113134413 964820260541348292425405)
                ·
                  refine ⟨361807597703005609659527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 964820260541348292425405 361807597703005609659527)
                  ·
                    rfl

theorem cell20_792695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 3].length) (baseStart_792695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792695 prefixEnd_792695 := by exact prefixLift 792695
  have htrace : WordTrace (prefixWord ++ tailWord_792695) baseStart_792695 baseEnd_792695 := by
    simpa [prefixWord, tailWord_792695, baseEnd_792695] using wordTrace_append hprefix tailTrace_792695
  have hstable : (prefixWord ++ tailWord_792695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792695).length < 2 ^ (prefixWord ++ tailWord_792695).sum := by decide
  have hdescent : baseEnd_792695 < baseStart_792695 := by decide
  rcases family_descends (prefixWord ++ tailWord_792695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792705 : List Nat := [1, 2, 4, 2, 3, 1, 3, 4]
def baseStart_792705 : Nat := 118140960795 + 792705 * 2 ^ 59
def prefixEnd_792705 : Nat := 4983230072969 + 3 ^ 40 * 792705 * 2
def baseEnd_792705 : Nat := 120604053991830006442051

theorem tailTrace_792705 : CollatzResearch.WordTrace tailWord_792705 prefixEnd_792705 120604053991830006442051 := by
  unfold tailWord_792705
  simp only [CollatzResearch.WordTrace]
  refine ⟨28912326593172643080699569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19274884395448428720466379 28912326593172643080699569)
  ·
    refine ⟨21684244944879482310524677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28912326593172643080699569 21684244944879482310524677)
    ·
      refine ⟨4065795927164902933223377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21684244944879482310524677 4065795927164902933223377)
      ·
        refine ⟨3049346945373677199917533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4065795927164902933223377 3049346945373677199917533)
        ·
          refine ⟨1143505104515128949969075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3049346945373677199917533 1143505104515128949969075)
          ·
            refine ⟨1715257656772693424953613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1143505104515128949969075 1715257656772693424953613)
            ·
              refine ⟨643221621289760034357605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1715257656772693424953613 643221621289760034357605)
              ·
                refine ⟨120604053991830006442051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 643221621289760034357605 120604053991830006442051)
                ·
                  rfl

theorem cell20_792705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 3, 4].length) (baseStart_792705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792705 prefixEnd_792705 := by exact prefixLift 792705
  have htrace : WordTrace (prefixWord ++ tailWord_792705) baseStart_792705 baseEnd_792705 := by
    simpa [prefixWord, tailWord_792705, baseEnd_792705] using wordTrace_append hprefix tailTrace_792705
  have hstable : (prefixWord ++ tailWord_792705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792705).length < 2 ^ (prefixWord ++ tailWord_792705).sum := by decide
  have hdescent : baseEnd_792705 < baseStart_792705 := by decide
  rcases family_descends (prefixWord ++ tailWord_792705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792723 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 8]
def baseStart_792723 : Nat := 118140960795 + 792723 * 2 ^ 59
def prefixEnd_792723 : Nat := 4983230072969 + 3 ^ 40 * 792723 * 2
def baseEnd_792723 : Nat := 361820377665961956726079

theorem tailTrace_792723 : CollatzResearch.WordTrace tailWord_792723 prefixEnd_792723 361820377665961956726079 := by
  unfold tailWord_792723
  simp only [CollatzResearch.WordTrace]
  refine ⟨28912983107107432154854823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19275322071404954769903215 28912983107107432154854823)
  ·
    refine ⟨43369474660661148232282235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28912983107107432154854823 43369474660661148232282235)
    ·
      refine ⟨65054211990991722348423353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43369474660661148232282235 65054211990991722348423353)
      ·
        refine ⟨48790658993243791761317515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65054211990991722348423353 48790658993243791761317515)
        ·
          refine ⟨73185988489865687641976273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48790658993243791761317515 73185988489865687641976273)
          ·
            refine ⟨54889491367399265731482205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73185988489865687641976273 54889491367399265731482205)
            ·
              refine ⟨20583559262774724649305827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54889491367399265731482205 20583559262774724649305827)
              ·
                refine ⟨30875338894162086973958741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20583559262774724649305827 30875338894162086973958741)
                ·
                  refine ⟨361820377665961956726079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30875338894162086973958741 361820377665961956726079)
                  ·
                    rfl

theorem cell20_792723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_792723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792723 prefixEnd_792723 := by exact prefixLift 792723
  have htrace : WordTrace (prefixWord ++ tailWord_792723) baseStart_792723 baseEnd_792723 := by
    simpa [prefixWord, tailWord_792723, baseEnd_792723] using wordTrace_append hprefix tailTrace_792723
  have hstable : (prefixWord ++ tailWord_792723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792723).length < 2 ^ (prefixWord ++ tailWord_792723).sum := by decide
  have hdescent : baseEnd_792723 < baseStart_792723 := by decide
  rcases family_descends (prefixWord ++ tailWord_792723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792733 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 5]
def baseStart_792733 : Nat := 118140960795 + 792733 * 2 ^ 59
def prefixEnd_792733 : Nat := 4983230072969 + 3 ^ 40 * 792733 * 2
def baseEnd_792733 : Nat := 361824941938446366392705

theorem tailTrace_792733 : CollatzResearch.WordTrace tailWord_792733 prefixEnd_792733 361824941938446366392705 := by
  unfold tailWord_792733
  simp only [CollatzResearch.WordTrace]
  refine ⟨28913347837071203862718853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19275565224714135908479235 28913347837071203862718853)
  ·
    refine ⟨5421252719450850724259785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28913347837071203862718853 5421252719450850724259785)
    ·
      refine ⟨4065939539588138043194839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5421252719450850724259785 4065939539588138043194839)
      ·
        refine ⟨6098909309382207064792259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4065939539588138043194839 6098909309382207064792259)
        ·
          refine ⟨9148363964073310597188389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6098909309382207064792259 9148363964073310597188389)
          ·
            refine ⟨1715318243263745736972823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9148363964073310597188389 1715318243263745736972823)
            ·
              refine ⟨2572977364895618605459235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1715318243263745736972823 2572977364895618605459235)
              ·
                refine ⟨3859466047343427908188853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2572977364895618605459235 3859466047343427908188853)
                ·
                  refine ⟨361824941938446366392705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3859466047343427908188853 361824941938446366392705)
                  ·
                    rfl

theorem cell20_792733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_792733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792733 prefixEnd_792733 := by exact prefixLift 792733
  have htrace : WordTrace (prefixWord ++ tailWord_792733) baseStart_792733 baseEnd_792733 := by
    simpa [prefixWord, tailWord_792733, baseEnd_792733] using wordTrace_append hprefix tailTrace_792733
  have hstable : (prefixWord ++ tailWord_792733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792733).length < 2 ^ (prefixWord ++ tailWord_792733).sum := by decide
  have hdescent : baseEnd_792733 < baseStart_792733 := by decide
  rcases family_descends (prefixWord ++ tailWord_792733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792746 : List Nat := [3, 1, 5, 1, 2, 1, 3, 1, 3]
def baseStart_792746 : Nat := 118140960795 + 792746 * 2 ^ 59
def prefixEnd_792746 : Nat := 4983230072969 + 3 ^ 40 * 792746 * 2
def baseEnd_792746 : Nat := 361830875492676098959319

theorem tailTrace_792746 : CollatzResearch.WordTrace tailWord_792746 prefixEnd_792746 361830875492676098959319 := by
  unfold tailWord_792746
  simp only [CollatzResearch.WordTrace]
  refine ⟨7228455496506026770735523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19275881324016071388628061 7228455496506026770735523)
  ·
    refine ⟨10842683244759040156103285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7228455496506026770735523 10842683244759040156103285)
    ·
      refine ⟨1016501554196160014634683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10842683244759040156103285 1016501554196160014634683)
      ·
        refine ⟨1524752331294240021952025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016501554196160014634683 1524752331294240021952025)
        ·
          refine ⟨1143564248470680016464019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1524752331294240021952025 1143564248470680016464019)
          ·
            refine ⟨1715346372706020024696029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1143564248470680016464019 1715346372706020024696029)
            ·
              refine ⟨643254889764757509261011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1715346372706020024696029 643254889764757509261011)
              ·
                refine ⟨964882334647136263891517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643254889764757509261011 964882334647136263891517)
                ·
                  refine ⟨361830875492676098959319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 964882334647136263891517 361830875492676098959319)
                  ·
                    rfl

theorem cell20_792746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_792746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792746 prefixEnd_792746 := by exact prefixLift 792746
  have htrace : WordTrace (prefixWord ++ tailWord_792746) baseStart_792746 baseEnd_792746 := by
    simpa [prefixWord, tailWord_792746, baseEnd_792746] using wordTrace_append hprefix tailTrace_792746
  have hstable : (prefixWord ++ tailWord_792746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792746).length < 2 ^ (prefixWord ++ tailWord_792746).sum := by decide
  have hdescent : baseEnd_792746 < baseStart_792746 := by decide
  rcases family_descends (prefixWord ++ tailWord_792746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792756 : List Nat := [2, 5, 3, 1, 1, 2, 2, 4]
def baseStart_792756 : Nat := 118140960795 + 792756 * 2 ^ 59
def prefixEnd_792756 : Nat := 4983230072969 + 3 ^ 40 * 792756 * 2
def baseEnd_792756 : Nat := 120611813255053502875315

theorem tailTrace_792756 : CollatzResearch.WordTrace tailWord_792756 prefixEnd_792756 120611813255053502875315 := by
  unfold tailWord_792756
  simp only [CollatzResearch.WordTrace]
  refine ⟨14457093357993939395403061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19276124477325252527204081 14457093357993939395403061)
  ·
    refine ⟨1355352502311931818319037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14457093357993939395403061 1355352502311931818319037)
    ·
      refine ⟨508257188366974431869639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1355352502311931818319037 508257188366974431869639)
      ·
        refine ⟨762385782550461647804459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508257188366974431869639 762385782550461647804459)
        ·
          refine ⟨1143578673825692471706689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762385782550461647804459 1143578673825692471706689)
          ·
            refine ⟨857684005369269353780017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1143578673825692471706689 857684005369269353780017)
            ·
              refine ⟨643263004026952015335013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 857684005369269353780017 643263004026952015335013)
              ·
                refine ⟨120611813255053502875315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 643263004026952015335013 120611813255053502875315)
                ·
                  rfl

theorem cell20_792756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 2, 4].length) (baseStart_792756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792756 prefixEnd_792756 := by exact prefixLift 792756
  have htrace : WordTrace (prefixWord ++ tailWord_792756) baseStart_792756 baseEnd_792756 := by
    simpa [prefixWord, tailWord_792756, baseEnd_792756] using wordTrace_append hprefix tailTrace_792756
  have hstable : (prefixWord ++ tailWord_792756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792756).length < 2 ^ (prefixWord ++ tailWord_792756).sum := by decide
  have hdescent : baseEnd_792756 < baseStart_792756 := by decide
  rcases family_descends (prefixWord ++ tailWord_792756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792764 : List Nat := [2, 2, 2, 3, 3, 1, 1, 6]
def baseStart_792764 : Nat := 118140960795 + 792764 * 2 ^ 59
def prefixEnd_792764 : Nat := 4983230072969 + 3 ^ 40 * 792764 * 2
def baseEnd_792764 : Nat := 120613030394382678786415

theorem tailTrace_792764 : CollatzResearch.WordTrace tailWord_792764 prefixEnd_792764 120613030394382678786415 := by
  unfold tailWord_792764
  simp only [CollatzResearch.WordTrace]
  refine ⟨14457239249979448078548673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19276318999972597438064897 14457239249979448078548673)
  ·
    refine ⟨10842929437484586058911505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14457239249979448078548673 10842929437484586058911505)
    ·
      refine ⟨8132197078113439544183629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10842929437484586058911505 8132197078113439544183629)
      ·
        refine ⟨3049573904292539829068861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8132197078113439544183629 3049573904292539829068861)
        ·
          refine ⟨1143590214109702435900823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3049573904292539829068861 1143590214109702435900823)
          ·
            refine ⟨1715385321164553653851235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1143590214109702435900823 1715385321164553653851235)
            ·
              refine ⟨2573077981746830480776853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1715385321164553653851235 2573077981746830480776853)
              ·
                refine ⟨120613030394382678786415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2573077981746830480776853 120613030394382678786415)
                ·
                  rfl

theorem cell20_792764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_792764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792764 prefixEnd_792764 := by exact prefixLift 792764
  have htrace : WordTrace (prefixWord ++ tailWord_792764) baseStart_792764 baseEnd_792764 := by
    simpa [prefixWord, tailWord_792764, baseEnd_792764] using wordTrace_append hprefix tailTrace_792764
  have hstable : (prefixWord ++ tailWord_792764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792764).length < 2 ^ (prefixWord ++ tailWord_792764).sum := by decide
  have hdescent : baseEnd_792764 < baseStart_792764 := by decide
  rcases family_descends (prefixWord ++ tailWord_792764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792770 : List Nat := [3, 5, 1, 1, 1, 1, 3, 3, 2]
def baseStart_792770 : Nat := 118140960795 + 792770 * 2 ^ 59
def prefixEnd_792770 : Nat := 4983230072969 + 3 ^ 40 * 792770 * 2
def baseEnd_792770 : Nat := 361841829746638682159221

theorem tailTrace_792770 : CollatzResearch.WordTrace tailWord_792770 prefixEnd_792770 361841829746638682159221 := by
  unfold tailWord_792770
  simp only [CollatzResearch.WordTrace]
  refine ⟨7228674334484289795453941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19276464891958106121210509 7228674334484289795453941)
  ·
    refine ⟨677688218857902168323807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7228674334484289795453941 677688218857902168323807)
    ·
      refine ⟨1016532328286853252485711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 677688218857902168323807 1016532328286853252485711)
      ·
        refine ⟨1524798492430279878728567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016532328286853252485711 1524798492430279878728567)
        ·
          refine ⟨2287197738645419818092851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524798492430279878728567 2287197738645419818092851)
          ·
            refine ⟨3430796607968129727139277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2287197738645419818092851 3430796607968129727139277)
            ·
              refine ⟨1286548727988048647677229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3430796607968129727139277 1286548727988048647677229)
              ·
                refine ⟨482455772995518242878961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1286548727988048647677229 482455772995518242878961)
                ·
                  refine ⟨361841829746638682159221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482455772995518242878961 361841829746638682159221)
                  ·
                    rfl

theorem cell20_792770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_792770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792770 prefixEnd_792770 := by exact prefixLift 792770
  have htrace : WordTrace (prefixWord ++ tailWord_792770) baseStart_792770 baseEnd_792770 := by
    simpa [prefixWord, tailWord_792770, baseEnd_792770] using wordTrace_append hprefix tailTrace_792770
  have hstable : (prefixWord ++ tailWord_792770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792770).length < 2 ^ (prefixWord ++ tailWord_792770).sum := by decide
  have hdescent : baseEnd_792770 < baseStart_792770 := by decide
  rcases family_descends (prefixWord ++ tailWord_792770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792805 : List Nat := [1, 3, 1, 4, 2, 3, 2, 1, 3]
def baseStart_792805 : Nat := 118140960795 + 792805 * 2 ^ 59
def prefixEnd_792805 : Nat := 4983230072969 + 3 ^ 40 * 792805 * 2
def baseEnd_792805 : Nat := 361857804700334115992411

theorem tailTrace_792805 : CollatzResearch.WordTrace tailWord_792805 prefixEnd_792805 361857804700334115992411 := by
  unfold tailWord_792805
  simp only [CollatzResearch.WordTrace]
  refine ⟨28915973892810360159339869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19277315928540240106226579 28915973892810360159339869)
  ·
    refine ⟨10843490209803885059752451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28915973892810360159339869 10843490209803885059752451)
    ·
      refine ⟨16265235314705827589628677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10843490209803885059752451 16265235314705827589628677)
      ·
        refine ⟨3049731621507342673055377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16265235314705827589628677 3049731621507342673055377)
        ·
          refine ⟨2287298716130507004791533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3049731621507342673055377 2287298716130507004791533)
          ·
            refine ⟨857737018548940126796825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2287298716130507004791533 857737018548940126796825)
            ·
              refine ⟨643302763911705095097619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 857737018548940126796825 643302763911705095097619)
              ·
                refine ⟨964954145867557642646429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643302763911705095097619 964954145867557642646429)
                ·
                  refine ⟨361857804700334115992411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 964954145867557642646429 361857804700334115992411)
                  ·
                    rfl

theorem cell20_792805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_792805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792805 prefixEnd_792805 := by exact prefixLift 792805
  have htrace : WordTrace (prefixWord ++ tailWord_792805) baseStart_792805 baseEnd_792805 := by
    simpa [prefixWord, tailWord_792805, baseEnd_792805] using wordTrace_append hprefix tailTrace_792805
  have hstable : (prefixWord ++ tailWord_792805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792805).length < 2 ^ (prefixWord ++ tailWord_792805).sum := by decide
  have hdescent : baseEnd_792805 < baseStart_792805 := by decide
  rcases family_descends (prefixWord ++ tailWord_792805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792833 : List Nat := [1, 2, 4, 1, 1, 2, 2, 5, 2]
def baseStart_792833 : Nat := 118140960795 + 792833 * 2 ^ 59
def prefixEnd_792833 : Nat := 4983230072969 + 3 ^ 40 * 792833 * 2
def baseEnd_792833 : Nat := 361870584663290463058963

theorem tailTrace_792833 : CollatzResearch.WordTrace tailWord_792833 prefixEnd_792833 361870584663290463058963 := by
  unfold tailWord_792833
  simp only [CollatzResearch.WordTrace]
  refine ⟨28916995136708920941359153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19277996757805947294239435 28916995136708920941359153)
  ·
    refine ⟨21687746352531690706019365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28916995136708920941359153 21687746352531690706019365)
    ·
      refine ⟨4066452441099692007378631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21687746352531690706019365 4066452441099692007378631)
      ·
        refine ⟨6099678661649538011067947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4066452441099692007378631 6099678661649538011067947)
        ·
          refine ⟨9149517992474307016601921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6099678661649538011067947 9149517992474307016601921)
          ·
            refine ⟨6862138494355730262451441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9149517992474307016601921 6862138494355730262451441)
            ·
              refine ⟨5146603870766797696838581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6862138494355730262451441 5146603870766797696838581)
              ·
                refine ⟨482494112884387284078617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5146603870766797696838581 482494112884387284078617)
                ·
                  refine ⟨361870584663290463058963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482494112884387284078617 361870584663290463058963)
                  ·
                    rfl

theorem cell20_792833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 5, 2].length) (baseStart_792833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792833 prefixEnd_792833 := by exact prefixLift 792833
  have htrace : WordTrace (prefixWord ++ tailWord_792833) baseStart_792833 baseEnd_792833 := by
    simpa [prefixWord, tailWord_792833, baseEnd_792833] using wordTrace_append hprefix tailTrace_792833
  have hstable : (prefixWord ++ tailWord_792833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792833).length < 2 ^ (prefixWord ++ tailWord_792833).sum := by decide
  have hdescent : baseEnd_792833 < baseStart_792833 := by decide
  rcases family_descends (prefixWord ++ tailWord_792833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792837 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 8]
def baseStart_792837 : Nat := 118140960795 + 792837 * 2 ^ 59
def prefixEnd_792837 : Nat := 4983230072969 + 3 ^ 40 * 792837 * 2
def baseEnd_792837 : Nat := 361872410372284226925613

theorem tailTrace_792837 : CollatzResearch.WordTrace tailWord_792837 prefixEnd_792837 361872410372284226925613 := by
  unfold tailWord_792837
  simp only [CollatzResearch.WordTrace]
  refine ⟨28917141028694429624504765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19278094019129619749669843 28917141028694429624504765)
  ·
    refine ⟨10843927885760411109189287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28917141028694429624504765 10843927885760411109189287)
    ·
      refine ⟨16265891828640616663783931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10843927885760411109189287 16265891828640616663783931)
      ·
        refine ⟨24398837742960924995675897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16265891828640616663783931 24398837742960924995675897)
        ·
          refine ⟨18299128307220693746756923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24398837742960924995675897 18299128307220693746756923)
          ·
            refine ⟨27448692460831040620135385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18299128307220693746756923 27448692460831040620135385)
            ·
              refine ⟨20586519345623280465101539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27448692460831040620135385 20586519345623280465101539)
              ·
                refine ⟨30879779018434920697652309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20586519345623280465101539 30879779018434920697652309)
                ·
                  refine ⟨361872410372284226925613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30879779018434920697652309 361872410372284226925613)
                  ·
                    rfl

theorem cell20_792837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_792837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792837 prefixEnd_792837 := by exact prefixLift 792837
  have htrace : WordTrace (prefixWord ++ tailWord_792837) baseStart_792837 baseEnd_792837 := by
    simpa [prefixWord, tailWord_792837, baseEnd_792837] using wordTrace_append hprefix tailTrace_792837
  have hstable : (prefixWord ++ tailWord_792837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792837).length < 2 ^ (prefixWord ++ tailWord_792837).sum := by decide
  have hdescent : baseEnd_792837 < baseStart_792837 := by decide
  rcases family_descends (prefixWord ++ tailWord_792837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792944 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 5]
def baseStart_792944 : Nat := 118140960795 + 792944 * 2 ^ 59
def prefixEnd_792944 : Nat := 4983230072969 + 3 ^ 40 * 792944 * 2
def baseEnd_792944 : Nat := 361921248087867410358509

theorem tailTrace_792944 : CollatzResearch.WordTrace tailWord_792944 prefixEnd_792944 361921248087867410358509 := by
  unfold tailWord_792944
  simp only [CollatzResearch.WordTrace]
  refine ⟨14460521819653393449324943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19280695759537857932433257 14460521819653393449324943)
  ·
    refine ⟨21690782729480090173987415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14460521819653393449324943 21690782729480090173987415)
    ·
      refine ⟨32536174094220135260981123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21690782729480090173987415 32536174094220135260981123)
      ·
        refine ⟨48804261141330202891471685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32536174094220135260981123 48804261141330202891471685)
        ·
          refine ⟨9150798963999413042150941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48804261141330202891471685 9150798963999413042150941)
          ·
            refine ⟨3431549611499779890806603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9150798963999413042150941 3431549611499779890806603)
            ·
              refine ⟨5147324417249669836209905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3431549611499779890806603 5147324417249669836209905)
              ·
                refine ⟨3860493312937252377157429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5147324417249669836209905 3860493312937252377157429)
                ·
                  refine ⟨361921248087867410358509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3860493312937252377157429 361921248087867410358509)
                  ·
                    rfl

theorem cell20_792944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_792944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792944 prefixEnd_792944 := by exact prefixLift 792944
  have htrace : WordTrace (prefixWord ++ tailWord_792944) baseStart_792944 baseEnd_792944 := by
    simpa [prefixWord, tailWord_792944, baseEnd_792944] using wordTrace_append hprefix tailTrace_792944
  have hstable : (prefixWord ++ tailWord_792944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792944).length < 2 ^ (prefixWord ++ tailWord_792944).sum := by decide
  have hdescent : baseEnd_792944 < baseStart_792944 := by decide
  rcases family_descends (prefixWord ++ tailWord_792944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792950 : List Nat := [5, 1, 1, 4, 2, 1, 6]
def baseStart_792950 : Nat := 118140960795 + 792950 * 2 ^ 59
def prefixEnd_792950 : Nat := 4983230072969 + 3 ^ 40 * 792950 * 2
def baseEnd_792950 : Nat := 40213776294595339573165

theorem tailTrace_792950 : CollatzResearch.WordTrace tailWord_792950 prefixEnd_792950 40213776294595339573165 := by
  unfold tailWord_792950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1807578904830315620210519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19280841651523366615578869 1807578904830315620210519)
  ·
    refine ⟨2711368357245473430315779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1807578904830315620210519 2711368357245473430315779)
    ·
      refine ⟨4067052535868210145473669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2711368357245473430315779 4067052535868210145473669)
      ·
        refine ⟨762572350475289402276313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4067052535868210145473669 762572350475289402276313)
        ·
          refine ⟨571929262856467051707235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 762572350475289402276313 571929262856467051707235)
          ·
            refine ⟨857893894284700577560853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571929262856467051707235 857893894284700577560853)
            ·
              refine ⟨40213776294595339573165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 857893894284700577560853 40213776294595339573165)
              ·
                rfl

theorem cell20_792950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 6].length) (baseStart_792950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792950 prefixEnd_792950 := by exact prefixLift 792950
  have htrace : WordTrace (prefixWord ++ tailWord_792950) baseStart_792950 baseEnd_792950 := by
    simpa [prefixWord, tailWord_792950, baseEnd_792950] using wordTrace_append hprefix tailTrace_792950
  have hstable : (prefixWord ++ tailWord_792950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792950).length < 2 ^ (prefixWord ++ tailWord_792950).sum := by decide
  have hdescent : baseEnd_792950 < baseStart_792950 := by decide
  rcases family_descends (prefixWord ++ tailWord_792950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792961 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 5]
def baseStart_792961 : Nat := 118140960795 + 792961 * 2 ^ 59
def prefixEnd_792961 : Nat := 4983230072969 + 3 ^ 40 * 792961 * 2
def baseEnd_792961 : Nat := 361929007351090906791773

theorem tailTrace_792961 : CollatzResearch.WordTrace tailWord_792961 prefixEnd_792961 361929007351090906791773 := by
  unfold tailWord_792961
  simp only [CollatzResearch.WordTrace]
  refine ⟨28921663680245198802018737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19281109120163465868012491 28921663680245198802018737)
  ·
    refine ⟨21691247760183899101514053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28921663680245198802018737 21691247760183899101514053)
    ·
      refine ⟨4067108955034481081533885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21691247760183899101514053 4067108955034481081533885)
      ·
        refine ⟨1525165858137930405575207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4067108955034481081533885 1525165858137930405575207)
        ·
          refine ⟨2287748787206895608362811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1525165858137930405575207 2287748787206895608362811)
          ·
            refine ⟨3431623180810343412544217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2287748787206895608362811 3431623180810343412544217)
            ·
              refine ⟨2573717385607757559408163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3431623180810343412544217 2573717385607757559408163)
              ·
                refine ⟨3860576078411636339112245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2573717385607757559408163 3860576078411636339112245)
                ·
                  refine ⟨361929007351090906791773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3860576078411636339112245 361929007351090906791773)
                  ·
                    rfl

theorem cell20_792961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_792961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792961 prefixEnd_792961 := by exact prefixLift 792961
  have htrace : WordTrace (prefixWord ++ tailWord_792961) baseStart_792961 baseEnd_792961 := by
    simpa [prefixWord, tailWord_792961, baseEnd_792961] using wordTrace_append hprefix tailTrace_792961
  have hstable : (prefixWord ++ tailWord_792961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792961).length < 2 ^ (prefixWord ++ tailWord_792961).sum := by decide
  have hdescent : baseEnd_792961 < baseStart_792961 := by decide
  rcases family_descends (prefixWord ++ tailWord_792961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792964 : List Nat := [2, 3, 2, 1, 1, 2, 5, 2, 2]
def baseStart_792964 : Nat := 118140960795 + 792964 * 2 ^ 59
def prefixEnd_792964 : Nat := 4983230072969 + 3 ^ 40 * 792964 * 2
def baseEnd_792964 : Nat := 361930376632836229691761

theorem tailTrace_792964 : CollatzResearch.WordTrace tailWord_792964 prefixEnd_792964 361930376632836229691761 := by
  unfold tailWord_792964
  simp only [CollatzResearch.WordTrace]
  refine ⟨14460886549617165157188973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19281182066156220209585297 14460886549617165157188973)
  ·
    refine ⟨5422832456106436933945865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14460886549617165157188973 5422832456106436933945865)
    ·
      refine ⟨4067124342079827700459399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5422832456106436933945865 4067124342079827700459399)
      ·
        refine ⟨6100686513119741550689099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4067124342079827700459399 6100686513119741550689099)
        ·
          refine ⟨9151029769679612326033649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6100686513119741550689099 9151029769679612326033649)
          ·
            refine ⟨6863272327259709244525237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9151029769679612326033649 6863272327259709244525237)
            ·
              refine ⟨643431780680597741674241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6863272327259709244525237 643431780680597741674241)
              ·
                refine ⟨482573835510448306255681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 643431780680597741674241 482573835510448306255681)
                ·
                  refine ⟨361930376632836229691761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482573835510448306255681 361930376632836229691761)
                  ·
                    rfl

theorem cell20_792964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_792964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_792964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_792964 prefixEnd_792964 := by exact prefixLift 792964
  have htrace : WordTrace (prefixWord ++ tailWord_792964) baseStart_792964 baseEnd_792964 := by
    simpa [prefixWord, tailWord_792964, baseEnd_792964] using wordTrace_append hprefix tailTrace_792964
  have hstable : (prefixWord ++ tailWord_792964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792964).length < 2 ^ (prefixWord ++ tailWord_792964).sum := by decide
  have hdescent : baseEnd_792964 < baseStart_792964 := by decide
  rcases family_descends (prefixWord ++ tailWord_792964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793012 : List Nat := [2, 5, 2, 2, 1, 1, 2, 2, 3]
def baseStart_793012 : Nat := 118140960795 + 793012 * 2 ^ 59
def prefixEnd_793012 : Nat := 4983230072969 + 3 ^ 40 * 793012 * 2
def baseEnd_793012 : Nat := 361952285140761396091565

theorem tailTrace_793012 : CollatzResearch.WordTrace tailWord_793012 prefixEnd_793012 361952285140761396091565 := by
  unfold tailWord_793012
  simp only [CollatzResearch.WordTrace]
  refine ⟨14461761901530217256062645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19282349202040289674750193 14461761901530217256062645)
  ·
    refine ⟨1355790178268457867755873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14461761901530217256062645 1355790178268457867755873)
    ·
      refine ⟨1016842633701343400816905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1355790178268457867755873 1016842633701343400816905)
      ·
        refine ⟨762631975276007550612679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1016842633701343400816905 762631975276007550612679)
        ·
          refine ⟨1143947962914011325919019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762631975276007550612679 1143947962914011325919019)
          ·
            refine ⟨1715921944371016988878529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1143947962914011325919019 1715921944371016988878529)
            ·
              refine ⟨1286941458278262741658897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1715921944371016988878529 1286941458278262741658897)
              ·
                refine ⟨965206093708697056244173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286941458278262741658897 965206093708697056244173)
                ·
                  refine ⟨361952285140761396091565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 965206093708697056244173 361952285140761396091565)
                  ·
                    rfl

theorem cell20_793012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_793012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793012 prefixEnd_793012 := by exact prefixLift 793012
  have htrace : WordTrace (prefixWord ++ tailWord_793012) baseStart_793012 baseEnd_793012 := by
    simpa [prefixWord, tailWord_793012, baseEnd_793012] using wordTrace_append hprefix tailTrace_793012
  have hstable : (prefixWord ++ tailWord_793012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793012).length < 2 ^ (prefixWord ++ tailWord_793012).sum := by decide
  have hdescent : baseEnd_793012 < baseStart_793012 := by decide
  rcases family_descends (prefixWord ++ tailWord_793012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793013 : List Nat := [1, 3, 3, 2, 3, 8]
def baseStart_793013 : Nat := 118140960795 + 793013 * 2 ^ 59
def prefixEnd_793013 : Nat := 4983230072969 + 3 ^ 40 * 793013 * 2
def baseEnd_793013 : Nat := 13405657095111475446601

theorem tailTrace_793013 : CollatzResearch.WordTrace tailWord_793013 prefixEnd_793013 13405657095111475446601 := by
  unfold tailWord_793013
  simp only [CollatzResearch.WordTrace]
  refine ⟨28923560276056811682911693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19282373517371207788607795 28923560276056811682911693)
  ·
    refine ⟨10846335103521304381091885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28923560276056811682911693 10846335103521304381091885)
    ·
      refine ⟨4067375663820489142909457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10846335103521304381091885 4067375663820489142909457)
      ·
        refine ⟨3050531747865366857182093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4067375663820489142909457 3050531747865366857182093)
        ·
          refine ⟨1143949405449512571443285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3050531747865366857182093 1143949405449512571443285)
          ·
            refine ⟨13405657095111475446601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1143949405449512571443285 13405657095111475446601)
            ·
              rfl

theorem cell20_793013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 8].length) (baseStart_793013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793013 prefixEnd_793013 := by exact prefixLift 793013
  have htrace : WordTrace (prefixWord ++ tailWord_793013) baseStart_793013 baseEnd_793013 := by
    simpa [prefixWord, tailWord_793013, baseEnd_793013] using wordTrace_append hprefix tailTrace_793013
  have hstable : (prefixWord ++ tailWord_793013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793013).length < 2 ^ (prefixWord ++ tailWord_793013).sum := by decide
  have hdescent : baseEnd_793013 < baseStart_793013 := by decide
  rcases family_descends (prefixWord ++ tailWord_793013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793027 : List Nat := [1, 1, 1, 3, 1, 1, 3, 5, 4]
def baseStart_793027 : Nat := 118140960795 + 793027 * 2 ^ 59
def prefixEnd_793027 : Nat := 4983230072969 + 3 ^ 40 * 793027 * 2
def baseEnd_793027 : Nat := 361959131549488010591503

theorem tailTrace_793027 : CollatzResearch.WordTrace tailWord_793027 prefixEnd_793027 361959131549488010591503 := by
  unfold tailWord_793027
  simp only [CollatzResearch.WordTrace]
  refine ⟨28924070898006092073921335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19282713932004061382614223 28924070898006092073921335)
  ·
    refine ⟨43386106347009138110882003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28924070898006092073921335 43386106347009138110882003)
    ·
      refine ⟨65079159520513707166323005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43386106347009138110882003 65079159520513707166323005)
      ·
        refine ⟨24404684820192640187371127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65079159520513707166323005 24404684820192640187371127)
        ·
          refine ⟨36607027230288960281056691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24404684820192640187371127 36607027230288960281056691)
          ·
            refine ⟨54910540845433440421585037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36607027230288960281056691 54910540845433440421585037)
            ·
              refine ⟨20591452817037540158094389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54910540845433440421585037 20591452817037540158094389)
              ·
                refine ⟨1930448701597269389821349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20591452817037540158094389 1930448701597269389821349)
                ·
                  refine ⟨361959131549488010591503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1930448701597269389821349 361959131549488010591503)
                  ·
                    rfl

theorem cell20_793027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_793027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793027 prefixEnd_793027 := by exact prefixLift 793027
  have htrace : WordTrace (prefixWord ++ tailWord_793027) baseStart_793027 baseEnd_793027 := by
    simpa [prefixWord, tailWord_793027, baseEnd_793027] using wordTrace_append hprefix tailTrace_793027
  have hstable : (prefixWord ++ tailWord_793027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793027).length < 2 ^ (prefixWord ++ tailWord_793027).sum := by decide
  have hdescent : baseEnd_793027 < baseStart_793027 := by decide
  rcases family_descends (prefixWord ++ tailWord_793027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793044 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 6]
def baseStart_793044 : Nat := 118140960795 + 793044 * 2 ^ 59
def prefixEnd_793044 : Nat := 4983230072969 + 3 ^ 40 * 793044 * 2
def baseEnd_793044 : Nat := 361966890812711507024767

theorem tailTrace_793044 : CollatzResearch.WordTrace tailWord_793044 prefixEnd_793044 361966890812711507024767 := by
  unfold tailWord_793044
  simp only [CollatzResearch.WordTrace]
  refine ⟨14462345469472251988645093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19283127292629669318193457 14462345469472251988645093)
  ·
    refine ⟨2711689775526047247870955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14462345469472251988645093 2711689775526047247870955)
    ·
      refine ⟨4067534663289070871806433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2711689775526047247870955 4067534663289070871806433)
      ·
        refine ⟨3050650997466803153854825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4067534663289070871806433 3050650997466803153854825)
        ·
          refine ⟨2287988248100102365391119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3050650997466803153854825 2287988248100102365391119)
          ·
            refine ⟨3431982372150153548086679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2287988248100102365391119 3431982372150153548086679)
            ·
              refine ⟨5147973558225230322130019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3431982372150153548086679 5147973558225230322130019)
              ·
                refine ⟨7721960337337845483195029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5147973558225230322130019 7721960337337845483195029)
                ·
                  refine ⟨361966890812711507024767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7721960337337845483195029 361966890812711507024767)
                  ·
                    rfl

theorem cell20_793044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_793044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793044 prefixEnd_793044 := by exact prefixLift 793044
  have htrace : WordTrace (prefixWord ++ tailWord_793044) baseStart_793044 baseEnd_793044 := by
    simpa [prefixWord, tailWord_793044, baseEnd_793044] using wordTrace_append hprefix tailTrace_793044
  have hstable : (prefixWord ++ tailWord_793044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793044).length < 2 ^ (prefixWord ++ tailWord_793044).sum := by decide
  have hdescent : baseEnd_793044 < baseStart_793044 := by decide
  rcases family_descends (prefixWord ++ tailWord_793044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793072 : List Nat := [2, 1, 1, 1, 3, 3, 9]
def baseStart_793072 : Nat := 118140960795 + 793072 * 2 ^ 59
def prefixEnd_793072 : Nat := 4983230072969 + 3 ^ 40 * 793072 * 2
def baseEnd_793072 : Nat := 40219963419518650454591

theorem tailTrace_793072 : CollatzResearch.WordTrace tailWord_793072 prefixEnd_793072 40219963419518650454591 := by
  unfold tailWord_793072
  simp only [CollatzResearch.WordTrace]
  refine ⟨14462856091421532379654735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19283808121895376506206313 14462856091421532379654735)
  ·
    refine ⟨21694284137132298569482103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14462856091421532379654735 21694284137132298569482103)
    ·
      refine ⟨32541426205698447854223155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21694284137132298569482103 32541426205698447854223155)
      ·
        refine ⟨48812139308547671781334733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32541426205698447854223155 48812139308547671781334733)
        ·
          refine ⟨18304552240705376918000525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48812139308547671781334733 18304552240705376918000525)
          ·
            refine ⟨6864207090264516344250197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18304552240705376918000525 6864207090264516344250197)
            ·
              refine ⟨40219963419518650454591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6864207090264516344250197 40219963419518650454591)
              ·
                rfl

theorem cell20_793072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 9].length) (baseStart_793072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793072 prefixEnd_793072 := by exact prefixLift 793072
  have htrace : WordTrace (prefixWord ++ tailWord_793072) baseStart_793072 baseEnd_793072 := by
    simpa [prefixWord, tailWord_793072, baseEnd_793072] using wordTrace_append hprefix tailTrace_793072
  have hstable : (prefixWord ++ tailWord_793072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793072).length < 2 ^ (prefixWord ++ tailWord_793072).sum := by decide
  have hdescent : baseEnd_793072 < baseStart_793072 := by decide
  rcases family_descends (prefixWord ++ tailWord_793072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793116 : List Nat := [2, 2, 3, 1, 2, 4, 1, 3, 2]
def baseStart_793116 : Nat := 118140960795 + 793116 * 2 ^ 59
def prefixEnd_793116 : Nat := 4983230072969 + 3 ^ 40 * 793116 * 2
def baseEnd_793116 : Nat := 361999753574599256624473

theorem tailTrace_793116 : CollatzResearch.WordTrace tailWord_793116 prefixEnd_793116 361999753574599256624473 := by
  unfold tailWord_793116
  simp only [CollatzResearch.WordTrace]
  refine ⟨14463658497341830136955601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19284877996455773515940801 14463658497341830136955601)
  ·
    refine ⟨10847743873006372602716701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14463658497341830136955601 10847743873006372602716701)
    ·
      refine ⟨4067903952377389726018763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10847743873006372602716701 4067903952377389726018763)
      ·
        refine ⟨6101855928566084589028145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4067903952377389726018763 6101855928566084589028145)
        ·
          refine ⟨4576391946424563441771109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6101855928566084589028145 4576391946424563441771109)
          ·
            refine ⟨858073489954605645332083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4576391946424563441771109 858073489954605645332083)
            ·
              refine ⟨1287110234931908467998125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858073489954605645332083 1287110234931908467998125)
              ·
                refine ⟨482666338099465675499297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1287110234931908467998125 482666338099465675499297)
                ·
                  refine ⟨361999753574599256624473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482666338099465675499297 361999753574599256624473)
                  ·
                    rfl

theorem cell20_793116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 3, 2].length) (baseStart_793116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793116 prefixEnd_793116 := by exact prefixLift 793116
  have htrace : WordTrace (prefixWord ++ tailWord_793116) baseStart_793116 baseEnd_793116 := by
    simpa [prefixWord, tailWord_793116, baseEnd_793116] using wordTrace_append hprefix tailTrace_793116
  have hstable : (prefixWord ++ tailWord_793116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793116).length < 2 ^ (prefixWord ++ tailWord_793116).sum := by decide
  have hdescent : baseEnd_793116 < baseStart_793116 := by decide
  rcases family_descends (prefixWord ++ tailWord_793116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793192 : List Nat := [2, 1, 4, 3, 2, 1, 1, 4, 2]
def baseStart_793192 : Nat := 118140960795 + 793192 * 2 ^ 59
def prefixEnd_793192 : Nat := 4983230072969 + 3 ^ 40 * 793192 * 2
def baseEnd_793192 : Nat := 362034442045480770090829

theorem tailTrace_793192 : CollatzResearch.WordTrace tailWord_793192 prefixEnd_793192 362034442045480770090829 := by
  unfold tailWord_793192
  simp only [CollatzResearch.WordTrace]
  refine ⟨14465044471204162626838915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19286725961605550169118553 14465044471204162626838915)
  ·
    refine ⟨21697566706806243940258373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14465044471204162626838915 21697566706806243940258373)
    ·
      refine ⟨4068293757526170738798445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21697566706806243940258373 4068293757526170738798445)
      ·
        refine ⟨1525610159072314027049417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4068293757526170738798445 1525610159072314027049417)
        ·
          refine ⟨1144207619304235520287063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1525610159072314027049417 1144207619304235520287063)
          ·
            refine ⟨1716311428956353280430595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144207619304235520287063 1716311428956353280430595)
            ·
              refine ⟨2574467143434529920645893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1716311428956353280430595 2574467143434529920645893)
              ·
                refine ⟨482712589393974360121105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2574467143434529920645893 482712589393974360121105)
                ·
                  refine ⟨362034442045480770090829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482712589393974360121105 362034442045480770090829)
                  ·
                    rfl

theorem cell20_793192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 2].length) (baseStart_793192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793192 prefixEnd_793192 := by exact prefixLift 793192
  have htrace : WordTrace (prefixWord ++ tailWord_793192) baseStart_793192 baseEnd_793192 := by
    simpa [prefixWord, tailWord_793192, baseEnd_793192] using wordTrace_append hprefix tailTrace_793192
  have hstable : (prefixWord ++ tailWord_793192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793192).length < 2 ^ (prefixWord ++ tailWord_793192).sum := by decide
  have hdescent : baseEnd_793192 < baseStart_793192 := by decide
  rcases family_descends (prefixWord ++ tailWord_793192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793220 : List Nat := [2, 3, 2, 1, 3, 2, 3, 4]
def baseStart_793220 : Nat := 118140960795 + 793220 * 2 ^ 59
def prefixEnd_793220 : Nat := 4983230072969 + 3 ^ 40 * 793220 * 2
def baseEnd_793220 : Nat := 120682407336145705719127

theorem tailTrace_793220 : CollatzResearch.WordTrace tailWord_793220 prefixEnd_793220 120682407336145705719127 := by
  unfold tailWord_793220
  simp only [CollatzResearch.WordTrace]
  refine ⟨14465555093153443017848557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19287406790871257357131409 14465555093153443017848557)
  ·
    refine ⟨5424583159932541131693209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14465555093153443017848557 5424583159932541131693209)
    ·
      refine ⟨4068437369949405848769907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5424583159932541131693209 4068437369949405848769907)
      ·
        refine ⟨6102656054924108773154861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4068437369949405848769907 6102656054924108773154861)
        ·
          refine ⟨2288496020596540789933073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6102656054924108773154861 2288496020596540789933073)
          ·
            refine ⟨1716372015447405592449805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2288496020596540789933073 1716372015447405592449805)
            ·
              refine ⟨643639505792777097168677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1716372015447405592449805 643639505792777097168677)
              ·
                refine ⟨120682407336145705719127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 643639505792777097168677 120682407336145705719127)
                ·
                  rfl

theorem cell20_793220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_793220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793220 prefixEnd_793220 := by exact prefixLift 793220
  have htrace : WordTrace (prefixWord ++ tailWord_793220) baseStart_793220 baseEnd_793220 := by
    simpa [prefixWord, tailWord_793220, baseEnd_793220] using wordTrace_append hprefix tailTrace_793220
  have hstable : (prefixWord ++ tailWord_793220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793220).length < 2 ^ (prefixWord ++ tailWord_793220).sum := by decide
  have hdescent : baseEnd_793220 < baseStart_793220 := by decide
  rcases family_descends (prefixWord ++ tailWord_793220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793231 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 7]
def baseStart_793231 : Nat := 118140960795 + 793231 * 2 ^ 59
def prefixEnd_793231 : Nat := 4983230072969 + 3 ^ 40 * 793231 * 2
def baseEnd_793231 : Nat := 362052242708169967790669

theorem tailTrace_793231 : CollatzResearch.WordTrace tailWord_793231 prefixEnd_793231 362052242708169967790669 := by
  unfold tailWord_793231
  simp only [CollatzResearch.WordTrace]
  refine ⟨28931511389267034914347547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19287674259511356609565031 28931511389267034914347547)
  ·
    refine ⟨43397267083900552371521321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28931511389267034914347547 43397267083900552371521321)
    ·
      refine ⟨32547950312925414278640991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43397267083900552371521321 32547950312925414278640991)
      ·
        refine ⟨48821925469388121417961487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32547950312925414278640991 48821925469388121417961487)
        ·
          refine ⟨73232888204082182126942231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48821925469388121417961487 73232888204082182126942231)
          ·
            refine ⟨109849332306123273190413347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73232888204082182126942231 109849332306123273190413347)
            ·
              refine ⟨164773998459184909785620021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109849332306123273190413347 164773998459184909785620021)
              ·
                refine ⟨15447562355548585292401877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164773998459184909785620021 15447562355548585292401877)
                ·
                  refine ⟨362052242708169967790669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15447562355548585292401877 362052242708169967790669)
                  ·
                    rfl

theorem cell20_793231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_793231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793231 prefixEnd_793231 := by exact prefixLift 793231
  have htrace : WordTrace (prefixWord ++ tailWord_793231) baseStart_793231 baseEnd_793231 := by
    simpa [prefixWord, tailWord_793231, baseEnd_793231] using wordTrace_append hprefix tailTrace_793231
  have hstable : (prefixWord ++ tailWord_793231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793231).length < 2 ^ (prefixWord ++ tailWord_793231).sum := by decide
  have hdescent : baseEnd_793231 < baseStart_793231 := by decide
  rcases family_descends (prefixWord ++ tailWord_793231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793244 : List Nat := [2, 2, 3, 2, 2, 3, 1, 2, 3]
def baseStart_793244 : Nat := 118140960795 + 793244 * 2 ^ 59
def prefixEnd_793244 : Nat := 4983230072969 + 3 ^ 40 * 793244 * 2
def baseEnd_793244 : Nat := 362058176262399700357283

theorem tailTrace_793244 : CollatzResearch.WordTrace tailWord_793244 prefixEnd_793244 362058176262399700357283 := by
  unfold tailWord_793244
  simp only [CollatzResearch.WordTrace]
  refine ⟨14465992769109969067285393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19287990358813292089713857 14465992769109969067285393)
  ·
    refine ⟨10849494576832476800464045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14465992769109969067285393 10849494576832476800464045)
    ·
      refine ⟨4068560466312178800174017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10849494576832476800464045 4068560466312178800174017)
      ·
        refine ⟨3051420349734134100130513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4068560466312178800174017 3051420349734134100130513)
        ·
          refine ⟨2288565262300600575097885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3051420349734134100130513 2288565262300600575097885)
          ·
            refine ⟨858211973362725215661707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2288565262300600575097885 858211973362725215661707)
            ·
              refine ⟨1287317960044087823492561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858211973362725215661707 1287317960044087823492561)
              ·
                refine ⟨965488470033065867619421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1287317960044087823492561 965488470033065867619421)
                ·
                  refine ⟨362058176262399700357283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 965488470033065867619421 362058176262399700357283)
                  ·
                    rfl

theorem cell20_793244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_793244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793244 prefixEnd_793244 := by exact prefixLift 793244
  have htrace : WordTrace (prefixWord ++ tailWord_793244) baseStart_793244 baseEnd_793244 := by
    simpa [prefixWord, tailWord_793244, baseEnd_793244] using wordTrace_append hprefix tailTrace_793244
  have hstable : (prefixWord ++ tailWord_793244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793244).length < 2 ^ (prefixWord ++ tailWord_793244).sum := by decide
  have hdescent : baseEnd_793244 < baseStart_793244 := by decide
  rcases family_descends (prefixWord ++ tailWord_793244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793279 : List Nat := [1, 1, 2, 2, 2, 4, 4, 4]
def baseStart_793279 : Nat := 118140960795 + 793279 * 2 ^ 59
def prefixEnd_793279 : Nat := 4983230072969 + 3 ^ 40 * 793279 * 2
def baseEnd_793279 : Nat := 120691383738698378063491

theorem tailTrace_793279 : CollatzResearch.WordTrace tailWord_793279 prefixEnd_793279 120691383738698378063491 := by
  unfold tailWord_793279
  simp only [CollatzResearch.WordTrace]
  refine ⟨28933262093093139112094891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19288841395395426074729927 28933262093093139112094891)
  ·
    refine ⟨43399893139639708668142337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28933262093093139112094891 43399893139639708668142337)
    ·
      refine ⟨32549919854729781501106753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43399893139639708668142337 32549919854729781501106753)
      ·
        refine ⟨24412439891047336125830065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32549919854729781501106753 24412439891047336125830065)
        ·
          refine ⟨18309329918285502094372549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24412439891047336125830065 18309329918285502094372549)
          ·
            refine ⟨3432999359678531642694853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18309329918285502094372549 3432999359678531642694853)
            ·
              refine ⟨643687379939724683005285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3432999359678531642694853 643687379939724683005285)
              ·
                refine ⟨120691383738698378063491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 643687379939724683005285 120691383738698378063491)
                ·
                  rfl

theorem cell20_793279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 4, 4].length) (baseStart_793279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793279 prefixEnd_793279 := by exact prefixLift 793279
  have htrace : WordTrace (prefixWord ++ tailWord_793279) baseStart_793279 baseEnd_793279 := by
    simpa [prefixWord, tailWord_793279, baseEnd_793279] using wordTrace_append hprefix tailTrace_793279
  have hstable : (prefixWord ++ tailWord_793279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793279).length < 2 ^ (prefixWord ++ tailWord_793279).sum := by decide
  have hdescent : baseEnd_793279 < baseStart_793279 := by decide
  rcases family_descends (prefixWord ++ tailWord_793279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793317 : List Nat := [1, 3, 1, 4, 1, 3, 2, 5]
def baseStart_793317 : Nat := 118140960795 + 793317 * 2 ^ 59
def prefixEnd_793317 : Nat := 4983230072969 + 3 ^ 40 * 793317 * 2
def baseEnd_793317 : Nat := 120697165150511963641217

theorem tailTrace_793317 : CollatzResearch.WordTrace tailWord_793317 prefixEnd_793317 120697165150511963641217 := by
  unfold tailWord_793317
  simp only [CollatzResearch.WordTrace]
  refine ⟨28934648066955471601978205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19289765377970314401318803 28934648066955471601978205)
  ·
    refine ⟨10850493025108301850741827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28934648066955471601978205 10850493025108301850741827)
    ·
      refine ⟨16275739537662452776112741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10850493025108301850741827 16275739537662452776112741)
      ·
        refine ⟨3051701163311709895521139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16275739537662452776112741 3051701163311709895521139)
        ·
          refine ⟨4577551744967564843281709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3051701163311709895521139 4577551744967564843281709)
          ·
            refine ⟨1716581904362836816230641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4577551744967564843281709 1716581904362836816230641)
            ·
              refine ⟨1287436428272127612172981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1716581904362836816230641 1287436428272127612172981)
              ·
                refine ⟨120697165150511963641217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1287436428272127612172981 120697165150511963641217)
                ·
                  rfl

theorem cell20_793317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 5].length) (baseStart_793317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793317 prefixEnd_793317 := by exact prefixLift 793317
  have htrace : WordTrace (prefixWord ++ tailWord_793317) baseStart_793317 baseEnd_793317 := by
    simpa [prefixWord, tailWord_793317, baseEnd_793317] using wordTrace_append hprefix tailTrace_793317
  have hstable : (prefixWord ++ tailWord_793317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793317).length < 2 ^ (prefixWord ++ tailWord_793317).sum := by decide
  have hdescent : baseEnd_793317 < baseStart_793317 := by decide
  rcases family_descends (prefixWord ++ tailWord_793317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793338 : List Nat := [3, 1, 1, 1, 1, 3, 4, 6]
def baseStart_793338 : Nat := 118140960795 + 793338 * 2 ^ 59
def prefixEnd_793338 : Nat := 4983230072969 + 3 ^ 40 * 793338 * 2
def baseEnd_793338 : Nat := 120700360141251050407855

theorem tailTrace_793338 : CollatzResearch.WordTrace tailWord_793338 prefixEnd_793338 120700360141251050407855 := by
  unfold tailWord_793338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7233853499969848047123167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19290275999919594792328445 7233853499969848047123167)
  ·
    refine ⟨10850780249954772070684751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7233853499969848047123167 10850780249954772070684751)
    ·
      refine ⟨16276170374932158106027127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10850780249954772070684751 16276170374932158106027127)
      ·
        refine ⟨24414255562398237159040691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16276170374932158106027127 24414255562398237159040691)
        ·
          refine ⟨36621383343597355738561037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24414255562398237159040691 36621383343597355738561037)
          ·
            refine ⟨13733018753849008401960389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36621383343597355738561037 13733018753849008401960389)
            ·
              refine ⟨2574941016346689075367573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13733018753849008401960389 2574941016346689075367573)
              ·
                refine ⟨120700360141251050407855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2574941016346689075367573 120700360141251050407855)
                ·
                  rfl

theorem cell20_793338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_793338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793338 prefixEnd_793338 := by exact prefixLift 793338
  have htrace : WordTrace (prefixWord ++ tailWord_793338) baseStart_793338 baseEnd_793338 := by
    simpa [prefixWord, tailWord_793338, baseEnd_793338] using wordTrace_append hprefix tailTrace_793338
  have hstable : (prefixWord ++ tailWord_793338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793338).length < 2 ^ (prefixWord ++ tailWord_793338).sum := by decide
  have hdescent : baseEnd_793338 < baseStart_793338 := by decide
  rcases family_descends (prefixWord ++ tailWord_793338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793393 : List Nat := [1, 2, 2, 3, 2, 1, 5, 4]
def baseStart_793393 : Nat := 118140960795 + 793393 * 2 ^ 59
def prefixEnd_793393 : Nat := 4983230072969 + 3 ^ 40 * 793393 * 2
def baseEnd_793393 : Nat := 120708727974139134796669

theorem tailTrace_793393 : CollatzResearch.WordTrace tailWord_793393 prefixEnd_793393 120708727974139134796669 := by
  unfold tailWord_793393
  simp only [CollatzResearch.WordTrace]
  refine ⟨28937420014680136581744833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19291613343120091054496555 28937420014680136581744833)
  ·
    refine ⟨21703065011010102436308625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28937420014680136581744833 21703065011010102436308625)
    ·
      refine ⟨16277298758257576827231469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21703065011010102436308625 16277298758257576827231469)
      ·
        refine ⟨6103987034346591310211801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16277298758257576827231469 6103987034346591310211801)
        ·
          refine ⟨4577990275759943482658851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6103987034346591310211801 4577990275759943482658851)
          ·
            refine ⟨6866985413639915223988277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4577990275759943482658851 6866985413639915223988277)
            ·
              refine ⟨643779882528742052248901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6866985413639915223988277 643779882528742052248901)
              ·
                refine ⟨120708727974139134796669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 643779882528742052248901 120708727974139134796669)
                ·
                  rfl

theorem cell20_793393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 4].length) (baseStart_793393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793393 prefixEnd_793393 := by exact prefixLift 793393
  have htrace : WordTrace (prefixWord ++ tailWord_793393) baseStart_793393 baseEnd_793393 := by
    simpa [prefixWord, tailWord_793393, baseEnd_793393] using wordTrace_append hprefix tailTrace_793393
  have hstable : (prefixWord ++ tailWord_793393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793393).length < 2 ^ (prefixWord ++ tailWord_793393).sum := by decide
  have hdescent : baseEnd_793393 < baseStart_793393 := by decide
  rcases family_descends (prefixWord ++ tailWord_793393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793417 : List Nat := [1, 2, 1, 1, 2, 7, 1, 2, 3]
def baseStart_793417 : Nat := 118140960795 + 793417 * 2 ^ 59
def prefixEnd_793417 : Nat := 4983230072969 + 3 ^ 40 * 793417 * 2
def baseEnd_793417 : Nat := 362137138176379987589909

theorem tailTrace_793417 : CollatzResearch.WordTrace tailWord_793417 prefixEnd_793417 362137138176379987589909 := by
  unfold tailWord_793417
  simp only [CollatzResearch.WordTrace]
  refine ⟨28938295366593188680618505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19292196911062125787079003 28938295366593188680618505)
  ·
    refine ⟨21703721524944891510463879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28938295366593188680618505 21703721524944891510463879)
    ·
      refine ⟨32555582287417337265695819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21703721524944891510463879 32555582287417337265695819)
      ·
        refine ⟨48833373431126005898543729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32555582287417337265695819 48833373431126005898543729)
        ·
          refine ⟨36625030073344504423907797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48833373431126005898543729 36625030073344504423907797)
          ·
            refine ⟨858399142344011822435339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 36625030073344504423907797 858399142344011822435339)
            ·
              refine ⟨1287598713516017733653009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858399142344011822435339 1287598713516017733653009)
              ·
                refine ⟨965699035137013300239757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1287598713516017733653009 965699035137013300239757)
                ·
                  refine ⟨362137138176379987589909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 965699035137013300239757 362137138176379987589909)
                  ·
                    rfl

theorem cell20_793417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 3].length) (baseStart_793417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793417 prefixEnd_793417 := by exact prefixLift 793417
  have htrace : WordTrace (prefixWord ++ tailWord_793417) baseStart_793417 baseEnd_793417 := by
    simpa [prefixWord, tailWord_793417, baseEnd_793417] using wordTrace_append hprefix tailTrace_793417
  have hstable : (prefixWord ++ tailWord_793417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793417).length < 2 ^ (prefixWord ++ tailWord_793417).sum := by decide
  have hdescent : baseEnd_793417 < baseStart_793417 := by decide
  rcases family_descends (prefixWord ++ tailWord_793417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793424 : List Nat := [2, 1, 1, 1, 1, 4, 4, 4, 2]
def baseStart_793424 : Nat := 118140960795 + 793424 * 2 ^ 59
def prefixEnd_793424 : Nat := 4983230072969 + 3 ^ 40 * 793424 * 2
def baseEnd_793424 : Nat := 362140333167119074356547

theorem tailTrace_793424 : CollatzResearch.WordTrace tailWord_793424 prefixEnd_793424 362140333167119074356547 := by
  unfold tailWord_793424
  simp only [CollatzResearch.WordTrace]
  refine ⟨14469275338783914438061663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19292367118378552584082217 14469275338783914438061663)
  ·
    refine ⟨21703913008175871657092495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14469275338783914438061663 21703913008175871657092495)
    ·
      refine ⟨32555869512263807485638743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21703913008175871657092495 32555869512263807485638743)
      ·
        refine ⟨48833804268395711228458115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32555869512263807485638743 48833804268395711228458115)
        ·
          refine ⟨73250706402593566842687173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48833804268395711228458115 73250706402593566842687173)
          ·
            refine ⟨13734507450486293783003845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73250706402593566842687173 13734507450486293783003845)
            ·
              refine ⟨2575220146966180084313221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13734507450486293783003845 2575220146966180084313221)
              ·
                refine ⟨482853777556158765808729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2575220146966180084313221 482853777556158765808729)
                ·
                  refine ⟨362140333167119074356547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482853777556158765808729 362140333167119074356547)
                  ·
                    rfl

theorem cell20_793424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 4, 2].length) (baseStart_793424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793424 prefixEnd_793424 := by exact prefixLift 793424
  have htrace : WordTrace (prefixWord ++ tailWord_793424) baseStart_793424 baseEnd_793424 := by
    simpa [prefixWord, tailWord_793424, baseEnd_793424] using wordTrace_append hprefix tailTrace_793424
  have hstable : (prefixWord ++ tailWord_793424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793424).length < 2 ^ (prefixWord ++ tailWord_793424).sum := by decide
  have hdescent : baseEnd_793424 < baseStart_793424 := by decide
  rcases family_descends (prefixWord ++ tailWord_793424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793445 : List Nat := [1, 3, 1, 3, 1, 1, 4, 2, 4]
def baseStart_793445 : Nat := 118140960795 + 793445 * 2 ^ 59
def prefixEnd_793445 : Nat := 4983230072969 + 3 ^ 40 * 793445 * 2
def baseEnd_793445 : Nat := 362149918139336334656461

theorem tailTrace_793445 : CollatzResearch.WordTrace tailWord_793445 prefixEnd_793445 362149918139336334656461 := by
  unfold tailWord_793445
  simp only [CollatzResearch.WordTrace]
  refine ⟨28939316610491749462637789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19292877740327832975091859 28939316610491749462637789)
  ·
    refine ⟨10852243728934406048489171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28939316610491749462637789 10852243728934406048489171)
    ·
      refine ⟨16278365593401609072733757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10852243728934406048489171 16278365593401609072733757)
      ·
        refine ⟨6104387097525603402275159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16278365593401609072733757 6104387097525603402275159)
        ·
          refine ⟨9156580646288405103412739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6104387097525603402275159 9156580646288405103412739)
          ·
            refine ⟨13734870969432607655119109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9156580646288405103412739 13734870969432607655119109)
            ·
              refine ⟨2575288306768613935334833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13734870969432607655119109 2575288306768613935334833)
              ·
                refine ⟨1931466230076460451501125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2575288306768613935334833 1931466230076460451501125)
                ·
                  refine ⟨362149918139336334656461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1931466230076460451501125 362149918139336334656461)
                  ·
                    rfl

theorem cell20_793445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_793445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793445 prefixEnd_793445 := by exact prefixLift 793445
  have htrace : WordTrace (prefixWord ++ tailWord_793445) baseStart_793445 baseEnd_793445 := by
    simpa [prefixWord, tailWord_793445, baseEnd_793445] using wordTrace_append hprefix tailTrace_793445
  have hstable : (prefixWord ++ tailWord_793445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793445).length < 2 ^ (prefixWord ++ tailWord_793445).sum := by decide
  have hdescent : baseEnd_793445 < baseStart_793445 := by decide
  rcases family_descends (prefixWord ++ tailWord_793445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793448 : List Nat := [2, 1, 4, 2, 1, 4, 2, 4]
def baseStart_793448 : Nat := 118140960795 + 793448 * 2 ^ 59
def prefixEnd_793448 : Nat := 4983230072969 + 3 ^ 40 * 793448 * 2
def baseEnd_793448 : Nat := 120717095807027219185483

theorem tailTrace_793448 : CollatzResearch.WordTrace tailWord_793448 prefixEnd_793448 120717095807027219185483 := by
  unfold tailWord_793448
  simp only [CollatzResearch.WordTrace]
  refine ⟨14469713014740440487498499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19292950686320587316664665 14469713014740440487498499)
  ·
    refine ⟨21704569522110660731247749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14469713014740440487498499 21704569522110660731247749)
    ·
      refine ⟨4069606785395748887108953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21704569522110660731247749 4069606785395748887108953)
      ·
        refine ⟨3052205089046811665331715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4069606785395748887108953 3052205089046811665331715)
        ·
          refine ⟨4578307633570217497997573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3052205089046811665331715 4578307633570217497997573)
          ·
            refine ⟨858432681294415780874545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4578307633570217497997573 858432681294415780874545)
            ·
              refine ⟨643824510970811835655909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 858432681294415780874545 643824510970811835655909)
              ·
                refine ⟨120717095807027219185483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 643824510970811835655909 120717095807027219185483)
                ·
                  rfl

theorem cell20_793448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_793448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793448 prefixEnd_793448 := by exact prefixLift 793448
  have htrace : WordTrace (prefixWord ++ tailWord_793448) baseStart_793448 baseEnd_793448 := by
    simpa [prefixWord, tailWord_793448, baseEnd_793448] using wordTrace_append hprefix tailTrace_793448
  have hstable : (prefixWord ++ tailWord_793448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793448).length < 2 ^ (prefixWord ++ tailWord_793448).sum := by decide
  have hdescent : baseEnd_793448 < baseStart_793448 := by decide
  rcases family_descends (prefixWord ++ tailWord_793448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793452 : List Nat := [2, 2, 1, 1, 4, 1, 3, 6]
def baseStart_793452 : Nat := 118140960795 + 793452 * 2 ^ 59
def prefixEnd_793452 : Nat := 4983230072969 + 3 ^ 40 * 793452 * 2
def baseEnd_793452 : Nat := 120717704376691807141033

theorem tailTrace_793452 : CollatzResearch.WordTrace tailWord_793452 prefixEnd_793452 120717704376691807141033 := by
  unfold tailWord_793452
  simp only [CollatzResearch.WordTrace]
  refine ⟨14469785960733194829071305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19293047947644259772095073 14469785960733194829071305)
  ·
    refine ⟨10852339470549896121803479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14469785960733194829071305 10852339470549896121803479)
    ·
      refine ⟨16278509205824844182705219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10852339470549896121803479 16278509205824844182705219)
      ·
        refine ⟨24417763808737266274057829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16278509205824844182705219 24417763808737266274057829)
        ·
          refine ⟨4578330714138237426385843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24417763808737266274057829 4578330714138237426385843)
          ·
            refine ⟨6867496071207356139578765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4578330714138237426385843 6867496071207356139578765)
            ·
              refine ⟨2575311026702758552342037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6867496071207356139578765 2575311026702758552342037)
              ·
                refine ⟨120717704376691807141033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2575311026702758552342037 120717704376691807141033)
                ·
                  rfl

theorem cell20_793452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_793452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793452 prefixEnd_793452 := by exact prefixLift 793452
  have htrace : WordTrace (prefixWord ++ tailWord_793452) baseStart_793452 baseEnd_793452 := by
    simpa [prefixWord, tailWord_793452, baseEnd_793452] using wordTrace_append hprefix tailTrace_793452
  have hstable : (prefixWord ++ tailWord_793452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793452).length < 2 ^ (prefixWord ++ tailWord_793452).sum := by decide
  have hdescent : baseEnd_793452 < baseStart_793452 := by decide
  rcases family_descends (prefixWord ++ tailWord_793452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793459 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 5]
def baseStart_793459 : Nat := 118140960795 + 793459 * 2 ^ 59
def prefixEnd_793459 : Nat := 4983230072969 + 3 ^ 40 * 793459 * 2
def baseEnd_793459 : Nat := 362156308120814508189737

theorem tailTrace_793459 : CollatzResearch.WordTrace tailWord_793459 prefixEnd_793459 362156308120814508189737 := by
  unfold tailWord_793459
  simp only [CollatzResearch.WordTrace]
  refine ⟨28939827232441029853647431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19293218154960686569098287 28939827232441029853647431)
  ·
    refine ⟨43409740848661544780471147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28939827232441029853647431 43409740848661544780471147)
    ·
      refine ⟨65114611272992317170706721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43409740848661544780471147 65114611272992317170706721)
      ·
        refine ⟨48835958454744237878030041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65114611272992317170706721 48835958454744237878030041)
        ·
          refine ⟨36626968841058178408522531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48835958454744237878030041 36626968841058178408522531)
          ·
            refine ⟨54940453261587267612783797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36626968841058178408522531 54940453261587267612783797)
            ·
              refine ⟨5150667493273806338698481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54940453261587267612783797 5150667493273806338698481)
              ·
                refine ⟨3863000619955354754023861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5150667493273806338698481 3863000619955354754023861)
                ·
                  refine ⟨362156308120814508189737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3863000619955354754023861 362156308120814508189737)
                  ·
                    rfl

theorem cell20_793459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_793459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793459 prefixEnd_793459 := by exact prefixLift 793459
  have htrace : WordTrace (prefixWord ++ tailWord_793459) baseStart_793459 baseEnd_793459 := by
    simpa [prefixWord, tailWord_793459, baseEnd_793459] using wordTrace_append hprefix tailTrace_793459
  have hstable : (prefixWord ++ tailWord_793459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793459).length < 2 ^ (prefixWord ++ tailWord_793459).sum := by decide
  have hdescent : baseEnd_793459 < baseStart_793459 := by decide
  rcases family_descends (prefixWord ++ tailWord_793459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793476 : List Nat := [2, 3, 2, 1, 1, 1, 1, 6, 3]
def baseStart_793476 : Nat := 118140960795 + 793476 * 2 ^ 59
def prefixEnd_793476 : Nat := 4983230072969 + 3 ^ 40 * 793476 * 2
def baseEnd_793476 : Nat := 362164067384038004623001

theorem tailTrace_793476 : CollatzResearch.WordTrace tailWord_793476 prefixEnd_793476 362164067384038004623001 := by
  unfold tailWord_793476
  simp only [CollatzResearch.WordTrace]
  refine ⟨14470223636689720878508141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19293631515586294504677521 14470223636689720878508141)
  ·
    refine ⟨5426333863758645329440553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14470223636689720878508141 5426333863758645329440553)
    ·
      refine ⟨4069750397818983997080415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5426333863758645329440553 4069750397818983997080415)
      ·
        refine ⟨6104625596728475995620623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4069750397818983997080415 6104625596728475995620623)
        ·
          refine ⟨9156938395092713993430935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6104625596728475995620623 9156938395092713993430935)
          ·
            refine ⟨13735407592639070990146403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9156938395092713993430935 13735407592639070990146403)
            ·
              refine ⟨20603111388958606485219605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13735407592639070990146403 20603111388958606485219605)
              ·
                refine ⟨965770846357434678994669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20603111388958606485219605 965770846357434678994669)
                ·
                  refine ⟨362164067384038004623001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 965770846357434678994669 362164067384038004623001)
                  ·
                    rfl

theorem cell20_793476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_793476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793476 prefixEnd_793476 := by exact prefixLift 793476
  have htrace : WordTrace (prefixWord ++ tailWord_793476) baseStart_793476 baseEnd_793476 := by
    simpa [prefixWord, tailWord_793476, baseEnd_793476] using wordTrace_append hprefix tailTrace_793476
  have hstable : (prefixWord ++ tailWord_793476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793476).length < 2 ^ (prefixWord ++ tailWord_793476).sum := by decide
  have hdescent : baseEnd_793476 < baseStart_793476 := by decide
  rcases family_descends (prefixWord ++ tailWord_793476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793483 : List Nat := [1, 1, 1, 1, 4, 2, 5, 1, 4]
def baseStart_793483 : Nat := 118140960795 + 793483 * 2 ^ 59
def prefixEnd_793483 : Nat := 4983230072969 + 3 ^ 40 * 793483 * 2
def baseEnd_793483 : Nat := 362167262374777091389639

theorem tailTrace_793483 : CollatzResearch.WordTrace tailWord_793483 prefixEnd_793483 362167262374777091389639 := by
  unfold tailWord_793483
  simp only [CollatzResearch.WordTrace]
  refine ⟨28940702584354081952521103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19293801722902721301680735 28940702584354081952521103)
  ·
    refine ⟨43411053876531122928781655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28940702584354081952521103 43411053876531122928781655)
    ·
      refine ⟨65116580814796684393172483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43411053876531122928781655 65116580814796684393172483)
      ·
        refine ⟨97674871222195026589758725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65116580814796684393172483 97674871222195026589758725)
        ·
          refine ⟨18314038354161567485579761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97674871222195026589758725 18314038354161567485579761)
          ·
            refine ⟨13735528765621175614184821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18314038354161567485579761 13735528765621175614184821)
            ·
              refine ⟨1287705821776985213829827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13735528765621175614184821 1287705821776985213829827)
              ·
                refine ⟨1931558732665477820744741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287705821776985213829827 1931558732665477820744741)
                ·
                  refine ⟨362167262374777091389639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1931558732665477820744741 362167262374777091389639)
                  ·
                    rfl

theorem cell20_793483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 4].length) (baseStart_793483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793483 prefixEnd_793483 := by exact prefixLift 793483
  have htrace : WordTrace (prefixWord ++ tailWord_793483) baseStart_793483 baseEnd_793483 := by
    simpa [prefixWord, tailWord_793483, baseEnd_793483] using wordTrace_append hprefix tailTrace_793483
  have hstable : (prefixWord ++ tailWord_793483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793483).length < 2 ^ (prefixWord ++ tailWord_793483).sum := by decide
  have hdescent : baseEnd_793483 < baseStart_793483 := by decide
  rcases family_descends (prefixWord ++ tailWord_793483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793493 : List Nat := [1, 3, 2, 1, 1, 4, 4, 1, 3]
def baseStart_793493 : Nat := 118140960795 + 793493 * 2 ^ 59
def prefixEnd_793493 : Nat := 4983230072969 + 3 ^ 40 * 793493 * 2
def baseEnd_793493 : Nat := 362171826647261501056265

theorem tailTrace_793493 : CollatzResearch.WordTrace tailWord_793493 prefixEnd_793493 362171826647261501056265 := by
  unfold tailWord_793493
  simp only [CollatzResearch.WordTrace]
  refine ⟨28941067314317853660385133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19294044876211902440256755 28941067314317853660385133)
  ·
    refine ⟨10852900242869195122644425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28941067314317853660385133 10852900242869195122644425)
    ·
      refine ⟨8139675182151896341983319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10852900242869195122644425 8139675182151896341983319)
      ·
        refine ⟨12209512773227844512974979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8139675182151896341983319 12209512773227844512974979)
        ·
          refine ⟨18314269159841766769462469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12209512773227844512974979 18314269159841766769462469)
          ·
            refine ⟨3433925467470331269274213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18314269159841766769462469 3433925467470331269274213)
            ·
              refine ⟨643861025150687112988915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3433925467470331269274213 643861025150687112988915)
              ·
                refine ⟨965791537726030669483373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643861025150687112988915 965791537726030669483373)
                ·
                  refine ⟨362171826647261501056265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 965791537726030669483373 362171826647261501056265)
                  ·
                    rfl

theorem cell20_793493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_793493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793493 prefixEnd_793493 := by exact prefixLift 793493
  have htrace : WordTrace (prefixWord ++ tailWord_793493) baseStart_793493 baseEnd_793493 := by
    simpa [prefixWord, tailWord_793493, baseEnd_793493] using wordTrace_append hprefix tailTrace_793493
  have hstable : (prefixWord ++ tailWord_793493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793493).length < 2 ^ (prefixWord ++ tailWord_793493).sum := by decide
  have hdescent : baseEnd_793493 < baseStart_793493 := by decide
  rcases family_descends (prefixWord ++ tailWord_793493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793526 : List Nat := [5, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_793526 : Nat := 118140960795 + 793526 * 2 ^ 59
def prefixEnd_793526 : Nat := 4983230072969 + 3 ^ 40 * 793526 * 2
def baseEnd_793526 : Nat := 362186888746460052956131

theorem tailTrace_793526 : CollatzResearch.WordTrace tailWord_793526 prefixEnd_793526 362186888746460052956131 := by
  unfold tailWord_793526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1808891932699893768521027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19294847282132200197557621 1808891932699893768521027)
  ·
    refine ⟨2713337899049840652781541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1808891932699893768521027 2713337899049840652781541)
    ·
      refine ⟨508750856071845122396539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2713337899049840652781541 508750856071845122396539)
      ·
        refine ⟨763126284107767683594809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508750856071845122396539 763126284107767683594809)
        ·
          refine ⟨572344713080825762696107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 763126284107767683594809 572344713080825762696107)
          ·
            refine ⟨858517069621238644044161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572344713080825762696107 858517069621238644044161)
            ·
              refine ⟨643887802215928983033121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 858517069621238644044161 643887802215928983033121)
              ·
                refine ⟨482915851661946737274841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 643887802215928983033121 482915851661946737274841)
                ·
                  refine ⟨362186888746460052956131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482915851661946737274841 362186888746460052956131)
                  ·
                    rfl

theorem cell20_793526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_793526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793526 prefixEnd_793526 := by exact prefixLift 793526
  have htrace : WordTrace (prefixWord ++ tailWord_793526) baseStart_793526 baseEnd_793526 := by
    simpa [prefixWord, tailWord_793526, baseEnd_793526] using wordTrace_append hprefix tailTrace_793526
  have hstable : (prefixWord ++ tailWord_793526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793526).length < 2 ^ (prefixWord ++ tailWord_793526).sum := by decide
  have hdescent : baseEnd_793526 < baseStart_793526 := by decide
  rcases family_descends (prefixWord ++ tailWord_793526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793576 : List Nat := [2, 1, 4, 1, 1, 1, 3, 5, 2]
def baseStart_793576 : Nat := 118140960795 + 793576 * 2 ^ 59
def prefixEnd_793576 : Nat := 4983230072969 + 3 ^ 40 * 793576 * 2
def baseEnd_793576 : Nat := 362209710108882101289259

theorem tailTrace_793576 : CollatzResearch.WordTrace tailWord_793576 prefixEnd_793576 362209710108882101289259 := by
  unfold tailWord_793576
  simp only [CollatzResearch.WordTrace]
  refine ⟨14472047286508579417828291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19296063048678105890437721 14472047286508579417828291)
  ·
    refine ⟨21708070929762869126742437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14472047286508579417828291 21708070929762869126742437)
    ·
      refine ⟨4070263299330537961264207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21708070929762869126742437 4070263299330537961264207)
      ·
        refine ⟨6105394948995806941896311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4070263299330537961264207 6105394948995806941896311)
        ·
          refine ⟨9158092423493710412844467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6105394948995806941896311 9158092423493710412844467)
          ·
            refine ⟨13737138635240565619266701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9158092423493710412844467 13737138635240565619266701)
            ·
              refine ⟨5151426988215212107225013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13737138635240565619266701 5151426988215212107225013)
              ·
                refine ⟨482946280145176135052345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5151426988215212107225013 482946280145176135052345)
                ·
                  refine ⟨362209710108882101289259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482946280145176135052345 362209710108882101289259)
                  ·
                    rfl

theorem cell20_793576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 2].length) (baseStart_793576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793576 prefixEnd_793576 := by exact prefixLift 793576
  have htrace : WordTrace (prefixWord ++ tailWord_793576) baseStart_793576 baseEnd_793576 := by
    simpa [prefixWord, tailWord_793576, baseEnd_793576] using wordTrace_append hprefix tailTrace_793576
  have hstable : (prefixWord ++ tailWord_793576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793576).length < 2 ^ (prefixWord ++ tailWord_793576).sum := by decide
  have hdescent : baseEnd_793576 < baseStart_793576 := by decide
  rcases family_descends (prefixWord ++ tailWord_793576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793607 : List Nat := [1, 1, 4, 3, 1, 1, 5, 1, 3]
def baseStart_793607 : Nat := 118140960795 + 793607 * 2 ^ 59
def prefixEnd_793607 : Nat := 4983230072969 + 3 ^ 40 * 793607 * 2
def baseEnd_793607 : Nat := 362223859353583771255799

theorem tailTrace_793607 : CollatzResearch.WordTrace tailWord_793607 prefixEnd_793607 362223859353583771255799 := by
  unfold tailWord_793607
  simp only [CollatzResearch.WordTrace]
  refine ⟨28945225235904851130035075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19296816823936567420023383 28945225235904851130035075)
  ·
    refine ⟨43417837853857276695052613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28945225235904851130035075 43417837853857276695052613)
    ·
      refine ⟨8140844597598239380322365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43417837853857276695052613 8140844597598239380322365)
      ·
        refine ⟨3052816724099339767620887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8140844597598239380322365 3052816724099339767620887)
        ·
          refine ⟨4579225086149009651431331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3052816724099339767620887 4579225086149009651431331)
          ·
            refine ⟨6868837629223514477146997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4579225086149009651431331 6868837629223514477146997)
            ·
              refine ⟨643953527739704482232531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6868837629223514477146997 643953527739704482232531)
              ·
                refine ⟨965930291609556723348797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643953527739704482232531 965930291609556723348797)
                ·
                  refine ⟨362223859353583771255799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 965930291609556723348797 362223859353583771255799)
                  ·
                    rfl

theorem cell20_793607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 3].length) (baseStart_793607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793607 prefixEnd_793607 := by exact prefixLift 793607
  have htrace : WordTrace (prefixWord ++ tailWord_793607) baseStart_793607 baseEnd_793607 := by
    simpa [prefixWord, tailWord_793607, baseEnd_793607] using wordTrace_append hprefix tailTrace_793607
  have hstable : (prefixWord ++ tailWord_793607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793607).length < 2 ^ (prefixWord ++ tailWord_793607).sum := by decide
  have hdescent : baseEnd_793607 < baseStart_793607 := by decide
  rcases family_descends (prefixWord ++ tailWord_793607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793621 : List Nat := [1, 3, 2, 1, 4, 1, 4, 4]
def baseStart_793621 : Nat := 118140960795 + 793621 * 2 ^ 59
def prefixEnd_793621 : Nat := 4983230072969 + 3 ^ 40 * 793621 * 2
def baseEnd_793621 : Nat := 120743416445020648263025

theorem tailTrace_793621 : CollatzResearch.WordTrace tailWord_793621 prefixEnd_793621 120743416445020648263025 := by
  unfold tailWord_793621
  simp only [CollatzResearch.WordTrace]
  refine ⟨28945735857854131521044717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19297157238569421014029811 28945735857854131521044717)
  ·
    refine ⟨10854650946695299320391769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28945735857854131521044717 10854650946695299320391769)
    ·
      refine ⟨8140988210021474490293827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10854650946695299320391769 8140988210021474490293827)
      ·
        refine ⟨12211482315032211735440741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8140988210021474490293827 12211482315032211735440741)
        ·
          refine ⟨2289652934068539700395139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12211482315032211735440741 2289652934068539700395139)
          ·
            refine ⟨3434479401102809550592709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2289652934068539700395139 3434479401102809550592709)
            ·
              refine ⟨643964887706776790736133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3434479401102809550592709 643964887706776790736133)
              ·
                refine ⟨120743416445020648263025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 643964887706776790736133 120743416445020648263025)
                ·
                  rfl

theorem cell20_793621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 4].length) (baseStart_793621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793621 prefixEnd_793621 := by exact prefixLift 793621
  have htrace : WordTrace (prefixWord ++ tailWord_793621) baseStart_793621 baseEnd_793621 := by
    simpa [prefixWord, tailWord_793621, baseEnd_793621] using wordTrace_append hprefix tailTrace_793621
  have hstable : (prefixWord ++ tailWord_793621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793621).length < 2 ^ (prefixWord ++ tailWord_793621).sum := by decide
  have hdescent : baseEnd_793621 < baseStart_793621 := by decide
  rcases family_descends (prefixWord ++ tailWord_793621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793631 : List Nat := [1, 1, 2, 4, 1, 5, 1, 3, 2]
def baseStart_793631 : Nat := 118140960795 + 793631 * 2 ^ 59
def prefixEnd_793631 : Nat := 4983230072969 + 3 ^ 40 * 793631 * 2
def baseEnd_793631 : Nat := 362234813607546354455701

theorem tailTrace_793631 : CollatzResearch.WordTrace tailWord_793631 prefixEnd_793631 362234813607546354455701 := by
  unfold tailWord_793631
  simp only [CollatzResearch.WordTrace]
  refine ⟨28946100587817903228908747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19297400391878602152605831 28946100587817903228908747)
  ·
    refine ⟨43419150881726854843363121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28946100587817903228908747 43419150881726854843363121)
    ·
      refine ⟨32564363161295141132522341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43419150881726854843363121 32564363161295141132522341)
      ·
        refine ⟨6105818092742838962347939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32564363161295141132522341 6105818092742838962347939)
        ·
          refine ⟨9158727139114258443521909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6105818092742838962347939 9158727139114258443521909)
          ·
            refine ⟨858630669291961729080179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9158727139114258443521909 858630669291961729080179)
            ·
              refine ⟨1287946003937942593620269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858630669291961729080179 1287946003937942593620269)
              ·
                refine ⟨482979751476728472607601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1287946003937942593620269 482979751476728472607601)
                ·
                  refine ⟨362234813607546354455701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 482979751476728472607601 362234813607546354455701)
                  ·
                    rfl

theorem cell20_793631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 2].length) (baseStart_793631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793631 prefixEnd_793631 := by exact prefixLift 793631
  have htrace : WordTrace (prefixWord ++ tailWord_793631) baseStart_793631 baseEnd_793631 := by
    simpa [prefixWord, tailWord_793631, baseEnd_793631] using wordTrace_append hprefix tailTrace_793631
  have hstable : (prefixWord ++ tailWord_793631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793631).length < 2 ^ (prefixWord ++ tailWord_793631).sum := by decide
  have hdescent : baseEnd_793631 < baseStart_793631 := by decide
  rcases family_descends (prefixWord ++ tailWord_793631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793649 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 5]
def baseStart_793649 : Nat := 118140960795 + 793649 * 2 ^ 59
def prefixEnd_793649 : Nat := 4983230072969 + 3 ^ 40 * 793649 * 2
def baseEnd_793649 : Nat := 362243029298018291855627

theorem tailTrace_793649 : CollatzResearch.WordTrace tailWord_793649 prefixEnd_793649 362243029298018291855627 := by
  unfold tailWord_793649
  simp only [CollatzResearch.WordTrace]
  refine ⟨28946757101752692303064001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19297838067835128202042667 28946757101752692303064001)
  ·
    refine ⟨21710067826314519227298001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28946757101752692303064001 21710067826314519227298001)
    ·
      refine ⟨16282550869735889420473501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21710067826314519227298001 16282550869735889420473501)
      ·
        refine ⟨6105956576150958532677563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16282550869735889420473501 6105956576150958532677563)
        ·
          refine ⟨9158934864226437799016345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6105956576150958532677563 9158934864226437799016345)
          ·
            refine ⟨6869201148169828349262259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9158934864226437799016345 6869201148169828349262259)
            ·
              refine ⟨10303801722254742523893389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6869201148169828349262259 10303801722254742523893389)
              ·
                refine ⟨3863925645845528446460021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10303801722254742523893389 3863925645845528446460021)
                ·
                  refine ⟨362243029298018291855627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3863925645845528446460021 362243029298018291855627)
                  ·
                    rfl

theorem cell20_793649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_793649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793649 prefixEnd_793649 := by exact prefixLift 793649
  have htrace : WordTrace (prefixWord ++ tailWord_793649) baseStart_793649 baseEnd_793649 := by
    simpa [prefixWord, tailWord_793649, baseEnd_793649] using wordTrace_append hprefix tailTrace_793649
  have hstable : (prefixWord ++ tailWord_793649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793649).length < 2 ^ (prefixWord ++ tailWord_793649).sum := by decide
  have hdescent : baseEnd_793649 < baseStart_793649 := by decide
  rcases family_descends (prefixWord ++ tailWord_793649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793662 : List Nat := [4, 2, 1, 3, 1, 1, 4, 1, 3]
def baseStart_793662 : Nat := 118140960795 + 793662 * 2 ^ 59
def prefixEnd_793662 : Nat := 4983230072969 + 3 ^ 40 * 793662 * 2
def baseEnd_793662 : Nat := 362248962852248024422241

theorem tailTrace_793662 : CollatzResearch.WordTrace tailWord_793662 prefixEnd_793662 362248962852248024422241 := by
  unfold tailWord_793662
  simp only [CollatzResearch.WordTrace]
  refine ⟨3618403906338199440410905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19298154167137063682191493 3618403906338199440410905)
  ·
    refine ⟨2713802929753649580308179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3618403906338199440410905 2713802929753649580308179)
    ·
      refine ⟨4070704394630474370462269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2713802929753649580308179 4070704394630474370462269)
      ·
        refine ⟨1526514147986427888923351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4070704394630474370462269 1526514147986427888923351)
        ·
          refine ⟨2289771221979641833385027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1526514147986427888923351 2289771221979641833385027)
          ·
            refine ⟨3434656832969462750077541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2289771221979641833385027 3434656832969462750077541)
            ·
              refine ⟨643998156181774265639539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3434656832969462750077541 643998156181774265639539)
              ·
                refine ⟨965997234272661398459309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643998156181774265639539 965997234272661398459309)
                ·
                  refine ⟨362248962852248024422241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 965997234272661398459309 362248962852248024422241)
                  ·
                    rfl

theorem cell20_793662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_793662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793662 prefixEnd_793662 := by exact prefixLift 793662
  have htrace : WordTrace (prefixWord ++ tailWord_793662) baseStart_793662 baseEnd_793662 := by
    simpa [prefixWord, tailWord_793662, baseEnd_793662] using wordTrace_append hprefix tailTrace_793662
  have hstable : (prefixWord ++ tailWord_793662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793662).length < 2 ^ (prefixWord ++ tailWord_793662).sum := by decide
  have hdescent : baseEnd_793662 < baseStart_793662 := by decide
  rcases family_descends (prefixWord ++ tailWord_793662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793739 : List Nat := [1, 1, 1, 1, 4, 1, 1, 10]
def baseStart_793739 : Nat := 118140960795 + 793739 * 2 ^ 59
def prefixEnd_793739 : Nat := 4983230072969 + 3 ^ 40 * 793739 * 2
def baseEnd_793739 : Nat := 120761369250125992951753

theorem tailTrace_793739 : CollatzResearch.WordTrace tailWord_793739 prefixEnd_793739 120761369250125992951753 := by
  unfold tailWord_793739
  simp only [CollatzResearch.WordTrace]
  refine ⟨28950039671426637673840271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19300026447617758449226847 28950039671426637673840271)
  ·
    refine ⟨43425059507139956510760407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28950039671426637673840271 43425059507139956510760407)
    ·
      refine ⟨65137589260709934766140611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43425059507139956510760407 65137589260709934766140611)
      ·
        refine ⟨97706383891064902149210917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65137589260709934766140611 97706383891064902149210917)
        ·
          refine ⟨18319946979574669152977047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97706383891064902149210917 18319946979574669152977047)
          ·
            refine ⟨27479920469362003729465571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18319946979574669152977047 27479920469362003729465571)
            ·
              refine ⟨41219880704043005594198357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27479920469362003729465571 41219880704043005594198357)
              ·
                refine ⟨120761369250125992951753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 41219880704043005594198357 120761369250125992951753)
                ·
                  rfl

theorem cell20_793739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 10].length) (baseStart_793739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793739 prefixEnd_793739 := by exact prefixLift 793739
  have htrace : WordTrace (prefixWord ++ tailWord_793739) baseStart_793739 baseEnd_793739 := by
    simpa [prefixWord, tailWord_793739, baseEnd_793739] using wordTrace_append hprefix tailTrace_793739
  have hstable : (prefixWord ++ tailWord_793739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793739).length < 2 ^ (prefixWord ++ tailWord_793739).sum := by decide
  have hdescent : baseEnd_793739 < baseStart_793739 := by decide
  rcases family_descends (prefixWord ++ tailWord_793739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793756 : List Nat := [2, 2, 3, 2, 1, 3, 7]
def baseStart_793756 : Nat := 118140960795 + 793756 * 2 ^ 59
def prefixEnd_793756 : Nat := 4983230072969 + 3 ^ 40 * 793756 * 2
def baseEnd_793756 : Nat := 40254651890400163920947

theorem tailTrace_793756 : CollatzResearch.WordTrace tailWord_793756 prefixEnd_793756 40254651890400163920947 := by
  unfold tailWord_793756
  simp only [CollatzResearch.WordTrace]
  refine ⟨14475329856182524788604561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19300439808243366384806081 14475329856182524788604561)
  ·
    refine ⟨10856497392136893591453421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14475329856182524788604561 10856497392136893591453421)
    ·
      refine ⟨4071186522051335096795033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10856497392136893591453421 4071186522051335096795033)
      ·
        refine ⟨3053389891538501322596275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4071186522051335096795033 3053389891538501322596275)
        ·
          refine ⟨4580084837307751983894413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3053389891538501322596275 4580084837307751983894413)
          ·
            refine ⟨1717531813990406993960405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4580084837307751983894413 1717531813990406993960405)
            ·
              refine ⟨40254651890400163920947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1717531813990406993960405 40254651890400163920947)
              ·
                rfl

theorem cell20_793756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 7].length) (baseStart_793756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793756 prefixEnd_793756 := by exact prefixLift 793756
  have htrace : WordTrace (prefixWord ++ tailWord_793756) baseStart_793756 baseEnd_793756 := by
    simpa [prefixWord, tailWord_793756, baseEnd_793756] using wordTrace_append hprefix tailTrace_793756
  have hstable : (prefixWord ++ tailWord_793756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793756).length < 2 ^ (prefixWord ++ tailWord_793756).sum := by decide
  have hdescent : baseEnd_793756 < baseStart_793756 := by decide
  rcases family_descends (prefixWord ++ tailWord_793756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793790 : List Nat := [4, 2, 1, 1, 3, 3, 2, 4]
def baseStart_793790 : Nat := 118140960795 + 793790 * 2 ^ 59
def prefixEnd_793790 : Nat := 4983230072969 + 3 ^ 40 * 793790 * 2
def baseEnd_793790 : Nat := 120769128513349489385017

theorem tailTrace_793790 : CollatzResearch.WordTrace tailWord_793790 prefixEnd_793790 120769128513349489385017 := by
  unfold tailWord_793790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3618987474280234172993353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19301266529494582255964549 3618987474280234172993353)
  ·
    refine ⟨2714240605710175629745015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3618987474280234172993353 2714240605710175629745015)
    ·
      refine ⟨4071360908565263444617523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2714240605710175629745015 4071360908565263444617523)
      ·
        refine ⟨6107041362847895166926285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4071360908565263444617523 6107041362847895166926285)
        ·
          refine ⟨2290140511067960687597357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6107041362847895166926285 2290140511067960687597357)
          ·
            refine ⟨858802691650485257849009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2290140511067960687597357 858802691650485257849009)
            ·
              refine ⟨644102018737863943386757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 858802691650485257849009 644102018737863943386757)
              ·
                refine ⟨120769128513349489385017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 644102018737863943386757 120769128513349489385017)
                ·
                  rfl

theorem cell20_793790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_793790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793790 prefixEnd_793790 := by exact prefixLift 793790
  have htrace : WordTrace (prefixWord ++ tailWord_793790) baseStart_793790 baseEnd_793790 := by
    simpa [prefixWord, tailWord_793790, baseEnd_793790] using wordTrace_append hprefix tailTrace_793790
  have hstable : (prefixWord ++ tailWord_793790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793790).length < 2 ^ (prefixWord ++ tailWord_793790).sum := by decide
  have hdescent : baseEnd_793790 < baseStart_793790 := by decide
  rcases family_descends (prefixWord ++ tailWord_793790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793815 : List Nat := [1, 1, 3, 2, 1, 2, 10]
def baseStart_793815 : Nat := 118140960795 + 793815 * 2 ^ 59
def prefixEnd_793815 : Nat := 4983230072969 + 3 ^ 40 * 793815 * 2
def baseEnd_793815 : Nat := 40257644024584388035735

theorem tailTrace_793815 : CollatzResearch.WordTrace tailWord_793815 prefixEnd_793815 40257644024584388035735 := by
  unfold tailWord_793815
  simp only [CollatzResearch.WordTrace]
  refine ⟨28952811619151302653606899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19301874412767535102404599 28952811619151302653606899)
  ·
    refine ⟨43429217428726953980410349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28952811619151302653606899 43429217428726953980410349)
    ·
      refine ⟨16285956535772607742653881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43429217428726953980410349 16285956535772607742653881)
      ·
        refine ⟨12214467401829455806990411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16285956535772607742653881 12214467401829455806990411)
        ·
          refine ⟨18321701102744183710485617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12214467401829455806990411 18321701102744183710485617)
          ·
            refine ⟨13741275827058137782864213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18321701102744183710485617 13741275827058137782864213)
            ·
              refine ⟨40257644024584388035735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13741275827058137782864213 40257644024584388035735)
              ·
                rfl

theorem cell20_793815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 10].length) (baseStart_793815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793815 prefixEnd_793815 := by exact prefixLift 793815
  have htrace : WordTrace (prefixWord ++ tailWord_793815) baseStart_793815 baseEnd_793815 := by
    simpa [prefixWord, tailWord_793815, baseEnd_793815] using wordTrace_append hprefix tailTrace_793815
  have hstable : (prefixWord ++ tailWord_793815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793815).length < 2 ^ (prefixWord ++ tailWord_793815).sum := by decide
  have hdescent : baseEnd_793815 < baseStart_793815 := by decide
  rcases family_descends (prefixWord ++ tailWord_793815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793821 : List Nat := [1, 4, 3, 2, 2, 2, 1, 1, 4]
def baseStart_793821 : Nat := 118140960795 + 793821 * 2 ^ 59
def prefixEnd_793821 : Nat := 4983230072969 + 3 ^ 40 * 793821 * 2
def baseEnd_793821 : Nat := 362321534784750138121591

theorem tailTrace_793821 : CollatzResearch.WordTrace tailWord_793821 prefixEnd_793821 362321534784750138121591 := by
  unfold tailWord_793821
  simp only [CollatzResearch.WordTrace]
  refine ⟨28953030457129565678325317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19302020304753043785550211 28953030457129565678325317)
  ·
    refine ⟨5428693210711793564685997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28953030457129565678325317 5428693210711793564685997)
    ·
      refine ⟨2035759954016922586757249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5428693210711793564685997 2035759954016922586757249)
      ·
        refine ⟨1526819965512691940067937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2035759954016922586757249 1526819965512691940067937)
        ·
          refine ⟨1145114974134518955050953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1526819965512691940067937 1145114974134518955050953)
          ·
            refine ⟨858836230600889216288215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1145114974134518955050953 858836230600889216288215)
            ·
              refine ⟨1288254345901333824432323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858836230600889216288215 1288254345901333824432323)
              ·
                refine ⟨1932381518852000736648485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1288254345901333824432323 1932381518852000736648485)
                ·
                  refine ⟨362321534784750138121591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1932381518852000736648485 362321534784750138121591)
                  ·
                    rfl

theorem cell20_793821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_793821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793821 prefixEnd_793821 := by exact prefixLift 793821
  have htrace : WordTrace (prefixWord ++ tailWord_793821) baseStart_793821 baseEnd_793821 := by
    simpa [prefixWord, tailWord_793821, baseEnd_793821] using wordTrace_append hprefix tailTrace_793821
  have hstable : (prefixWord ++ tailWord_793821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793821).length < 2 ^ (prefixWord ++ tailWord_793821).sum := by decide
  have hdescent : baseEnd_793821 < baseStart_793821 := by decide
  rcases family_descends (prefixWord ++ tailWord_793821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793825 : List Nat := [1, 2, 3, 1, 3, 2, 3, 1, 4]
def baseStart_793825 : Nat := 118140960795 + 793825 * 2 ^ 59
def prefixEnd_793825 : Nat := 4983230072969 + 3 ^ 40 * 793825 * 2
def baseEnd_793825 : Nat := 362323360493743901988241

theorem tailTrace_793825 : CollatzResearch.WordTrace tailWord_793825 prefixEnd_793825 362323360493743901988241 := by
  unfold tailWord_793825
  simp only [CollatzResearch.WordTrace]
  refine ⟨28953176349115074361470929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19302117566076716240980619 28953176349115074361470929)
  ·
    refine ⟨21714882261836305771103197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28953176349115074361470929 21714882261836305771103197)
    ·
      refine ⟨8143080848188614664163699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21714882261836305771103197 8143080848188614664163699)
      ·
        refine ⟨12214621272282921996245549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8143080848188614664163699 12214621272282921996245549)
        ·
          refine ⟨4580482977106095748592081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12214621272282921996245549 4580482977106095748592081)
          ·
            refine ⟨3435362232829571811444061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4580482977106095748592081 3435362232829571811444061)
            ·
              refine ⟨1288260837311089429291523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3435362232829571811444061 1288260837311089429291523)
              ·
                refine ⟨1932391255966634143937285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1288260837311089429291523 1932391255966634143937285)
                ·
                  refine ⟨362323360493743901988241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1932391255966634143937285 362323360493743901988241)
                  ·
                    rfl

theorem cell20_793825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_793825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793825 prefixEnd_793825 := by exact prefixLift 793825
  have htrace : WordTrace (prefixWord ++ tailWord_793825) baseStart_793825 baseEnd_793825 := by
    simpa [prefixWord, tailWord_793825, baseEnd_793825] using wordTrace_append hprefix tailTrace_793825
  have hstable : (prefixWord ++ tailWord_793825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793825).length < 2 ^ (prefixWord ++ tailWord_793825).sum := by decide
  have hdescent : baseEnd_793825 < baseStart_793825 := by decide
  rcases family_descends (prefixWord ++ tailWord_793825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793831 : List Nat := [1, 1, 5, 3, 3, 1, 2, 1, 3]
def baseStart_793831 : Nat := 118140960795 + 793831 * 2 ^ 59
def prefixEnd_793831 : Nat := 4983230072969 + 3 ^ 40 * 793831 * 2
def baseEnd_793831 : Nat := 362326099057234547788217

theorem tailTrace_793831 : CollatzResearch.WordTrace tailWord_793831 prefixEnd_793831 362326099057234547788217 := by
  unfold tailWord_793831
  simp only [CollatzResearch.WordTrace]
  refine ⟨28953395187093337386189347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19302263458062224924126231 28953395187093337386189347)
  ·
    refine ⟨43430092780640006079284021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28953395187093337386189347 43430092780640006079284021)
    ·
      refine ⟨4071571198185000569932877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43430092780640006079284021 4071571198185000569932877)
      ·
        refine ⟨1526839199319375213724829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4071571198185000569932877 1526839199319375213724829)
        ·
          refine ⟨572564699744765705146811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1526839199319375213724829 572564699744765705146811)
          ·
            refine ⟨858847049617148557720217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572564699744765705146811 858847049617148557720217)
            ·
              refine ⟨644135287212861418290163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 858847049617148557720217 644135287212861418290163)
              ·
                refine ⟨966202930819292127435245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644135287212861418290163 966202930819292127435245)
                ·
                  refine ⟨362326099057234547788217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 966202930819292127435245 362326099057234547788217)
                  ·
                    rfl

theorem cell20_793831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 1, 3].length) (baseStart_793831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793831 prefixEnd_793831 := by exact prefixLift 793831
  have htrace : WordTrace (prefixWord ++ tailWord_793831) baseStart_793831 baseEnd_793831 := by
    simpa [prefixWord, tailWord_793831, baseEnd_793831] using wordTrace_append hprefix tailTrace_793831
  have hstable : (prefixWord ++ tailWord_793831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793831).length < 2 ^ (prefixWord ++ tailWord_793831).sum := by decide
  have hdescent : baseEnd_793831 < baseStart_793831 := by decide
  rcases family_descends (prefixWord ++ tailWord_793831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793832 : List Nat := [2, 1, 4, 1, 2, 1, 4, 5]
def baseStart_793832 : Nat := 118140960795 + 793832 * 2 ^ 59
def prefixEnd_793832 : Nat := 4983230072969 + 3 ^ 40 * 793832 * 2
def baseEnd_793832 : Nat := 120775518494827662918293

theorem tailTrace_793832 : CollatzResearch.WordTrace tailWord_793832 prefixEnd_793832 120775518494827662918293 := by
  unfold tailWord_793832
  simp only [CollatzResearch.WordTrace]
  refine ⟨14476715830044857278487875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19302287773393143037983833 14476715830044857278487875)
  ·
    refine ⟨21715073745067285917731813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14476715830044857278487875 21715073745067285917731813)
    ·
      refine ⟨4071576327200116109574715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21715073745067285917731813 4071576327200116109574715)
      ·
        refine ⟨6107364490800174164362073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4071576327200116109574715 6107364490800174164362073)
        ·
          refine ⟨4580523368100130623271555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6107364490800174164362073 4580523368100130623271555)
          ·
            refine ⟨6870785052150195934907333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4580523368100130623271555 6870785052150195934907333)
            ·
              refine ⟨1288272197278161737795125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6870785052150195934907333 1288272197278161737795125)
              ·
                refine ⟨120775518494827662918293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1288272197278161737795125 120775518494827662918293)
                ·
                  rfl

theorem cell20_793832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_793832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793832 prefixEnd_793832 := by exact prefixLift 793832
  have htrace : WordTrace (prefixWord ++ tailWord_793832) baseStart_793832 baseEnd_793832 := by
    simpa [prefixWord, tailWord_793832, baseEnd_793832] using wordTrace_append hprefix tailTrace_793832
  have hstable : (prefixWord ++ tailWord_793832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793832).length < 2 ^ (prefixWord ++ tailWord_793832).sum := by decide
  have hdescent : baseEnd_793832 < baseStart_793832 := by decide
  rcases family_descends (prefixWord ++ tailWord_793832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793835 : List Nat := [1, 1, 1, 1, 2, 8, 2, 1, 3]
def baseStart_793835 : Nat := 118140960795 + 793835 * 2 ^ 59
def prefixEnd_793835 : Nat := 4983230072969 + 3 ^ 40 * 793835 * 2
def baseEnd_793835 : Nat := 362327924766228311654867

theorem tailTrace_793835 : CollatzResearch.WordTrace tailWord_793835 prefixEnd_793835 362327924766228311654867 := by
  unfold tailWord_793835
  simp only [CollatzResearch.WordTrace]
  refine ⟨28953541079078846069334959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19302360719385897379556639 28953541079078846069334959)
  ·
    refine ⟨43430311618618269104002439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28953541079078846069334959 43430311618618269104002439)
    ·
      refine ⟨65145467427927403656003659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43430311618618269104002439 65145467427927403656003659)
      ·
        refine ⟨97718201141891105484005489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65145467427927403656003659 97718201141891105484005489)
        ·
          refine ⟨73288650856418329113004117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97718201141891105484005489 73288650856418329113004117)
          ·
            refine ⟨858851377223652294293017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 73288650856418329113004117 858851377223652294293017)
            ·
              refine ⟨644138532917739220719763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 858851377223652294293017 644138532917739220719763)
              ·
                refine ⟨966207799376608831079645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644138532917739220719763 966207799376608831079645)
                ·
                  refine ⟨362327924766228311654867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 966207799376608831079645 362327924766228311654867)
                  ·
                    rfl

theorem cell20_793835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 3].length) (baseStart_793835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793835 prefixEnd_793835 := by exact prefixLift 793835
  have htrace : WordTrace (prefixWord ++ tailWord_793835) baseStart_793835 baseEnd_793835 := by
    simpa [prefixWord, tailWord_793835, baseEnd_793835] using wordTrace_append hprefix tailTrace_793835
  have hstable : (prefixWord ++ tailWord_793835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793835).length < 2 ^ (prefixWord ++ tailWord_793835).sum := by decide
  have hdescent : baseEnd_793835 < baseStart_793835 := by decide
  rcases family_descends (prefixWord ++ tailWord_793835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793880 : List Nat := [2, 1, 2, 3, 1, 4, 1, 4, 2]
def baseStart_793880 : Nat := 118140960795 + 793880 * 2 ^ 59
def prefixEnd_793880 : Nat := 4983230072969 + 3 ^ 40 * 793880 * 2
def baseEnd_793880 : Nat := 362348463992408155154683

theorem tailTrace_793880 : CollatzResearch.WordTrace tailWord_793880 prefixEnd_793880 362348463992408155154683 := by
  unfold tailWord_793880
  simp only [CollatzResearch.WordTrace]
  refine ⟨14477591181957909377361547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19303454909277212503148729 14477591181957909377361547)
  ·
    refine ⟨21716386772936864066042321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14477591181957909377361547 21716386772936864066042321)
    ·
      refine ⟨16287290079702648049531741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21716386772936864066042321 16287290079702648049531741)
      ·
        refine ⟨6107733779888493018574403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16287290079702648049531741 6107733779888493018574403)
        ·
          refine ⟨9161600669832739527861605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6107733779888493018574403 9161600669832739527861605)
          ·
            refine ⟨1717800125593638661474051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9161600669832739527861605 1717800125593638661474051)
            ·
              refine ⟨2576700188390457992211077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1717800125593638661474051 2576700188390457992211077)
              ·
                refine ⟨483131285323210873539577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2576700188390457992211077 483131285323210873539577)
                ·
                  refine ⟨362348463992408155154683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483131285323210873539577 362348463992408155154683)
                  ·
                    rfl

theorem cell20_793880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 2].length) (baseStart_793880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793880 prefixEnd_793880 := by exact prefixLift 793880
  have htrace : WordTrace (prefixWord ++ tailWord_793880) baseStart_793880 baseEnd_793880 := by
    simpa [prefixWord, tailWord_793880, baseEnd_793880] using wordTrace_append hprefix tailTrace_793880
  have hstable : (prefixWord ++ tailWord_793880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793880).length < 2 ^ (prefixWord ++ tailWord_793880).sum := by decide
  have hdescent : baseEnd_793880 < baseStart_793880 := by decide
  rcases family_descends (prefixWord ++ tailWord_793880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793887 : List Nat := [1, 1, 2, 4, 4, 2, 1, 5]
def baseStart_793887 : Nat := 118140960795 + 793887 * 2 ^ 59
def prefixEnd_793887 : Nat := 4983230072969 + 3 ^ 40 * 793887 * 2
def baseEnd_793887 : Nat := 120783886327715747307107

theorem tailTrace_793887 : CollatzResearch.WordTrace tailWord_793887 prefixEnd_793887 120783886327715747307107 := by
  unfold tailWord_793887
  simp only [CollatzResearch.WordTrace]
  refine ⟨28955437674890458950227915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19303625116593639300151943 28955437674890458950227915)
  ·
    refine ⟨43433156512335688425341873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28955437674890458950227915 43433156512335688425341873)
    ·
      refine ⟨32574867384251766319006405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43433156512335688425341873 32574867384251766319006405)
      ·
        refine ⟨6107787634547206184813701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32574867384251766319006405 6107787634547206184813701)
        ·
          refine ⟨1145210181477601159652569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6107787634547206184813701 1145210181477601159652569)
          ·
            refine ⟨858907636108200869739427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1145210181477601159652569 858907636108200869739427)
            ·
              refine ⟨1288361454162301304609141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858907636108200869739427 1288361454162301304609141)
              ·
                refine ⟨120783886327715747307107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1288361454162301304609141 120783886327715747307107)
                ·
                  rfl

theorem cell20_793887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 5].length) (baseStart_793887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793887 prefixEnd_793887 := by exact prefixLift 793887
  have htrace : WordTrace (prefixWord ++ tailWord_793887) baseStart_793887 baseEnd_793887 := by
    simpa [prefixWord, tailWord_793887, baseEnd_793887] using wordTrace_append hprefix tailTrace_793887
  have hstable : (prefixWord ++ tailWord_793887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793887).length < 2 ^ (prefixWord ++ tailWord_793887).sum := by decide
  have hdescent : baseEnd_793887 < baseStart_793887 := by decide
  rcases family_descends (prefixWord ++ tailWord_793887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793932 : List Nat := [2, 2, 1, 3, 2, 2, 3, 2, 3]
def baseStart_793932 : Nat := 118140960795 + 793932 * 2 ^ 59
def prefixEnd_793932 : Nat := 4983230072969 + 3 ^ 40 * 793932 * 2
def baseEnd_793932 : Nat := 362372198209327085421137

theorem tailTrace_793932 : CollatzResearch.WordTrace tailWord_793932 prefixEnd_793932 362372198209327085421137 := by
  unfold tailWord_793932
  simp only [CollatzResearch.WordTrace]
  refine ⟨14478539479863715817808025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19304719306484954423744033 14478539479863715817808025)
  ·
    refine ⟨10858904609897786863356019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14478539479863715817808025 10858904609897786863356019)
    ·
      refine ⟨16288356914846680295034029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10858904609897786863356019 16288356914846680295034029)
      ·
        refine ⟨6108133843067505110637761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16288356914846680295034029 6108133843067505110637761)
        ·
          refine ⟨4581100382300628832978321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6108133843067505110637761 4581100382300628832978321)
          ·
            refine ⟨3435825286725471624733741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4581100382300628832978321 3435825286725471624733741)
            ·
              refine ⟨1288434482522051859275153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3435825286725471624733741 1288434482522051859275153)
              ·
                refine ⟨966325861891538894456365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1288434482522051859275153 966325861891538894456365)
                ·
                  refine ⟨362372198209327085421137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 966325861891538894456365 362372198209327085421137)
                  ·
                    rfl

theorem cell20_793932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_793932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793932 prefixEnd_793932 := by exact prefixLift 793932
  have htrace : WordTrace (prefixWord ++ tailWord_793932) baseStart_793932 baseEnd_793932 := by
    simpa [prefixWord, tailWord_793932, baseEnd_793932] using wordTrace_append hprefix tailTrace_793932
  have hstable : (prefixWord ++ tailWord_793932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793932).length < 2 ^ (prefixWord ++ tailWord_793932).sum := by decide
  have hdescent : baseEnd_793932 < baseStart_793932 := by decide
  rcases family_descends (prefixWord ++ tailWord_793932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793939 : List Nat := [1, 1, 1, 2, 1, 1, 5, 6, 2]
def baseStart_793939 : Nat := 118140960795 + 793939 * 2 ^ 59
def prefixEnd_793939 : Nat := 4983230072969 + 3 ^ 40 * 793939 * 2
def baseEnd_793939 : Nat := 362375393200066172187775

theorem tailTrace_793939 : CollatzResearch.WordTrace tailWord_793939 prefixEnd_793939 362375393200066172187775 := by
  unfold tailWord_793939
  simp only [CollatzResearch.WordTrace]
  refine ⟨28957334270702071831120871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19304889513801381220747247 28957334270702071831120871)
  ·
    refine ⟨43436001406053107746681307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28957334270702071831120871 43436001406053107746681307)
    ·
      refine ⟨65154002109079661620021961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43436001406053107746681307 65154002109079661620021961)
      ·
        refine ⟨48865501581809746215016471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65154002109079661620021961 48865501581809746215016471)
        ·
          refine ⟨73298252372714619322524707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48865501581809746215016471 73298252372714619322524707)
          ·
            refine ⟨109947378559071928983787061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73298252372714619322524707 109947378559071928983787061)
            ·
              refine ⟨10307566739912993342230037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109947378559071928983787061 10307566739912993342230037)
              ·
                refine ⟨483167190933421562917033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10307566739912993342230037 483167190933421562917033)
                ·
                  refine ⟨362375393200066172187775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483167190933421562917033 362375393200066172187775)
                  ·
                    rfl

theorem cell20_793939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 6, 2].length) (baseStart_793939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793939 prefixEnd_793939 := by exact prefixLift 793939
  have htrace : WordTrace (prefixWord ++ tailWord_793939) baseStart_793939 baseEnd_793939 := by
    simpa [prefixWord, tailWord_793939, baseEnd_793939] using wordTrace_append hprefix tailTrace_793939
  have hstable : (prefixWord ++ tailWord_793939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793939).length < 2 ^ (prefixWord ++ tailWord_793939).sum := by decide
  have hdescent : baseEnd_793939 < baseStart_793939 := by decide
  rcases family_descends (prefixWord ++ tailWord_793939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793953 : List Nat := [1, 2, 3, 1, 1, 1, 1, 7, 3]
def baseStart_793953 : Nat := 118140960795 + 793953 * 2 ^ 59
def prefixEnd_793953 : Nat := 4983230072969 + 3 ^ 40 * 793953 * 2
def baseEnd_793953 : Nat := 362381783181544345721051

theorem tailTrace_793953 : CollatzResearch.WordTrace tailWord_793953 prefixEnd_793953 362381783181544345721051 := by
  unfold tailWord_793953
  simp only [CollatzResearch.WordTrace]
  refine ⟨28957844892651352222130513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19305229928434234814753675 28957844892651352222130513)
  ·
    refine ⟨21718383669488514166597885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28957844892651352222130513 21718383669488514166597885)
    ·
      refine ⟨8144393876058192812474207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21718383669488514166597885 8144393876058192812474207)
      ·
        refine ⟨12216590814087289218711311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8144393876058192812474207 12216590814087289218711311)
        ·
          refine ⟨18324886221130933828066967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12216590814087289218711311 18324886221130933828066967)
          ·
            refine ⟨27487329331696400742100451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18324886221130933828066967 27487329331696400742100451)
            ·
              refine ⟨41230993997544601113150677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27487329331696400742100451 41230993997544601113150677)
              ·
                refine ⟨966351421817451588589469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 41230993997544601113150677 966351421817451588589469)
                ·
                  refine ⟨362381783181544345721051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 966351421817451588589469 362381783181544345721051)
                  ·
                    rfl

theorem cell20_793953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_793953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793953 prefixEnd_793953 := by exact prefixLift 793953
  have htrace : WordTrace (prefixWord ++ tailWord_793953) baseStart_793953 baseEnd_793953 := by
    simpa [prefixWord, tailWord_793953, baseEnd_793953] using wordTrace_append hprefix tailTrace_793953
  have hstable : (prefixWord ++ tailWord_793953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793953).length < 2 ^ (prefixWord ++ tailWord_793953).sum := by decide
  have hdescent : baseEnd_793953 < baseStart_793953 := by decide
  rcases family_descends (prefixWord ++ tailWord_793953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793967 : List Nat := [1, 1, 2, 1, 3, 1, 5, 6]
def baseStart_793967 : Nat := 118140960795 + 793967 * 2 ^ 59
def prefixEnd_793967 : Nat := 4983230072969 + 3 ^ 40 * 793967 * 2
def baseEnd_793967 : Nat := 120796057721007506418109

theorem tailTrace_793967 : CollatzResearch.WordTrace tailWord_793967 prefixEnd_793967 120796057721007506418109 := by
  unfold tailWord_793967
  simp only [CollatzResearch.WordTrace]
  refine ⟨28958355514600632613140155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19305570343067088408760103 28958355514600632613140155)
  ·
    refine ⟨43437533271900948919710233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28958355514600632613140155 43437533271900948919710233)
    ·
      refine ⟨32578149953925711689782675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43437533271900948919710233 32578149953925711689782675)
      ·
        refine ⟨48867224930888567534674013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32578149953925711689782675 48867224930888567534674013)
        ·
          refine ⟨18325209349083212825502755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48867224930888567534674013 18325209349083212825502755)
          ·
            refine ⟨27487814023624819238254133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18325209349083212825502755 27487814023624819238254133)
            ·
              refine ⟨2576982564714826803586325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27487814023624819238254133 2576982564714826803586325)
              ·
                refine ⟨120796057721007506418109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2576982564714826803586325 120796057721007506418109)
                ·
                  rfl

theorem cell20_793967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 6].length) (baseStart_793967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793967 prefixEnd_793967 := by exact prefixLift 793967
  have htrace : WordTrace (prefixWord ++ tailWord_793967) baseStart_793967 baseEnd_793967 := by
    simpa [prefixWord, tailWord_793967, baseEnd_793967] using wordTrace_append hprefix tailTrace_793967
  have hstable : (prefixWord ++ tailWord_793967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793967).length < 2 ^ (prefixWord ++ tailWord_793967).sum := by decide
  have hdescent : baseEnd_793967 < baseStart_793967 := by decide
  rcases family_descends (prefixWord ++ tailWord_793967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793991 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 5]
def baseStart_793991 : Nat := 118140960795 + 793991 * 2 ^ 59
def prefixEnd_793991 : Nat := 4983230072969 + 3 ^ 40 * 793991 * 2
def baseEnd_793991 : Nat := 362399127416985102454229

theorem tailTrace_793991 : CollatzResearch.WordTrace tailWord_793991 prefixEnd_793991 362399127416985102454229 := by
  unfold tailWord_793991
  simp only [CollatzResearch.WordTrace]
  refine ⟨28959230866513684712013827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19306153911009123141342551 28959230866513684712013827)
  ·
    refine ⟨43438846299770527068020741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28959230866513684712013827 43438846299770527068020741)
    ·
      refine ⟨8144783681206973825253889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43438846299770527068020741 8144783681206973825253889)
      ·
        refine ⟨6108587760905230368940417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8144783681206973825253889 6108587760905230368940417)
        ·
          refine ⟨4581440820678922776705313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6108587760905230368940417 4581440820678922776705313)
          ·
            refine ⟨3436080615509192082528985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4581440820678922776705313 3436080615509192082528985)
            ·
              refine ⟨2577060461631894061896739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3436080615509192082528985 2577060461631894061896739)
              ·
                refine ⟨3865590692447841092845109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2577060461631894061896739 3865590692447841092845109)
                ·
                  refine ⟨362399127416985102454229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3865590692447841092845109 362399127416985102454229)
                  ·
                    rfl

theorem cell20_793991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_793991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_793991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_793991 prefixEnd_793991 := by exact prefixLift 793991
  have htrace : WordTrace (prefixWord ++ tailWord_793991) baseStart_793991 baseEnd_793991 := by
    simpa [prefixWord, tailWord_793991, baseEnd_793991] using wordTrace_append hprefix tailTrace_793991
  have hstable : (prefixWord ++ tailWord_793991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793991).length < 2 ^ (prefixWord ++ tailWord_793991).sum := by decide
  have hdescent : baseEnd_793991 < baseStart_793991 := by decide
  rcases family_descends (prefixWord ++ tailWord_793991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794004 : List Nat := [2, 4, 2, 1, 2, 3, 2, 1, 3]
def baseStart_794004 : Nat := 118140960795 + 794004 * 2 ^ 59
def prefixEnd_794004 : Nat := 4983230072969 + 3 ^ 40 * 794004 * 2
def baseEnd_794004 : Nat := 362405060971214835020843

theorem tailTrace_794004 : CollatzResearch.WordTrace tailWord_794004 prefixEnd_794004 362405060971214835020843 := by
  unfold tailWord_794004
  simp only [CollatzResearch.WordTrace]
  refine ⟨14479852507733293966118533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19306470010311058621491377 14479852507733293966118533)
  ·
    refine ⟨2714972345199992618647225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14479852507733293966118533 2714972345199992618647225)
    ·
      refine ⟨2036229258899994463985419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2714972345199992618647225 2036229258899994463985419)
      ·
        refine ⟨3054343888349991695978129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2036229258899994463985419 3054343888349991695978129)
        ·
          refine ⟨2290757916262493771983597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3054343888349991695978129 2290757916262493771983597)
          ·
            refine ⟨859034218598435164493849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2290757916262493771983597 859034218598435164493849)
            ·
              refine ⟨644275663948826373370387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 859034218598435164493849 644275663948826373370387)
              ·
                refine ⟨966413495923239560055581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644275663948826373370387 966413495923239560055581)
                ·
                  refine ⟨362405060971214835020843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 966413495923239560055581 362405060971214835020843)
                  ·
                    rfl

theorem cell20_794004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_794004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794004 prefixEnd_794004 := by exact prefixLift 794004
  have htrace : WordTrace (prefixWord ++ tailWord_794004) baseStart_794004 baseEnd_794004 := by
    simpa [prefixWord, tailWord_794004, baseEnd_794004] using wordTrace_append hprefix tailTrace_794004
  have hstable : (prefixWord ++ tailWord_794004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794004).length < 2 ^ (prefixWord ++ tailWord_794004).sum := by decide
  have hdescent : baseEnd_794004 < baseStart_794004 := by decide
  rcases family_descends (prefixWord ++ tailWord_794004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794005 : List Nat := [1, 3, 2, 1, 1, 2, 3, 7]
def baseStart_794005 : Nat := 118140960795 + 794005 * 2 ^ 59
def prefixEnd_794005 : Nat := 4983230072969 + 3 ^ 40 * 794005 * 2
def baseEnd_794005 : Nat := 120801839132821091995835

theorem tailTrace_794005 : CollatzResearch.WordTrace tailWord_794005 prefixEnd_794005 120801839132821091995835 := by
  unfold tailWord_794005
  simp only [CollatzResearch.WordTrace]
  refine ⟨28959741488462965103023469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19306494325641976735348979 28959741488462965103023469)
  ·
    refine ⟨10859903058173611913633801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28959741488462965103023469 10859903058173611913633801)
    ·
      refine ⟨8144927293630208935225351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10859903058173611913633801 8144927293630208935225351)
      ·
        refine ⟨12217390940445313402838027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8144927293630208935225351 12217390940445313402838027)
        ·
          refine ⟨18326086410667970104257041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12217390940445313402838027 18326086410667970104257041)
          ·
            refine ⟨13744564808000977578192781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18326086410667970104257041 13744564808000977578192781)
            ·
              refine ⟨5154211803000366591822293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13744564808000977578192781 5154211803000366591822293)
              ·
                refine ⟨120801839132821091995835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5154211803000366591822293 120801839132821091995835)
                ·
                  rfl

theorem cell20_794005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 7].length) (baseStart_794005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794005 prefixEnd_794005 := by exact prefixLift 794005
  have htrace : WordTrace (prefixWord ++ tailWord_794005) baseStart_794005 baseEnd_794005 := by
    simpa [prefixWord, tailWord_794005, baseEnd_794005] using wordTrace_append hprefix tailTrace_794005
  have hstable : (prefixWord ++ tailWord_794005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794005).length < 2 ^ (prefixWord ++ tailWord_794005).sum := by decide
  have hdescent : baseEnd_794005 < baseStart_794005 := by decide
  rcases family_descends (prefixWord ++ tailWord_794005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794060 : List Nat := [2, 2, 1, 4, 2, 1, 3, 5]
def baseStart_794060 : Nat := 118140960795 + 794060 * 2 ^ 59
def prefixEnd_794060 : Nat := 4983230072969 + 3 ^ 40 * 794060 * 2
def baseEnd_794060 : Nat := 120810206965709176384649

theorem tailTrace_794060 : CollatzResearch.WordTrace tailWord_794060 prefixEnd_794060 120810206965709176384649 := by
  unfold tailWord_794060
  simp only [CollatzResearch.WordTrace]
  refine ⟨14480873751631854748137817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19307831668842472997517089 14480873751631854748137817)
  ·
    refine ⟨10860655313723891061103363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14480873751631854748137817 10860655313723891061103363)
    ·
      refine ⟨16290982970585836591655045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10860655313723891061103363 16290982970585836591655045)
      ·
        refine ⟨3054559306984844360935321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16290982970585836591655045 3054559306984844360935321)
        ·
          refine ⟨2290919480238633270701491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3054559306984844360935321 2290919480238633270701491)
          ·
            refine ⟨3436379220357949906052237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2290919480238633270701491 3436379220357949906052237)
            ·
              refine ⟨1288642207634231214769589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3436379220357949906052237 1288642207634231214769589)
              ·
                refine ⟨120810206965709176384649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1288642207634231214769589 120810206965709176384649)
                ·
                  rfl

theorem cell20_794060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_794060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794060 prefixEnd_794060 := by exact prefixLift 794060
  have htrace : WordTrace (prefixWord ++ tailWord_794060) baseStart_794060 baseEnd_794060 := by
    simpa [prefixWord, tailWord_794060, baseEnd_794060] using wordTrace_append hprefix tailTrace_794060
  have hstable : (prefixWord ++ tailWord_794060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794060).length < 2 ^ (prefixWord ++ tailWord_794060).sum := by decide
  have hdescent : baseEnd_794060 < baseStart_794060 := by decide
  rcases family_descends (prefixWord ++ tailWord_794060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794070 : List Nat := [5, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_794070 : Nat := 118140960795 + 794070 * 2 ^ 59
def prefixEnd_794070 : Nat := 4983230072969 + 3 ^ 40 * 794070 * 2
def baseEnd_794070 : Nat := 362435185169611938820573

theorem tailTrace_794070 : CollatzResearch.WordTrace tailWord_794070 prefixEnd_794070 362435185169611938820573 := by
  unfold tailWord_794070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1810132014576717575258729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19308074822151654136093109 1810132014576717575258729)
  ·
    refine ⟨1357599010932538181444047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1810132014576717575258729 1357599010932538181444047)
    ·
      refine ⟨2036398516398807272166071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1357599010932538181444047 2036398516398807272166071)
      ·
        refine ⟨3054597774598210908249107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2036398516398807272166071 3054597774598210908249107)
        ·
          refine ⟨4581896661897316362373661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3054597774598210908249107 4581896661897316362373661)
          ·
            refine ⟨1718211248211493635890123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4581896661897316362373661 1718211248211493635890123)
            ·
              refine ⟨2577316872317240453835185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1718211248211493635890123 2577316872317240453835185)
              ·
                refine ⟨1932987654237930340376389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2577316872317240453835185 1932987654237930340376389)
                ·
                  refine ⟨362435185169611938820573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1932987654237930340376389 362435185169611938820573)
                  ·
                    rfl

theorem cell20_794070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_794070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794070 prefixEnd_794070 := by exact prefixLift 794070
  have htrace : WordTrace (prefixWord ++ tailWord_794070) baseStart_794070 baseEnd_794070 := by
    simpa [prefixWord, tailWord_794070, baseEnd_794070] using wordTrace_append hprefix tailTrace_794070
  have hstable : (prefixWord ++ tailWord_794070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794070).length < 2 ^ (prefixWord ++ tailWord_794070).sum := by decide
  have hdescent : baseEnd_794070 < baseStart_794070 := by decide
  rcases family_descends (prefixWord ++ tailWord_794070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794074 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_794074 : Nat := 118140960795 + 794074 * 2 ^ 59
def prefixEnd_794074 : Nat := 4983230072969 + 3 ^ 40 * 794074 * 2
def baseEnd_794074 : Nat := 362437010878605702687223

theorem tailTrace_794074 : CollatzResearch.WordTrace tailWord_794074 prefixEnd_794074 362437010878605702687223 := by
  unfold tailWord_794074
  simp only [CollatzResearch.WordTrace]
  refine ⟨7240564531303247471821319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19308172083475326591523517 7240564531303247471821319)
  ·
    refine ⟨10860846796954871207731979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7240564531303247471821319 10860846796954871207731979)
    ·
      refine ⟨16291270195432306811597969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10860846796954871207731979 16291270195432306811597969)
      ·
        refine ⟨12218452646574230108698477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16291270195432306811597969 12218452646574230108698477)
        ·
          refine ⟨4581919742465336290761929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12218452646574230108698477 4581919742465336290761929)
          ·
            refine ⟨3436439806849002218071447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4581919742465336290761929 3436439806849002218071447)
            ·
              refine ⟨5154659710273503327107171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3436439806849002218071447 5154659710273503327107171)
              ·
                refine ⟨7731989565410254990660757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5154659710273503327107171 7731989565410254990660757)
                ·
                  refine ⟨362437010878605702687223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7731989565410254990660757 362437010878605702687223)
                  ·
                    rfl

theorem cell20_794074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_794074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794074 prefixEnd_794074 := by exact prefixLift 794074
  have htrace : WordTrace (prefixWord ++ tailWord_794074) baseStart_794074 baseEnd_794074 := by
    simpa [prefixWord, tailWord_794074, baseEnd_794074] using wordTrace_append hprefix tailTrace_794074
  have hstable : (prefixWord ++ tailWord_794074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794074).length < 2 ^ (prefixWord ++ tailWord_794074).sum := by decide
  have hdescent : baseEnd_794074 < baseStart_794074 := by decide
  rcases family_descends (prefixWord ++ tailWord_794074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794077 : List Nat := [1, 4, 3, 1, 1, 3, 3, 4]
def baseStart_794077 : Nat := 118140960795 + 794077 * 2 ^ 59
def prefixEnd_794077 : Nat := 4983230072969 + 3 ^ 40 * 794077 * 2
def baseEnd_794077 : Nat := 120812793386783675195737

theorem tailTrace_794077 : CollatzResearch.WordTrace tailWord_794077 prefixEnd_794077 120812793386783675195737 := by
  unfold tailWord_794077
  simp only [CollatzResearch.WordTrace]
  refine ⟨28962367544202121399644485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19308245029468080933096323 28962367544202121399644485)
  ·
    refine ⟨5430443914537897762433341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28962367544202121399644485 5430443914537897762433341)
    ·
      refine ⟨2036416467951711660912503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5430443914537897762433341 2036416467951711660912503)
      ·
        refine ⟨3054624701927567491368755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2036416467951711660912503 3054624701927567491368755)
        ·
          refine ⟨4581937052891351237053133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3054624701927567491368755 4581937052891351237053133)
          ·
            refine ⟨1718226394834256713894925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4581937052891351237053133 1718226394834256713894925)
            ·
              refine ⟨644334898062846267710597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1718226394834256713894925 644334898062846267710597)
              ·
                refine ⟨120812793386783675195737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 644334898062846267710597 120812793386783675195737)
                ·
                  rfl

theorem cell20_794077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 4].length) (baseStart_794077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794077 prefixEnd_794077 := by exact prefixLift 794077
  have htrace : WordTrace (prefixWord ++ tailWord_794077) baseStart_794077 baseEnd_794077 := by
    simpa [prefixWord, tailWord_794077, baseEnd_794077] using wordTrace_append hprefix tailTrace_794077
  have hstable : (prefixWord ++ tailWord_794077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794077).length < 2 ^ (prefixWord ++ tailWord_794077).sum := by decide
  have hdescent : baseEnd_794077 < baseStart_794077 := by decide
  rcases family_descends (prefixWord ++ tailWord_794077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794098 : List Nat := [3, 2, 1, 4, 1, 2, 7]
def baseStart_794098 : Nat := 118140960795 + 794098 * 2 ^ 59
def prefixEnd_794098 : Nat := 4983230072969 + 3 ^ 40 * 794098 * 2
def baseEnd_794098 : Nat := 40271996125840920654125

theorem tailTrace_794098 : CollatzResearch.WordTrace tailWord_794098 prefixEnd_794098 40271996125840920654125 := by
  unfold tailWord_794098
  simp only [CollatzResearch.WordTrace]
  refine ⟨7240783369281510496539737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19308755651417361324105965 7240783369281510496539737)
  ·
    refine ⟨5430587526961132872404803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7240783369281510496539737 5430587526961132872404803)
    ·
      refine ⟨8145881290441699308607205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5430587526961132872404803 8145881290441699308607205)
      ·
        refine ⟨1527352741957818620363851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8145881290441699308607205 1527352741957818620363851)
        ·
          refine ⟨2291029112936727930545777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1527352741957818620363851 2291029112936727930545777)
          ·
            refine ⟨1718271834702545947909333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2291029112936727930545777 1718271834702545947909333)
            ·
              refine ⟨40271996125840920654125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1718271834702545947909333 40271996125840920654125)
              ·
                rfl

theorem cell20_794098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 7].length) (baseStart_794098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794098 prefixEnd_794098 := by exact prefixLift 794098
  have htrace : WordTrace (prefixWord ++ tailWord_794098) baseStart_794098 baseEnd_794098 := by
    simpa [prefixWord, tailWord_794098, baseEnd_794098] using wordTrace_append hprefix tailTrace_794098
  have hstable : (prefixWord ++ tailWord_794098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794098).length < 2 ^ (prefixWord ++ tailWord_794098).sum := by decide
  have hdescent : baseEnd_794098 < baseStart_794098 := by decide
  rcases family_descends (prefixWord ++ tailWord_794098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794101 : List Nat := [1, 3, 5, 1, 1, 1, 3, 2, 3]
def baseStart_794101 : Nat := 118140960795 + 794101 * 2 ^ 59
def prefixEnd_794101 : Nat := 4983230072969 + 3 ^ 40 * 794101 * 2
def baseEnd_794101 : Nat := 362449334414313608787113

theorem tailTrace_794101 : CollatzResearch.WordTrace tailWord_794101 prefixEnd_794101 362449334414313608787113 := by
  unfold tailWord_794101
  simp only [CollatzResearch.WordTrace]
  refine ⟨28963242896115173498518157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19308828597410115665678771 28963242896115173498518157)
  ·
    refine ⟨10861216086043190061944309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28963242896115173498518157 10861216086043190061944309)
    ·
      refine ⟨1018239008066549068307279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10861216086043190061944309 1018239008066549068307279)
      ·
        refine ⟨1527358512099823602460919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1018239008066549068307279 1527358512099823602460919)
        ·
          refine ⟨2291037768149735403691379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1527358512099823602460919 2291037768149735403691379)
          ·
            refine ⟨3436556652224603105537069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2291037768149735403691379 3436556652224603105537069)
            ·
              refine ⟨1288708744584226164576401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3436556652224603105537069 1288708744584226164576401)
              ·
                refine ⟨966531558438169623432301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1288708744584226164576401 966531558438169623432301)
                ·
                  refine ⟨362449334414313608787113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 966531558438169623432301 362449334414313608787113)
                  ·
                    rfl

theorem cell20_794101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_794101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794101 prefixEnd_794101 := by exact prefixLift 794101
  have htrace : WordTrace (prefixWord ++ tailWord_794101) baseStart_794101 baseEnd_794101 := by
    simpa [prefixWord, tailWord_794101, baseEnd_794101] using wordTrace_append hprefix tailTrace_794101
  have hstable : (prefixWord ++ tailWord_794101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794101).length < 2 ^ (prefixWord ++ tailWord_794101).sum := by decide
  have hdescent : baseEnd_794101 < baseStart_794101 := by decide
  rcases family_descends (prefixWord ++ tailWord_794101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794136 : List Nat := [2, 1, 2, 3, 4, 1, 1, 6]
def baseStart_794136 : Nat := 118140960795 + 794136 * 2 ^ 59
def prefixEnd_794136 : Nat := 4983230072969 + 3 ^ 40 * 794136 * 2
def baseEnd_794136 : Nat := 120821769789336347540101

theorem tailTrace_794136 : CollatzResearch.WordTrace tailWord_794136 prefixEnd_794136 120821769789336347540101 := by
  unfold tailWord_794136
  simp only [CollatzResearch.WordTrace]
  refine ⟨14482259725494187238021131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19309679633992249650694841 14482259725494187238021131)
  ·
    refine ⟨21723389588241280857031697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14482259725494187238021131 21723389588241280857031697)
    ·
      refine ⟨16292542191180960642773773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21723389588241280857031697 16292542191180960642773773)
      ·
        refine ⟨6109703321692860241040165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16292542191180960642773773 6109703321692860241040165)
        ·
          refine ⟨1145569372817411295195031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6109703321692860241040165 1145569372817411295195031)
          ·
            refine ⟨1718354059226116942792547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1145569372817411295195031 1718354059226116942792547)
            ·
              refine ⟨2577531088839175414188821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1718354059226116942792547 2577531088839175414188821)
              ·
                refine ⟨120821769789336347540101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2577531088839175414188821 120821769789336347540101)
                ·
                  rfl

theorem cell20_794136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_794136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794136 prefixEnd_794136 := by exact prefixLift 794136
  have htrace : WordTrace (prefixWord ++ tailWord_794136) baseStart_794136 baseEnd_794136 := by
    simpa [prefixWord, tailWord_794136, baseEnd_794136] using wordTrace_append hprefix tailTrace_794136
  have hstable : (prefixWord ++ tailWord_794136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794136).length < 2 ^ (prefixWord ++ tailWord_794136).sum := by decide
  have hdescent : baseEnd_794136 < baseStart_794136 := by decide
  rcases family_descends (prefixWord ++ tailWord_794136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794146 : List Nat := [3, 3, 1, 1, 1, 1, 5, 3, 2]
def baseStart_794146 : Nat := 118140960795 + 794146 * 2 ^ 59
def prefixEnd_794146 : Nat := 4983230072969 + 3 ^ 40 * 794146 * 2
def baseEnd_794146 : Nat := 362469873640493452286929

theorem tailTrace_794146 : CollatzResearch.WordTrace tailWord_794146 prefixEnd_794146 362469873640493452286929 := by
  unfold tailWord_794146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7241221045238036545976573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19309922787301430789270861 7241221045238036545976573)
  ·
    refine ⟨2715457891964263704741215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7241221045238036545976573 2715457891964263704741215)
    ·
      refine ⟨4073186837946395557111823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2715457891964263704741215 4073186837946395557111823)
      ·
        refine ⟨6109780256919593335667735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4073186837946395557111823 6109780256919593335667735)
        ·
          refine ⟨9164670385379390003501603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6109780256919593335667735 9164670385379390003501603)
          ·
            refine ⟨13747005578069085005252405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9164670385379390003501603 13747005578069085005252405)
            ·
              refine ⟨1288781772943976719242413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13747005578069085005252405 1288781772943976719242413)
              ·
                refine ⟨483293164853991269715905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1288781772943976719242413 483293164853991269715905)
                ·
                  refine ⟨362469873640493452286929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483293164853991269715905 362469873640493452286929)
                  ·
                    rfl

theorem cell20_794146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_794146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794146 prefixEnd_794146 := by exact prefixLift 794146
  have htrace : WordTrace (prefixWord ++ tailWord_794146) baseStart_794146 baseEnd_794146 := by
    simpa [prefixWord, tailWord_794146, baseEnd_794146] using wordTrace_append hprefix tailTrace_794146
  have hstable : (prefixWord ++ tailWord_794146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794146).length < 2 ^ (prefixWord ++ tailWord_794146).sum := by decide
  have hdescent : baseEnd_794146 < baseStart_794146 := by decide
  rcases family_descends (prefixWord ++ tailWord_794146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794167 : List Nat := [1, 1, 3, 1, 2, 6, 1, 1, 4]
def baseStart_794167 : Nat := 118140960795 + 794167 * 2 ^ 59
def prefixEnd_794167 : Nat := 4983230072969 + 3 ^ 40 * 794167 * 2
def baseEnd_794167 : Nat := 362479458612710712586843

theorem tailTrace_794167 : CollatzResearch.WordTrace tailWord_794167 prefixEnd_794167 362479458612710712586843 := by
  unfold tailWord_794167
  simp only [CollatzResearch.WordTrace]
  refine ⟨28965650113876066770420755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19310433409250711180280503 28965650113876066770420755)
  ·
    refine ⟨43448475170814100155631133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28965650113876066770420755 43448475170814100155631133)
    ·
      refine ⟨16293178189055287558361675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43448475170814100155631133 16293178189055287558361675)
      ·
        refine ⟨24439767283582931337542513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16293178189055287558361675 24439767283582931337542513)
        ·
          refine ⟨18329825462687198503156885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24439767283582931337542513 18329825462687198503156885)
          ·
            refine ⟨859210568563462429835479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18329825462687198503156885 859210568563462429835479)
            ·
              refine ⟨1288815852845193644753219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859210568563462429835479 1288815852845193644753219)
              ·
                refine ⟨1933223779267790467129829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1288815852845193644753219 1933223779267790467129829)
                ·
                  refine ⟨362479458612710712586843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1933223779267790467129829 362479458612710712586843)
                  ·
                    rfl

theorem cell20_794167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 4].length) (baseStart_794167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794167 prefixEnd_794167 := by exact prefixLift 794167
  have htrace : WordTrace (prefixWord ++ tailWord_794167) baseStart_794167 baseEnd_794167 := by
    simpa [prefixWord, tailWord_794167, baseEnd_794167] using wordTrace_append hprefix tailTrace_794167
  have hstable : (prefixWord ++ tailWord_794167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794167).length < 2 ^ (prefixWord ++ tailWord_794167).sum := by decide
  have hdescent : baseEnd_794167 < baseStart_794167 := by decide
  rcases family_descends (prefixWord ++ tailWord_794167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794181 : List Nat := [1, 3, 1, 1, 1, 4, 3, 3, 3]
def baseStart_794181 : Nat := 118140960795 + 794181 * 2 ^ 59
def prefixEnd_794181 : Nat := 4983230072969 + 3 ^ 40 * 794181 * 2
def baseEnd_794181 : Nat := 362485848594188886120119

theorem tailTrace_794181 : CollatzResearch.WordTrace tailWord_794181 prefixEnd_794181 362485848594188886120119 := by
  unfold tailWord_794181
  simp only [CollatzResearch.WordTrace]
  refine ⟨28966160735825347161430397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19310773823883564774286931 28966160735825347161430397)
  ·
    refine ⟨10862310275934505185536399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28966160735825347161430397 10862310275934505185536399)
    ·
      refine ⟨16293465413901757778304599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10862310275934505185536399 16293465413901757778304599)
      ·
        refine ⟨24440198120852636667456899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16293465413901757778304599 24440198120852636667456899)
        ·
          refine ⟨36660297181278955001185349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24440198120852636667456899 36660297181278955001185349)
          ·
            refine ⟨6873805721489804062722253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36660297181278955001185349 6873805721489804062722253)
            ·
              refine ⟨2577677145558676523520845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6873805721489804062722253 2577677145558676523520845)
              ·
                refine ⟨966628929584503696320317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2577677145558676523520845 966628929584503696320317)
                ·
                  refine ⟨362485848594188886120119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 966628929584503696320317 362485848594188886120119)
                  ·
                    rfl

theorem cell20_794181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_794181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794181 prefixEnd_794181 := by exact prefixLift 794181
  have htrace : WordTrace (prefixWord ++ tailWord_794181) baseStart_794181 baseEnd_794181 := by
    simpa [prefixWord, tailWord_794181, baseEnd_794181] using wordTrace_append hprefix tailTrace_794181
  have hstable : (prefixWord ++ tailWord_794181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794181).length < 2 ^ (prefixWord ++ tailWord_794181).sum := by decide
  have hdescent : baseEnd_794181 < baseStart_794181 := by decide
  rcases family_descends (prefixWord ++ tailWord_794181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794202 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_794202 : Nat := 118140960795 + 794202 * 2 ^ 59
def prefixEnd_794202 : Nat := 4983230072969 + 3 ^ 40 * 794202 * 2
def baseEnd_794202 : Nat := 362495433566406146420033

theorem tailTrace_794202 : CollatzResearch.WordTrace tailWord_794202 prefixEnd_794202 362495433566406146420033 := by
  unfold tailWord_794202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7241731667187316936986215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19311284445832845165296573 7241731667187316936986215)
  ·
    refine ⟨10862597500780975405479323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7241731667187316936986215 10862597500780975405479323)
    ·
      refine ⟨16293896251171463108218985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10862597500780975405479323 16293896251171463108218985)
      ·
        refine ⟨12220422188378597331164239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16293896251171463108218985 12220422188378597331164239)
        ·
          refine ⟨18330633282567895996746359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12220422188378597331164239 18330633282567895996746359)
          ·
            refine ⟨27495949923851843995119539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18330633282567895996746359 27495949923851843995119539)
            ·
              refine ⟨41243924885777765992679309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27495949923851843995119539 41243924885777765992679309)
              ·
                refine ⟨15466471832166662247254741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41243924885777765992679309 15466471832166662247254741)
                ·
                  refine ⟨362495433566406146420033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15466471832166662247254741 362495433566406146420033)
                  ·
                    rfl

theorem cell20_794202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_794202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794202 prefixEnd_794202 := by exact prefixLift 794202
  have htrace : WordTrace (prefixWord ++ tailWord_794202) baseStart_794202 baseEnd_794202 := by
    simpa [prefixWord, tailWord_794202, baseEnd_794202] using wordTrace_append hprefix tailTrace_794202
  have hstable : (prefixWord ++ tailWord_794202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794202).length < 2 ^ (prefixWord ++ tailWord_794202).sum := by decide
  have hdescent : baseEnd_794202 < baseStart_794202 := by decide
  rcases family_descends (prefixWord ++ tailWord_794202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794229 : List Nat := [1, 3, 4, 2, 1, 3, 1, 5]
def baseStart_794229 : Nat := 118140960795 + 794229 * 2 ^ 59
def prefixEnd_794229 : Nat := 4983230072969 + 3 ^ 40 * 794229 * 2
def baseEnd_794229 : Nat := 120835919034038017506641

theorem tailTrace_794229 : CollatzResearch.WordTrace tailWord_794229 prefixEnd_794229 120835919034038017506641 := by
  unfold tailWord_794229
  simp only [CollatzResearch.WordTrace]
  refine ⟨28967911439651451359177741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19311940959767634239451827 28967911439651451359177741)
  ·
    refine ⟨10862966789869294259691653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28967911439651451359177741 10862966789869294259691653)
    ·
      refine ⟨2036806273100492673692185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10862966789869294259691653 2036806273100492673692185)
      ·
        refine ⟨1527604704825369505269139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2036806273100492673692185 1527604704825369505269139)
        ·
          refine ⟨2291407057238054257903709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1527604704825369505269139 2291407057238054257903709)
          ·
            refine ⟨859277646464270346713891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2291407057238054257903709 859277646464270346713891)
            ·
              refine ⟨1288916469696405520070837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859277646464270346713891 1288916469696405520070837)
              ·
                refine ⟨120835919034038017506641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1288916469696405520070837 120835919034038017506641)
                ·
                  rfl

theorem cell20_794229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 5].length) (baseStart_794229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794229 prefixEnd_794229 := by exact prefixLift 794229
  have htrace : WordTrace (prefixWord ++ tailWord_794229) baseStart_794229 baseEnd_794229 := by
    simpa [prefixWord, tailWord_794229, baseEnd_794229] using wordTrace_append hprefix tailTrace_794229
  have hstable : (prefixWord ++ tailWord_794229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794229).length < 2 ^ (prefixWord ++ tailWord_794229).sum := by decide
  have hdescent : baseEnd_794229 < baseStart_794229 := by decide
  rcases family_descends (prefixWord ++ tailWord_794229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794332 : List Nat := [2, 2, 5, 1, 2, 1, 3, 2, 2]
def baseStart_794332 : Nat := 118140960795 + 794332 * 2 ^ 59
def prefixEnd_794332 : Nat := 4983230072969 + 3 ^ 40 * 794332 * 2
def baseEnd_794332 : Nat := 362554769108703472086169

theorem tailTrace_794332 : CollatzResearch.WordTrace tailWord_794332 prefixEnd_794332 362554769108703472086169 := by
  unfold tailWord_794332
  simp only [CollatzResearch.WordTrace]
  refine ⟨14485834079139149975088625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19314445438852199966784833 14485834079139149975088625)
  ·
    refine ⟨10864375559354362481316469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14485834079139149975088625 10864375559354362481316469)
    ·
      refine ⟨1018535208689471482623419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10864375559354362481316469 1018535208689471482623419)
      ·
        refine ⟨1527802813034207223935129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1018535208689471482623419 1527802813034207223935129)
        ·
          refine ⟨1145852109775655417951347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1527802813034207223935129 1145852109775655417951347)
          ·
            refine ⟨1718778164663483126927021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1145852109775655417951347 1718778164663483126927021)
            ·
              refine ⟨644541811748806172597633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1718778164663483126927021 644541811748806172597633)
              ·
                refine ⟨483406358811604629448225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 644541811748806172597633 483406358811604629448225)
                ·
                  refine ⟨362554769108703472086169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483406358811604629448225 362554769108703472086169)
                  ·
                    rfl

theorem cell20_794332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_794332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794332 prefixEnd_794332 := by exact prefixLift 794332
  have htrace : WordTrace (prefixWord ++ tailWord_794332) baseStart_794332 baseEnd_794332 := by
    simpa [prefixWord, tailWord_794332, baseEnd_794332] using wordTrace_append hprefix tailTrace_794332
  have hstable : (prefixWord ++ tailWord_794332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794332).length < 2 ^ (prefixWord ++ tailWord_794332).sum := by decide
  have hdescent : baseEnd_794332 < baseStart_794332 := by decide
  rcases family_descends (prefixWord ++ tailWord_794332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794343 : List Nat := [1, 1, 5, 4, 1, 1, 2, 5]
def baseStart_794343 : Nat := 118140960795 + 794343 * 2 ^ 59
def prefixEnd_794343 : Nat := 4983230072969 + 3 ^ 40 * 794343 * 2
def baseEnd_794343 : Nat := 120853263269478774239819

theorem tailTrace_794343 : CollatzResearch.WordTrace tailWord_794343 prefixEnd_794343 120853263269478774239819 := by
  unfold tailWord_794343
  simp only [CollatzResearch.WordTrace]
  refine ⟨28972069361238448828827683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19314712907492299219218455 28972069361238448828827683)
  ·
    refine ⟨43458104041857673243241525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28972069361238448828827683 43458104041857673243241525)
    ·
      refine ⟨4074197253924156866553893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43458104041857673243241525 4074197253924156866553893)
      ·
        refine ⟨763911985110779412478855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4074197253924156866553893 763911985110779412478855)
        ·
          refine ⟨1145867977666169118718283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 763911985110779412478855 1145867977666169118718283)
          ·
            refine ⟨1718801966499253678077425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1145867977666169118718283 1718801966499253678077425)
            ·
              refine ⟨1289101474874440258558069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1718801966499253678077425 1289101474874440258558069)
              ·
                refine ⟨120853263269478774239819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1289101474874440258558069 120853263269478774239819)
                ·
                  rfl

theorem cell20_794343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 5].length) (baseStart_794343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794343 prefixEnd_794343 := by exact prefixLift 794343
  have htrace : WordTrace (prefixWord ++ tailWord_794343) baseStart_794343 baseEnd_794343 := by
    simpa [prefixWord, tailWord_794343, baseEnd_794343] using wordTrace_append hprefix tailTrace_794343
  have hstable : (prefixWord ++ tailWord_794343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794343).length < 2 ^ (prefixWord ++ tailWord_794343).sum := by decide
  have hdescent : baseEnd_794343 < baseStart_794343 := by decide
  rcases family_descends (prefixWord ++ tailWord_794343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794391 : List Nat := [1, 1, 3, 4, 2, 3, 2, 2, 2]
def baseStart_794391 : Nat := 118140960795 + 794391 * 2 ^ 59
def prefixEnd_794391 : Nat := 4983230072969 + 3 ^ 40 * 794391 * 2
def baseEnd_794391 : Nat := 362581698316361489119261

theorem tailTrace_794391 : CollatzResearch.WordTrace tailWord_794391 prefixEnd_794391 362581698316361489119261 := by
  unfold tailWord_794391
  simp only [CollatzResearch.WordTrace]
  refine ⟨28973820065064553026575027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19315880043376368684383351 28973820065064553026575027)
  ·
    refine ⟨43460730097596829539862541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28973820065064553026575027 43460730097596829539862541)
    ·
      refine ⟨16297773786598811077448453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43460730097596829539862541 16297773786598811077448453)
      ·
        refine ⟨3055832584987277077021585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16297773786598811077448453 3055832584987277077021585)
        ·
          refine ⟨2291874438740457807766189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3055832584987277077021585 2291874438740457807766189)
          ·
            refine ⟨859452914527671677912321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2291874438740457807766189 859452914527671677912321)
            ·
              refine ⟨644589685895753758434241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 859452914527671677912321 644589685895753758434241)
              ·
                refine ⟨483442264421815318825681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 644589685895753758434241 483442264421815318825681)
                ·
                  refine ⟨362581698316361489119261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483442264421815318825681 362581698316361489119261)
                  ·
                    rfl

theorem cell20_794391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 2].length) (baseStart_794391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794391 prefixEnd_794391 := by exact prefixLift 794391
  have htrace : WordTrace (prefixWord ++ tailWord_794391) baseStart_794391 baseEnd_794391 := by
    simpa [prefixWord, tailWord_794391, baseEnd_794391] using wordTrace_append hprefix tailTrace_794391
  have hstable : (prefixWord ++ tailWord_794391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794391).length < 2 ^ (prefixWord ++ tailWord_794391).sum := by decide
  have hdescent : baseEnd_794391 < baseStart_794391 := by decide
  rcases family_descends (prefixWord ++ tailWord_794391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794392 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 5]
def baseStart_794392 : Nat := 118140960795 + 794392 * 2 ^ 59
def prefixEnd_794392 : Nat := 4983230072969 + 3 ^ 40 * 794392 * 2
def baseEnd_794392 : Nat := 362582154743609930085923

theorem tailTrace_794392 : CollatzResearch.WordTrace tailWord_794392 prefixEnd_794392 362582154743609930085923 := by
  unfold tailWord_794392
  simp only [CollatzResearch.WordTrace]
  refine ⟨14486928269030465098680715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19315904358707286798240953 14486928269030465098680715)
  ·
    refine ⟨21730392403545697648021073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14486928269030465098680715 21730392403545697648021073)
    ·
      refine ⟨16297794302659273236015805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21730392403545697648021073 16297794302659273236015805)
      ·
        refine ⟨6111672863497227463505927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16297794302659273236015805 6111672863497227463505927)
        ·
          refine ⟨9167509295245841195258891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6111672863497227463505927 9167509295245841195258891)
          ·
            refine ⟨13751263942868761792888337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9167509295245841195258891 13751263942868761792888337)
            ·
              refine ⟨10313447957151571344666253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13751263942868761792888337 10313447957151571344666253)
              ·
                refine ⟨3867542983931839254249845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10313447957151571344666253 3867542983931839254249845)
                ·
                  refine ⟨362582154743609930085923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3867542983931839254249845 362582154743609930085923)
                  ·
                    rfl

theorem cell20_794392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_794392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794392 prefixEnd_794392 := by exact prefixLift 794392
  have htrace : WordTrace (prefixWord ++ tailWord_794392) baseStart_794392 baseEnd_794392 := by
    simpa [prefixWord, tailWord_794392, baseEnd_794392] using wordTrace_append hprefix tailTrace_794392
  have hstable : (prefixWord ++ tailWord_794392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794392).length < 2 ^ (prefixWord ++ tailWord_794392).sum := by decide
  have hdescent : baseEnd_794392 < baseStart_794392 := by decide
  rcases family_descends (prefixWord ++ tailWord_794392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794437 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 6]
def baseStart_794437 : Nat := 118140960795 + 794437 * 2 ^ 59
def prefixEnd_794437 : Nat := 4983230072969 + 3 ^ 40 * 794437 * 2
def baseEnd_794437 : Nat := 362602693969789773585739

theorem tailTrace_794437 : CollatzResearch.WordTrace tailWord_794437 prefixEnd_794437 362602693969789773585739 := by
  unfold tailWord_794437
  simp only [CollatzResearch.WordTrace]
  refine ⟨28975497822897902882749565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19316998548598601921833043 28975497822897902882749565)
  ·
    refine ⟨10865811683586713581031087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28975497822897902882749565 10865811683586713581031087)
    ·
      refine ⟨16298717525380070371546631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10865811683586713581031087 16298717525380070371546631)
      ·
        refine ⟨24448076288070105557319947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16298717525380070371546631 24448076288070105557319947)
        ·
          refine ⟨36672114432105158335979921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24448076288070105557319947 36672114432105158335979921)
          ·
            refine ⟨27504085824078868751984941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36672114432105158335979921 27504085824078868751984941)
            ·
              refine ⟨10314032184029575781994353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27504085824078868751984941 10314032184029575781994353)
              ·
                refine ⟨7735524138022181836495765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10314032184029575781994353 7735524138022181836495765)
                ·
                  refine ⟨362602693969789773585739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7735524138022181836495765 362602693969789773585739)
                  ·
                    rfl

theorem cell20_794437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_794437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794437 prefixEnd_794437 := by exact prefixLift 794437
  have htrace : WordTrace (prefixWord ++ tailWord_794437) baseStart_794437 baseEnd_794437 := by
    simpa [prefixWord, tailWord_794437, baseEnd_794437] using wordTrace_append hprefix tailTrace_794437
  have hstable : (prefixWord ++ tailWord_794437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794437).length < 2 ^ (prefixWord ++ tailWord_794437).sum := by decide
  have hdescent : baseEnd_794437 < baseStart_794437 := by decide
  rcases family_descends (prefixWord ++ tailWord_794437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794464 : List Nat := [2, 1, 1, 3, 3, 3, 3, 1, 3]
def baseStart_794464 : Nat := 118140960795 + 794464 * 2 ^ 59
def prefixEnd_794464 : Nat := 4983230072969 + 3 ^ 40 * 794464 * 2
def baseEnd_794464 : Nat := 362615017505497679685629

theorem tailTrace_794464 : CollatzResearch.WordTrace tailWord_794464 prefixEnd_794464 362615017505497679685629 := by
  unfold tailWord_794464
  simp only [CollatzResearch.WordTrace]
  refine ⟨14488241296900043246991223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19317655062533390995988297 14488241296900043246991223)
  ·
    refine ⟨21732361945350064870486835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14488241296900043246991223 21732361945350064870486835)
    ·
      refine ⟨32598542918025097305730253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21732361945350064870486835 32598542918025097305730253)
      ·
        refine ⟨12224453594259411489648845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32598542918025097305730253 12224453594259411489648845)
        ·
          refine ⟨4584170097847279308618317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12224453594259411489648845 4584170097847279308618317)
          ·
            refine ⟨1719063786692729740731869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4584170097847279308618317 1719063786692729740731869)
            ·
              refine ⟨644648920009773652774451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1719063786692729740731869 644648920009773652774451)
              ·
                refine ⟨966973380014660479161677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644648920009773652774451 966973380014660479161677)
                ·
                  refine ⟨362615017505497679685629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 966973380014660479161677 362615017505497679685629)
                  ·
                    rfl

theorem cell20_794464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 3].length) (baseStart_794464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794464 prefixEnd_794464 := by exact prefixLift 794464
  have htrace : WordTrace (prefixWord ++ tailWord_794464) baseStart_794464 baseEnd_794464 := by
    simpa [prefixWord, tailWord_794464, baseEnd_794464] using wordTrace_append hprefix tailTrace_794464
  have hstable : (prefixWord ++ tailWord_794464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794464).length < 2 ^ (prefixWord ++ tailWord_794464).sum := by decide
  have hdescent : baseEnd_794464 < baseStart_794464 := by decide
  rcases family_descends (prefixWord ++ tailWord_794464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794474 : List Nat := [3, 1, 3, 4, 1, 2, 2, 4]
def baseStart_794474 : Nat := 118140960795 + 794474 * 2 ^ 59
def prefixEnd_794474 : Nat := 4983230072969 + 3 ^ 40 * 794474 * 2
def baseEnd_794474 : Nat := 120873193925994029784085

theorem tailTrace_794474 : CollatzResearch.WordTrace tailWord_794474 prefixEnd_794474 120873193925994029784085 := by
  unfold tailWord_794474
  simp only [CollatzResearch.WordTrace]
  refine ⟨7244211830940964550461619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19317898215842572134564317 7244211830940964550461619)
  ·
    refine ⟨10866317746411446825692429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7244211830940964550461619 10866317746411446825692429)
    ·
      refine ⟨4074869154904292559634661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10866317746411446825692429 4074869154904292559634661)
      ·
        refine ⟨764037966544554854931499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4074869154904292559634661 764037966544554854931499)
        ·
          refine ⟨1146056949816832282397249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764037966544554854931499 1146056949816832282397249)
          ·
            refine ⟨859542712362624211797937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1146056949816832282397249 859542712362624211797937)
            ·
              refine ⟨644657034271968158848453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 859542712362624211797937 644657034271968158848453)
              ·
                refine ⟨120873193925994029784085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 644657034271968158848453 120873193925994029784085)
                ·
                  rfl

theorem cell20_794474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_794474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794474 prefixEnd_794474 := by exact prefixLift 794474
  have htrace : WordTrace (prefixWord ++ tailWord_794474) baseStart_794474 baseEnd_794474 := by
    simpa [prefixWord, tailWord_794474, baseEnd_794474] using wordTrace_append hprefix tailTrace_794474
  have hstable : (prefixWord ++ tailWord_794474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794474).length < 2 ^ (prefixWord ++ tailWord_794474).sum := by decide
  have hdescent : baseEnd_794474 < baseStart_794474 := by decide
  rcases family_descends (prefixWord ++ tailWord_794474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794478 : List Nat := [4, 1, 2, 3, 1, 2, 1, 6]
def baseStart_794478 : Nat := 118140960795 + 794478 * 2 ^ 59
def prefixEnd_794478 : Nat := 4983230072969 + 3 ^ 40 * 794478 * 2
def baseEnd_794478 : Nat := 120873802495658617739635

theorem tailTrace_794478 : CollatzResearch.WordTrace tailWord_794478 prefixEnd_794478 120873802495658617739635 := by
  unfold tailWord_794478
  simp only [CollatzResearch.WordTrace]
  refine ⟨3622124151968670860624011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19317995477166244589994725 3622124151968670860624011)
  ·
    refine ⟨5433186227953006290936017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3622124151968670860624011 5433186227953006290936017)
    ·
      refine ⟨4074889670964754718202013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5433186227953006290936017 4074889670964754718202013)
      ·
        refine ⟨1528083626611783019325755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4074889670964754718202013 1528083626611783019325755)
        ·
          refine ⟨2292125439917674528988633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1528083626611783019325755 2292125439917674528988633)
          ·
            refine ⟨1719094079938255896741475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2292125439917674528988633 1719094079938255896741475)
            ·
              refine ⟨2578641119907383845112213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1719094079938255896741475 2578641119907383845112213)
              ·
                refine ⟨120873802495658617739635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2578641119907383845112213 120873802495658617739635)
                ·
                  rfl

theorem cell20_794478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_794478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794478 prefixEnd_794478 := by exact prefixLift 794478
  have htrace : WordTrace (prefixWord ++ tailWord_794478) baseStart_794478 baseEnd_794478 := by
    simpa [prefixWord, tailWord_794478, baseEnd_794478] using wordTrace_append hprefix tailTrace_794478
  have hstable : (prefixWord ++ tailWord_794478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794478).length < 2 ^ (prefixWord ++ tailWord_794478).sum := by decide
  have hdescent : baseEnd_794478 < baseStart_794478 := by decide
  rcases family_descends (prefixWord ++ tailWord_794478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794499 : List Nat := [1, 1, 1, 3, 4, 4, 6]
def baseStart_794499 : Nat := 118140960795 + 794499 * 2 ^ 59
def prefixEnd_794499 : Nat := 4983230072969 + 3 ^ 40 * 794499 * 2
def baseEnd_794499 : Nat := 40292332495465901502091

theorem tailTrace_794499 : CollatzResearch.WordTrace tailWord_794499 prefixEnd_794499 40292332495465901502091 := by
  unfold tailWord_794499
  simp only [CollatzResearch.WordTrace]
  refine ⟨28977759148673287471506551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19318506099115524981004367 28977759148673287471506551)
  ·
    refine ⟨43466638723009931207259827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28977759148673287471506551 43466638723009931207259827)
    ·
      refine ⟨65199958084514896810889741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43466638723009931207259827 65199958084514896810889741)
      ·
        refine ⟨24449984281693086304083653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65199958084514896810889741 24449984281693086304083653)
        ·
          refine ⟨4584372052817453682015685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24449984281693086304083653 4584372052817453682015685)
          ·
            refine ⟨859569759903272565377941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4584372052817453682015685 859569759903272565377941)
            ·
              refine ⟨40292332495465901502091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 859569759903272565377941 40292332495465901502091)
              ·
                rfl

theorem cell20_794499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 6].length) (baseStart_794499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794499 prefixEnd_794499 := by exact prefixLift 794499
  have htrace : WordTrace (prefixWord ++ tailWord_794499) baseStart_794499 baseEnd_794499 := by
    simpa [prefixWord, tailWord_794499, baseEnd_794499] using wordTrace_append hprefix tailTrace_794499
  have hstable : (prefixWord ++ tailWord_794499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794499).length < 2 ^ (prefixWord ++ tailWord_794499).sum := by decide
  have hdescent : baseEnd_794499 < baseStart_794499 := by decide
  rcases family_descends (prefixWord ++ tailWord_794499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794516 : List Nat := [2, 4, 2, 1, 1, 3, 2, 5]
def baseStart_794516 : Nat := 118140960795 + 794516 * 2 ^ 59
def prefixEnd_794516 : Nat := 4983230072969 + 3 ^ 40 * 794516 * 2
def baseEnd_794516 : Nat := 120879583907472203317361

theorem tailTrace_794516 : CollatzResearch.WordTrace tailWord_794516 prefixEnd_794516 120879583907472203317361 := by
  unfold tailWord_794516
  simp only [CollatzResearch.WordTrace]
  refine ⟨14489189594805849687437701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19318919459741132916583601 14489189594805849687437701)
  ·
    refine ⟨2716723049026096816394569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14489189594805849687437701 2716723049026096816394569)
    ·
      refine ⟨2037542286769572612295927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2716723049026096816394569 2037542286769572612295927)
      ·
        refine ⟨3056313430154358918443891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2037542286769572612295927 3056313430154358918443891)
        ·
          refine ⟨4584470145231538377665837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3056313430154358918443891 4584470145231538377665837)
          ·
            refine ⟨1719176304461826891624689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4584470145231538377665837 1719176304461826891624689)
            ·
              refine ⟨1289382228346370168718517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1719176304461826891624689 1289382228346370168718517)
              ·
                refine ⟨120879583907472203317361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1289382228346370168718517 120879583907472203317361)
                ·
                  rfl

theorem cell20_794516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_794516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794516 prefixEnd_794516 := by exact prefixLift 794516
  have htrace : WordTrace (prefixWord ++ tailWord_794516) baseStart_794516 baseEnd_794516 := by
    simpa [prefixWord, tailWord_794516, baseEnd_794516] using wordTrace_append hprefix tailTrace_794516
  have hstable : (prefixWord ++ tailWord_794516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794516).length < 2 ^ (prefixWord ++ tailWord_794516).sum := by decide
  have hdescent : baseEnd_794516 < baseStart_794516 := by decide
  rcases family_descends (prefixWord ++ tailWord_794516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794620 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 5]
def baseStart_794620 : Nat := 118140960795 + 794620 * 2 ^ 59
def prefixEnd_794620 : Nat := 4983230072969 + 3 ^ 40 * 794620 * 2
def baseEnd_794620 : Nat := 362686220156254470484991

theorem tailTrace_794620 : CollatzResearch.WordTrace tailWord_794620 prefixEnd_794620 362686220156254470484991 := by
  unfold tailWord_794620
  simp only [CollatzResearch.WordTrace]
  refine ⟨14491086190617462568330657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19321448254156616757774209 14491086190617462568330657)
  ·
    refine ⟨10868314642963096926247993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14491086190617462568330657 10868314642963096926247993)
    ·
      refine ⟨8151235982222322694685995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10868314642963096926247993 8151235982222322694685995)
      ·
        refine ⟨12226853973333484042028993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8151235982222322694685995 12226853973333484042028993)
        ·
          refine ⟨9170140480000113031521745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12226853973333484042028993 9170140480000113031521745)
          ·
            refine ⟨6877605360000084773641309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9170140480000113031521745 6877605360000084773641309)
            ·
              refine ⟨2579102010000031790115491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6877605360000084773641309 2579102010000031790115491)
              ·
                refine ⟨3868653015000047685173237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2579102010000031790115491 3868653015000047685173237)
                ·
                  refine ⟨362686220156254470484991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3868653015000047685173237 362686220156254470484991)
                  ·
                    rfl

theorem cell20_794620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_794620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794620 prefixEnd_794620 := by exact prefixLift 794620
  have htrace : WordTrace (prefixWord ++ tailWord_794620) baseStart_794620 baseEnd_794620 := by
    simpa [prefixWord, tailWord_794620, baseEnd_794620] using wordTrace_append hprefix tailTrace_794620
  have hstable : (prefixWord ++ tailWord_794620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794620).length < 2 ^ (prefixWord ++ tailWord_794620).sum := by decide
  have hdescent : baseEnd_794620 < baseStart_794620 := by decide
  rcases family_descends (prefixWord ++ tailWord_794620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794647 : List Nat := [1, 1, 3, 5, 2, 2, 2, 4]
def baseStart_794647 : Nat := 118140960795 + 794647 * 2 ^ 59
def prefixEnd_794647 : Nat := 4983230072969 + 3 ^ 40 * 794647 * 2
def baseEnd_794647 : Nat := 120899514563987458861627

theorem tailTrace_794647 : CollatzResearch.WordTrace tailWord_794647 prefixEnd_794647 120899514563987458861627 := by
  unfold tailWord_794647
  simp only [CollatzResearch.WordTrace]
  refine ⟨28983157152137108747894195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19322104768091405831929463 28983157152137108747894195)
  ·
    refine ⟨43474735728205663121841293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28983157152137108747894195 43474735728205663121841293)
    ·
      refine ⟨16303025898077123670690485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43474735728205663121841293 16303025898077123670690485)
      ·
        refine ⟨1528408677944730344127233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16303025898077123670690485 1528408677944730344127233)
        ·
          refine ⟨1146306508458547758095425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1528408677944730344127233 1146306508458547758095425)
          ·
            refine ⟨859729881343910818571569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1146306508458547758095425 859729881343910818571569)
            ·
              refine ⟨644797411007933113928677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 859729881343910818571569 644797411007933113928677)
              ·
                refine ⟨120899514563987458861627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 644797411007933113928677 120899514563987458861627)
                ·
                  rfl

theorem cell20_794647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 4].length) (baseStart_794647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794647 prefixEnd_794647 := by exact prefixLift 794647
  have htrace : WordTrace (prefixWord ++ tailWord_794647) baseStart_794647 baseEnd_794647 := by
    simpa [prefixWord, tailWord_794647, baseEnd_794647] using wordTrace_append hprefix tailTrace_794647
  have hstable : (prefixWord ++ tailWord_794647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794647).length < 2 ^ (prefixWord ++ tailWord_794647).sum := by decide
  have hdescent : baseEnd_794647 < baseStart_794647 := by decide
  rcases family_descends (prefixWord ++ tailWord_794647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794657 : List Nat := [1, 2, 3, 2, 5, 1, 1, 3, 2]
def baseStart_794657 : Nat := 118140960795 + 794657 * 2 ^ 59
def prefixEnd_794657 : Nat := 4983230072969 + 3 ^ 40 * 794657 * 2
def baseEnd_794657 : Nat := 362703107964446786251507

theorem tailTrace_794657 : CollatzResearch.WordTrace tailWord_794657 prefixEnd_794657 362703107964446786251507 := by
  unfold tailWord_794657
  simp only [CollatzResearch.WordTrace]
  refine ⟨28983521882100880455758225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19322347921400586970505483 28983521882100880455758225)
  ·
    refine ⟨21737641411575660341818669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28983521882100880455758225 21737641411575660341818669)
    ·
      refine ⟨8151615529340872628182001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21737641411575660341818669 8151615529340872628182001)
      ·
        refine ⟨6113711647005654471136501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8151615529340872628182001 6113711647005654471136501)
        ·
          refine ⟨573160466906780106669047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6113711647005654471136501 573160466906780106669047)
          ·
            refine ⟨859740700360170160003571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573160466906780106669047 859740700360170160003571)
            ·
              refine ⟨1289611050540255240005357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859740700360170160003571 1289611050540255240005357)
              ·
                refine ⟨483604143952595715002009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1289611050540255240005357 483604143952595715002009)
                ·
                  refine ⟨362703107964446786251507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483604143952595715002009 362703107964446786251507)
                  ·
                    rfl

theorem cell20_794657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 2].length) (baseStart_794657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794657 prefixEnd_794657 := by exact prefixLift 794657
  have htrace : WordTrace (prefixWord ++ tailWord_794657) baseStart_794657 baseEnd_794657 := by
    simpa [prefixWord, tailWord_794657, baseEnd_794657] using wordTrace_append hprefix tailTrace_794657
  have hstable : (prefixWord ++ tailWord_794657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794657).length < 2 ^ (prefixWord ++ tailWord_794657).sum := by decide
  have hdescent : baseEnd_794657 < baseStart_794657 := by decide
  rcases family_descends (prefixWord ++ tailWord_794657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794658 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_794658 : Nat := 118140960795 + 794658 * 2 ^ 59
def prefixEnd_794658 : Nat := 4983230072969 + 3 ^ 40 * 794658 * 2
def baseEnd_794658 : Nat := 362703564391695227218169

theorem tailTrace_794658 : CollatzResearch.WordTrace tailWord_794658 prefixEnd_794658 362703564391695227218169 := by
  unfold tailWord_794658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7245889588774314406636157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19322372236731505084363085 7245889588774314406636157)
  ·
    refine ⟨2717208595790367902488559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7245889588774314406636157 2717208595790367902488559)
    ·
      refine ⟨4075812893685551853732839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2717208595790367902488559 4075812893685551853732839)
      ·
        refine ⟨6113719340528327780599259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4075812893685551853732839 6113719340528327780599259)
        ·
          refine ⟨9170579010792491670898889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6113719340528327780599259 9170579010792491670898889)
          ·
            refine ⟨6877934258094368753174167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9170579010792491670898889 6877934258094368753174167)
            ·
              refine ⟨10316901387141553129761251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6877934258094368753174167 10316901387141553129761251)
              ·
                refine ⟨15475352080712329694641877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10316901387141553129761251 15475352080712329694641877)
                ·
                  refine ⟨362703564391695227218169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15475352080712329694641877 362703564391695227218169)
                  ·
                    rfl

theorem cell20_794658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_794658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794658 prefixEnd_794658 := by exact prefixLift 794658
  have htrace : WordTrace (prefixWord ++ tailWord_794658) baseStart_794658 baseEnd_794658 := by
    simpa [prefixWord, tailWord_794658, baseEnd_794658] using wordTrace_append hprefix tailTrace_794658
  have hstable : (prefixWord ++ tailWord_794658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794658).length < 2 ^ (prefixWord ++ tailWord_794658).sum := by decide
  have hdescent : baseEnd_794658 < baseStart_794658 := by decide
  rcases family_descends (prefixWord ++ tailWord_794658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794661 : List Nat := [1, 3, 1, 2, 2, 3, 3, 3, 2]
def baseStart_794661 : Nat := 118140960795 + 794661 * 2 ^ 59
def prefixEnd_794661 : Nat := 4983230072969 + 3 ^ 40 * 794661 * 2
def baseEnd_794661 : Nat := 362704933673440550118157

theorem tailTrace_794661 : CollatzResearch.WordTrace tailWord_794661 prefixEnd_794661 362704933673440550118157 := by
  unfold tailWord_794661
  simp only [CollatzResearch.WordTrace]
  refine ⟨28983667774086389138903837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19322445182724259425935891 28983667774086389138903837)
  ·
    refine ⟨10868875415282395927088939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28983667774086389138903837 10868875415282395927088939)
    ·
      refine ⟨16303313122923593890633409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10868875415282395927088939 16303313122923593890633409)
      ·
        refine ⟨12227484842192695417975057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16303313122923593890633409 12227484842192695417975057)
        ·
          refine ⟨9170613631644521563481293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12227484842192695417975057 9170613631644521563481293)
          ·
            refine ⟨3438980111866695586305485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9170613631644521563481293 3438980111866695586305485)
            ·
              refine ⟨1289617541950010844864557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3438980111866695586305485 1289617541950010844864557)
              ·
                refine ⟨483606578231254066824209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1289617541950010844864557 483606578231254066824209)
                ·
                  refine ⟨362704933673440550118157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483606578231254066824209 362704933673440550118157)
                  ·
                    rfl

theorem cell20_794661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_794661 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794661 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794661 prefixEnd_794661 := by exact prefixLift 794661
  have htrace : WordTrace (prefixWord ++ tailWord_794661) baseStart_794661 baseEnd_794661 := by
    simpa [prefixWord, tailWord_794661, baseEnd_794661] using wordTrace_append hprefix tailTrace_794661
  have hstable : (prefixWord ++ tailWord_794661).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794661).length < 2 ^ (prefixWord ++ tailWord_794661).sum := by decide
  have hdescent : baseEnd_794661 < baseStart_794661 := by decide
  rcases family_descends (prefixWord ++ tailWord_794661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794672 : List Nat := [2, 1, 1, 1, 2, 5, 8]
def baseStart_794672 : Nat := 118140960795 + 794672 * 2 ^ 59
def prefixEnd_794672 : Nat := 4983230072969 + 3 ^ 40 * 794672 * 2
def baseEnd_794672 : Nat := 40301106041463711194605

theorem tailTrace_794672 : CollatzResearch.WordTrace tailWord_794672 prefixEnd_794672 40301106041463711194605 := by
  unfold tailWord_794672
  simp only [CollatzResearch.WordTrace]
  refine ⟨14492034488523269008777135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19322712651364358678369513 14492034488523269008777135)
  ·
    refine ⟨21738051732784903513165703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14492034488523269008777135 21738051732784903513165703)
    ·
      refine ⟨32607077599177355269748555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21738051732784903513165703 32607077599177355269748555)
      ·
        refine ⟨48910616398766032904622833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32607077599177355269748555 48910616398766032904622833)
        ·
          refine ⟨36682962299074524678467125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48910616398766032904622833 36682962299074524678467125)
          ·
            refine ⟨3439027715538236688606293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36682962299074524678467125 3439027715538236688606293)
            ·
              refine ⟨40301106041463711194605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3439027715538236688606293 40301106041463711194605)
              ·
                rfl

theorem cell20_794672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 8].length) (baseStart_794672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794672 prefixEnd_794672 := by exact prefixLift 794672
  have htrace : WordTrace (prefixWord ++ tailWord_794672) baseStart_794672 baseEnd_794672 := by
    simpa [prefixWord, tailWord_794672, baseEnd_794672] using wordTrace_append hprefix tailTrace_794672
  have hstable : (prefixWord ++ tailWord_794672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794672).length < 2 ^ (prefixWord ++ tailWord_794672).sum := by decide
  have hdescent : baseEnd_794672 < baseStart_794672 := by decide
  rcases family_descends (prefixWord ++ tailWord_794672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794689 : List Nat := [1, 2, 5, 1, 2, 1, 1, 7]
def baseStart_794689 : Nat := 118140960795 + 794689 * 2 ^ 59
def prefixEnd_794689 : Nat := 4983230072969 + 3 ^ 40 * 794689 * 2
def baseEnd_794689 : Nat := 120905904545465632394903

theorem tailTrace_794689 : CollatzResearch.WordTrace tailWord_794689 prefixEnd_794689 120905904545465632394903 := by
  unfold tailWord_794689
  simp only [CollatzResearch.WordTrace]
  refine ⟨28984689017984949920923121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19323126011989966613948747 28984689017984949920923121)
  ·
    refine ⟨21738516763488712440692341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28984689017984949920923121 21738516763488712440692341)
    ·
      refine ⟨2037985946577066791314907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21738516763488712440692341 2037985946577066791314907)
      ·
        refine ⟨3056978919865600186972361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2037985946577066791314907 3056978919865600186972361)
        ·
          refine ⟨2292734189899200140229271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3056978919865600186972361 2292734189899200140229271)
          ·
            refine ⟨3439101284848800210343907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2292734189899200140229271 3439101284848800210343907)
            ·
              refine ⟨5158651927273200315515861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3439101284848800210343907 5158651927273200315515861)
              ·
                refine ⟨120905904545465632394903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5158651927273200315515861 120905904545465632394903)
                ·
                  rfl

theorem cell20_794689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 7].length) (baseStart_794689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794689 prefixEnd_794689 := by exact prefixLift 794689
  have htrace : WordTrace (prefixWord ++ tailWord_794689) baseStart_794689 baseEnd_794689 := by
    simpa [prefixWord, tailWord_794689, baseEnd_794689] using wordTrace_append hprefix tailTrace_794689
  have hstable : (prefixWord ++ tailWord_794689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794689).length < 2 ^ (prefixWord ++ tailWord_794689).sum := by decide
  have hdescent : baseEnd_794689 < baseStart_794689 := by decide
  rcases family_descends (prefixWord ++ tailWord_794689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794730 : List Nat := [3, 1, 3, 2, 3, 1, 2, 2, 3]
def baseStart_794730 : Nat := 118140960795 + 794730 * 2 ^ 59
def prefixEnd_794730 : Nat := 4983230072969 + 3 ^ 40 * 794730 * 2
def baseEnd_794730 : Nat := 362736427153582976817875

theorem tailTrace_794730 : CollatzResearch.WordTrace tailWord_794730 prefixEnd_794730 362736427153582976817875 := by
  unfold tailWord_794730
  simp only [CollatzResearch.WordTrace]
  refine ⟨7246546102709103480791411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19324122940557609282110429 7246546102709103480791411)
  ·
    refine ⟨10869819154063655221187117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7246546102709103480791411 10869819154063655221187117)
    ·
      refine ⟨4076182182773870707945169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10869819154063655221187117 4076182182773870707945169)
      ·
        refine ⟨3057136637080403030958877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4076182182773870707945169 3057136637080403030958877)
        ·
          refine ⟨1146426238905151136609579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3057136637080403030958877 1146426238905151136609579)
          ·
            refine ⟨1719639358357726704914369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146426238905151136609579 1719639358357726704914369)
            ·
              refine ⟨1289729518768295028685777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1719639358357726704914369 1289729518768295028685777)
              ·
                refine ⟨967297139076221271514333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1289729518768295028685777 967297139076221271514333)
                ·
                  refine ⟨362736427153582976817875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 967297139076221271514333 362736427153582976817875)
                  ·
                    rfl

theorem cell20_794730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_794730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794730 prefixEnd_794730 := by exact prefixLift 794730
  have htrace : WordTrace (prefixWord ++ tailWord_794730) baseStart_794730 baseEnd_794730 := by
    simpa [prefixWord, tailWord_794730, baseEnd_794730] using wordTrace_append hprefix tailTrace_794730
  have hstable : (prefixWord ++ tailWord_794730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794730).length < 2 ^ (prefixWord ++ tailWord_794730).sum := by decide
  have hdescent : baseEnd_794730 < baseStart_794730 := by decide
  rcases family_descends (prefixWord ++ tailWord_794730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794782 : List Nat := [4, 3, 1, 1, 3, 1, 7]
def baseStart_794782 : Nat := 118140960795 + 794782 * 2 ^ 59
def prefixEnd_794782 : Nat := 4983230072969 + 3 ^ 40 * 794782 * 2
def baseEnd_794782 : Nat := 40306684596722434120481

theorem tailTrace_794782 : CollatzResearch.WordTrace tailWord_794782 prefixEnd_794782 40306684596722434120481 := by
  unfold tailWord_794782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3623510125831003350507325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19325387337765351202705733 3623510125831003350507325)
  ·
    refine ⟨1358816297186626256440247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3623510125831003350507325 1358816297186626256440247)
    ·
      refine ⟨2038224445779939384660371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1358816297186626256440247 2038224445779939384660371)
      ·
        refine ⟨3057336668669909076990557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2038224445779939384660371 3057336668669909076990557)
        ·
          refine ⟨1146501250751215903871459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3057336668669909076990557 1146501250751215903871459)
          ·
            refine ⟨1719751876126823855807189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146501250751215903871459 1719751876126823855807189)
            ·
              refine ⟨40306684596722434120481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1719751876126823855807189 40306684596722434120481)
              ·
                rfl

theorem cell20_794782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 7].length) (baseStart_794782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794782 prefixEnd_794782 := by exact prefixLift 794782
  have htrace : WordTrace (prefixWord ++ tailWord_794782) baseStart_794782 baseEnd_794782 := by
    simpa [prefixWord, tailWord_794782, baseEnd_794782] using wordTrace_append hprefix tailTrace_794782
  have hstable : (prefixWord ++ tailWord_794782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794782).length < 2 ^ (prefixWord ++ tailWord_794782).sum := by decide
  have hdescent : baseEnd_794782 < baseStart_794782 := by decide
  rcases family_descends (prefixWord ++ tailWord_794782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794810 : List Nat := [3, 1, 1, 1, 2, 2, 2, 5, 3]
def baseStart_794810 : Nat := 118140960795 + 794810 * 2 ^ 59
def prefixEnd_794810 : Nat := 4983230072969 + 3 ^ 40 * 794810 * 2
def baseEnd_794810 : Nat := 362772941333458254150881

theorem tailTrace_794810 : CollatzResearch.WordTrace tailWord_794810 prefixEnd_794810 362772941333458254150881 := by
  unfold tailWord_794810
  simp only [CollatzResearch.WordTrace]
  refine ⟨7247275562636646896519471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19326068167031058390718589 7247275562636646896519471)
  ·
    refine ⟨10870913343954970344779207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7247275562636646896519471 10870913343954970344779207)
    ·
      refine ⟨16306370015932455517168811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10870913343954970344779207 16306370015932455517168811)
      ·
        refine ⟨24459555023898683275753217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16306370015932455517168811 24459555023898683275753217)
        ·
          refine ⟨18344666267924012456814913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24459555023898683275753217 18344666267924012456814913)
          ·
            refine ⟨13758499700943009342611185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18344666267924012456814913 13758499700943009342611185)
            ·
              refine ⟨10318874775707257006958389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13758499700943009342611185 10318874775707257006958389)
              ·
                refine ⟨967394510222555344402349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10318874775707257006958389 967394510222555344402349)
                ·
                  refine ⟨362772941333458254150881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 967394510222555344402349 362772941333458254150881)
                  ·
                    rfl

theorem cell20_794810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_794810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794810 prefixEnd_794810 := by exact prefixLift 794810
  have htrace : WordTrace (prefixWord ++ tailWord_794810) baseStart_794810 baseEnd_794810 := by
    simpa [prefixWord, tailWord_794810, baseEnd_794810] using wordTrace_append hprefix tailTrace_794810
  have hstable : (prefixWord ++ tailWord_794810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794810).length < 2 ^ (prefixWord ++ tailWord_794810).sum := by decide
  have hdescent : baseEnd_794810 < baseStart_794810 := by decide
  rcases family_descends (prefixWord ++ tailWord_794810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794820 : List Nat := [2, 3, 3, 1, 2, 1, 4, 4]
def baseStart_794820 : Nat := 118140960795 + 794820 * 2 ^ 59
def prefixEnd_794820 : Nat := 4983230072969 + 3 ^ 40 * 794820 * 2
def baseEnd_794820 : Nat := 120925835201980887939169

theorem tailTrace_794820 : CollatzResearch.WordTrace tailWord_794820 prefixEnd_794820 120925835201980887939169 := by
  unfold tailWord_794820
  simp only [CollatzResearch.WordTrace]
  refine ⟨14494733490255179646970957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19326311320340239529294609 14494733490255179646970957)
  ·
    refine ⟨5435525058845692367614109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14494733490255179646970957 5435525058845692367614109)
    ·
      refine ⟨2038321897067134637855291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5435525058845692367614109 2038321897067134637855291)
      ·
        refine ⟨3057482845600701956782937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2038321897067134637855291 3057482845600701956782937)
        ·
          refine ⟨2293112134200526467587203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3057482845600701956782937 2293112134200526467587203)
          ·
            refine ⟨3439668201300789701380805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2293112134200526467587203 3439668201300789701380805)
            ·
              refine ⟨644937787743898069008901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3439668201300789701380805 644937787743898069008901)
              ·
                refine ⟨120925835201980887939169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 644937787743898069008901 120925835201980887939169)
                ·
                  rfl

theorem cell20_794820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_794820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794820 prefixEnd_794820 := by exact prefixLift 794820
  have htrace : WordTrace (prefixWord ++ tailWord_794820) baseStart_794820 baseEnd_794820 := by
    simpa [prefixWord, tailWord_794820, baseEnd_794820] using wordTrace_append hprefix tailTrace_794820
  have hstable : (prefixWord ++ tailWord_794820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794820).length < 2 ^ (prefixWord ++ tailWord_794820).sum := by decide
  have hdescent : baseEnd_794820 < baseStart_794820 := by decide
  rcases family_descends (prefixWord ++ tailWord_794820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794830 : List Nat := [4, 1, 1, 1, 4, 3, 1, 3, 2]
def baseStart_794830 : Nat := 118140960795 + 794830 * 2 ^ 59
def prefixEnd_794830 : Nat := 4983230072969 + 3 ^ 40 * 794830 * 2
def baseEnd_794830 : Nat := 362782069878427073484133

theorem tailTrace_794830 : CollatzResearch.WordTrace tailWord_794830 prefixEnd_794830 362782069878427073484133 := by
  unfold tailWord_794830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3623728963809266375225743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19326554473649420667870629 3623728963809266375225743)
  ·
    refine ⟨5435593445713899562838615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3623728963809266375225743 5435593445713899562838615)
    ·
      refine ⟨8153390168570849344257923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5435593445713899562838615 8153390168570849344257923)
      ·
        refine ⟨12230085252856274016386885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8153390168570849344257923 12230085252856274016386885)
        ·
          refine ⟨2293140984910551378072541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12230085252856274016386885 2293140984910551378072541)
          ·
            refine ⟨859927869341456766777203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2293140984910551378072541 859927869341456766777203)
            ·
              refine ⟨1289891804012185150165805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859927869341456766777203 1289891804012185150165805)
              ·
                refine ⟨483709426504569431312177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1289891804012185150165805 483709426504569431312177)
                ·
                  refine ⟨362782069878427073484133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483709426504569431312177 362782069878427073484133)
                  ·
                    rfl

theorem cell20_794830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_794830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794830 prefixEnd_794830 := by exact prefixLift 794830
  have htrace : WordTrace (prefixWord ++ tailWord_794830) baseStart_794830 baseEnd_794830 := by
    simpa [prefixWord, tailWord_794830, baseEnd_794830] using wordTrace_append hprefix tailTrace_794830
  have hstable : (prefixWord ++ tailWord_794830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794830).length < 2 ^ (prefixWord ++ tailWord_794830).sum := by decide
  have hdescent : baseEnd_794830 < baseStart_794830 := by decide
  rcases family_descends (prefixWord ++ tailWord_794830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794831 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 7]
def baseStart_794831 : Nat := 118140960795 + 794831 * 2 ^ 59
def prefixEnd_794831 : Nat := 4983230072969 + 3 ^ 40 * 794831 * 2
def baseEnd_794831 : Nat := 362782526305675514450795

theorem tailTrace_794831 : CollatzResearch.WordTrace tailWord_794831 prefixEnd_794831 362782526305675514450795 := by
  unfold tailWord_794831
  simp only [CollatzResearch.WordTrace]
  refine ⟨28989868183470508172592347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19326578788980338781728231 28989868183470508172592347)
  ·
    refine ⟨43484802275205762258888521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28989868183470508172592347 43484802275205762258888521)
    ·
      refine ⟨32613601706404321694166391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43484802275205762258888521 32613601706404321694166391)
      ·
        refine ⟨48920402559606482541249587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32613601706404321694166391 48920402559606482541249587)
        ·
          refine ⟨73380603839409723811874381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48920402559606482541249587 73380603839409723811874381)
          ·
            refine ⟨27517726439778646429452893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73380603839409723811874381 27517726439778646429452893)
            ·
              refine ⟨10319147414916992411044835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27517726439778646429452893 10319147414916992411044835)
              ·
                refine ⟨15478721122375488616567253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10319147414916992411044835 15478721122375488616567253)
                ·
                  refine ⟨362782526305675514450795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15478721122375488616567253 362782526305675514450795)
                  ·
                    rfl

theorem cell20_794831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_794831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794831 prefixEnd_794831 := by exact prefixLift 794831
  have htrace : WordTrace (prefixWord ++ tailWord_794831) baseStart_794831 baseEnd_794831 := by
    simpa [prefixWord, tailWord_794831, baseEnd_794831] using wordTrace_append hprefix tailTrace_794831
  have hstable : (prefixWord ++ tailWord_794831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794831).length < 2 ^ (prefixWord ++ tailWord_794831).sum := by decide
  have hdescent : baseEnd_794831 < baseStart_794831 := by decide
  rcases family_descends (prefixWord ++ tailWord_794831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794848 : List Nat := [2, 1, 1, 3, 1, 3, 2, 4, 3]
def baseStart_794848 : Nat := 118140960795 + 794848 * 2 ^ 59
def prefixEnd_794848 : Nat := 4983230072969 + 3 ^ 40 * 794848 * 2
def baseEnd_794848 : Nat := 362790285568899010884059

theorem tailTrace_794848 : CollatzResearch.WordTrace tailWord_794848 prefixEnd_794848 362790285568899010884059 := by
  unfold tailWord_794848
  simp only [CollatzResearch.WordTrace]
  refine ⟨14495244112204460037980599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19326992149605946717307465 14495244112204460037980599)
  ·
    refine ⟨21742866168306690056970899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14495244112204460037980599 21742866168306690056970899)
    ·
      refine ⟨32614299252460035085456349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21742866168306690056970899 32614299252460035085456349)
      ·
        refine ⟨12230362219672513157046131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32614299252460035085456349 12230362219672513157046131)
        ·
          refine ⟨18345543329508769735569197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12230362219672513157046131 18345543329508769735569197)
          ·
            refine ⟨6879578748565788650838449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18345543329508769735569197 6879578748565788650838449)
            ·
              refine ⟨5159684061424341488128837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6879578748565788650838449 5159684061424341488128837)
              ·
                refine ⟨967440761517064029024157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5159684061424341488128837 967440761517064029024157)
                ·
                  refine ⟨362790285568899010884059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 967440761517064029024157 362790285568899010884059)
                  ·
                    rfl

theorem cell20_794848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_794848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794848 prefixEnd_794848 := by exact prefixLift 794848
  have htrace : WordTrace (prefixWord ++ tailWord_794848) baseStart_794848 baseEnd_794848 := by
    simpa [prefixWord, tailWord_794848, baseEnd_794848] using wordTrace_append hprefix tailTrace_794848
  have hstable : (prefixWord ++ tailWord_794848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794848).length < 2 ^ (prefixWord ++ tailWord_794848).sum := by decide
  have hdescent : baseEnd_794848 < baseStart_794848 := by decide
  rcases family_descends (prefixWord ++ tailWord_794848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794861 : List Nat := [1, 5, 1, 2, 3, 2, 2, 1, 3]
def baseStart_794861 : Nat := 118140960795 + 794861 * 2 ^ 59
def prefixEnd_794861 : Nat := 4983230072969 + 3 ^ 40 * 794861 * 2
def baseEnd_794861 : Nat := 362796219123128743450673

theorem tailTrace_794861 : CollatzResearch.WordTrace tailWord_794861 prefixEnd_794861 362796219123128743450673 := by
  unfold tailWord_794861
  simp only [CollatzResearch.WordTrace]
  refine ⟨28990962373361823296184437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19327308248907882197456291 28990962373361823296184437)
  ·
    refine ⟨2717902722502670934017291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28990962373361823296184437 2717902722502670934017291)
    ·
      refine ⟨4076854083754006401025937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2717902722502670934017291 4076854083754006401025937)
      ·
        refine ⟨3057640562815504800769453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4076854083754006401025937 3057640562815504800769453)
        ·
          refine ⟨1146615211055814300288545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3057640562815504800769453 1146615211055814300288545)
          ·
            refine ⟨859961408291860725216409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1146615211055814300288545 859961408291860725216409)
            ·
              refine ⟨644971056218895543912307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 859961408291860725216409 644971056218895543912307)
              ·
                refine ⟨967456584328343315868461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644971056218895543912307 967456584328343315868461)
                ·
                  refine ⟨362796219123128743450673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 967456584328343315868461 362796219123128743450673)
                  ·
                    rfl

theorem cell20_794861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_794861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794861 prefixEnd_794861 := by exact prefixLift 794861
  have htrace : WordTrace (prefixWord ++ tailWord_794861) baseStart_794861 baseEnd_794861 := by
    simpa [prefixWord, tailWord_794861, baseEnd_794861] using wordTrace_append hprefix tailTrace_794861
  have hstable : (prefixWord ++ tailWord_794861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794861).length < 2 ^ (prefixWord ++ tailWord_794861).sum := by decide
  have hdescent : baseEnd_794861 < baseStart_794861 := by decide
  rcases family_descends (prefixWord ++ tailWord_794861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794865 : List Nat := [1, 2, 2, 2, 2, 1, 6, 1, 3]
def baseStart_794865 : Nat := 118140960795 + 794865 * 2 ^ 59
def prefixEnd_794865 : Nat := 4983230072969 + 3 ^ 40 * 794865 * 2
def baseEnd_794865 : Nat := 362798044832122507317323

theorem tailTrace_794865 : CollatzResearch.WordTrace tailWord_794865 prefixEnd_794865 362798044832122507317323 := by
  unfold tailWord_794865
  simp only [CollatzResearch.WordTrace]
  refine ⟨28991108265347331979330049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19327405510231554652886699 28991108265347331979330049)
  ·
    refine ⟨21743331199010498984497537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28991108265347331979330049 21743331199010498984497537)
    ·
      refine ⟨16307498399257874238373153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21743331199010498984497537 16307498399257874238373153)
      ·
        refine ⟨12230623799443405678779865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16307498399257874238373153 12230623799443405678779865)
        ·
          refine ⟨9172967849582554259084899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12230623799443405678779865 9172967849582554259084899)
          ·
            refine ⟨13759451774373831388627349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9172967849582554259084899 13759451774373831388627349)
            ·
              refine ⟨644974301923773346341907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13759451774373831388627349 644974301923773346341907)
              ·
                refine ⟨967461452885660019512861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644974301923773346341907 967461452885660019512861)
                ·
                  refine ⟨362798044832122507317323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 967461452885660019512861 362798044832122507317323)
                  ·
                    rfl

theorem cell20_794865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 3].length) (baseStart_794865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794865 prefixEnd_794865 := by exact prefixLift 794865
  have htrace : WordTrace (prefixWord ++ tailWord_794865) baseStart_794865 baseEnd_794865 := by
    simpa [prefixWord, tailWord_794865, baseEnd_794865] using wordTrace_append hprefix tailTrace_794865
  have hstable : (prefixWord ++ tailWord_794865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794865).length < 2 ^ (prefixWord ++ tailWord_794865).sum := by decide
  have hdescent : baseEnd_794865 < baseStart_794865 := by decide
  rcases family_descends (prefixWord ++ tailWord_794865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794903 : List Nat := [1, 1, 3, 4, 1, 3, 2, 2, 3]
def baseStart_794903 : Nat := 118140960795 + 794903 * 2 ^ 59
def prefixEnd_794903 : Nat := 4983230072969 + 3 ^ 40 * 794903 * 2
def baseEnd_794903 : Nat := 362815389067563264050501

theorem tailTrace_794903 : CollatzResearch.WordTrace tailWord_794903 prefixEnd_794903 362815389067563264050501 := by
  unfold tailWord_794903
  simp only [CollatzResearch.WordTrace]
  refine ⟨28992494239209664469213363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19328329492806442979475575 28992494239209664469213363)
  ·
    refine ⟨43488741358814496703820045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28992494239209664469213363 43488741358814496703820045)
    ·
      refine ⟨16308278009555436263932517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43488741358814496703820045 16308278009555436263932517)
      ·
        refine ⟨3057802126791644299487347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16308278009555436263932517 3057802126791644299487347)
        ·
          refine ⟨4586703190187466449231021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3057802126791644299487347 4586703190187466449231021)
          ·
            refine ⟨1720013696320299918461633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4586703190187466449231021 1720013696320299918461633)
            ·
              refine ⟨1290010272240224938846225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1720013696320299918461633 1290010272240224938846225)
              ·
                refine ⟨967507704180168704134669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1290010272240224938846225 967507704180168704134669)
                ·
                  refine ⟨362815389067563264050501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 967507704180168704134669 362815389067563264050501)
                  ·
                    rfl

theorem cell20_794903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 3].length) (baseStart_794903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794903 prefixEnd_794903 := by exact prefixLift 794903
  have htrace : WordTrace (prefixWord ++ tailWord_794903) baseStart_794903 baseEnd_794903 := by
    simpa [prefixWord, tailWord_794903, baseEnd_794903] using wordTrace_append hprefix tailTrace_794903
  have hstable : (prefixWord ++ tailWord_794903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794903).length < 2 ^ (prefixWord ++ tailWord_794903).sum := by decide
  have hdescent : baseEnd_794903 < baseStart_794903 := by decide
  rcases family_descends (prefixWord ++ tailWord_794903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794907 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 5]
def baseStart_794907 : Nat := 118140960795 + 794907 * 2 ^ 59
def prefixEnd_794907 : Nat := 4983230072969 + 3 ^ 40 * 794907 * 2
def baseEnd_794907 : Nat := 362817214776557027917151

theorem tailTrace_794907 : CollatzResearch.WordTrace tailWord_794907 prefixEnd_794907 362817214776557027917151 := by
  unfold tailWord_794907
  simp only [CollatzResearch.WordTrace]
  refine ⟨28992640131195173152358975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19328426754130115434905983 28992640131195173152358975)
  ·
    refine ⟨43488960196792759728538463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28992640131195173152358975 43488960196792759728538463)
    ·
      refine ⟨65233440295189139592807695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43488960196792759728538463 65233440295189139592807695)
      ·
        refine ⟨97850160442783709389211543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65233440295189139592807695 97850160442783709389211543)
        ·
          refine ⟨146775240664175564083817315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97850160442783709389211543 146775240664175564083817315)
          ·
            refine ⟨220162860996263346125725973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146775240664175564083817315 220162860996263346125725973)
            ·
              refine ⟨10320134109199844349643405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 220162860996263346125725973 10320134109199844349643405)
              ·
                refine ⟨3870050290949941631116277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10320134109199844349643405 3870050290949941631116277)
                ·
                  refine ⟨362817214776557027917151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3870050290949941631116277 362817214776557027917151)
                  ·
                    rfl

theorem cell20_794907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_794907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794907 prefixEnd_794907 := by exact prefixLift 794907
  have htrace : WordTrace (prefixWord ++ tailWord_794907) baseStart_794907 baseEnd_794907 := by
    simpa [prefixWord, tailWord_794907, baseEnd_794907] using wordTrace_append hprefix tailTrace_794907
  have hstable : (prefixWord ++ tailWord_794907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794907).length < 2 ^ (prefixWord ++ tailWord_794907).sum := by decide
  have hdescent : baseEnd_794907 < baseStart_794907 := by decide
  rcases family_descends (prefixWord ++ tailWord_794907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794924 : List Nat := [2, 2, 1, 1, 1, 3, 4, 3, 3]
def baseStart_794924 : Nat := 118140960795 + 794924 * 2 ^ 59
def prefixEnd_794924 : Nat := 4983230072969 + 3 ^ 40 * 794924 * 2
def baseEnd_794924 : Nat := 362824974039780524350415

theorem tailTrace_794924 : CollatzResearch.WordTrace tailWord_794924 prefixEnd_794924 362824974039780524350415 := by
  unfold tailWord_794924
  simp only [CollatzResearch.WordTrace]
  refine ⟨14496630086066792527863913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19328840114755723370485217 14496630086066792527863913)
  ·
    refine ⟨10872472564550094395897935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14496630086066792527863913 10872472564550094395897935)
    ·
      refine ⟨16308708846825141593846903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10872472564550094395897935 16308708846825141593846903)
      ·
        refine ⟨24463063270237712390770355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16308708846825141593846903 24463063270237712390770355)
        ·
          refine ⟨36694594905356568586155533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24463063270237712390770355 36694594905356568586155533)
          ·
            refine ⟨13760473089508713219808325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36694594905356568586155533 13760473089508713219808325)
            ·
              refine ⟨2580088704282883728714061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13760473089508713219808325 2580088704282883728714061)
              ·
                refine ⟨967533264106081398267773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2580088704282883728714061 967533264106081398267773)
                ·
                  refine ⟨362824974039780524350415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 967533264106081398267773 362824974039780524350415)
                  ·
                    rfl

theorem cell20_794924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_794924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794924 prefixEnd_794924 := by exact prefixLift 794924
  have htrace : WordTrace (prefixWord ++ tailWord_794924) baseStart_794924 baseEnd_794924 := by
    simpa [prefixWord, tailWord_794924, baseEnd_794924] using wordTrace_append hprefix tailTrace_794924
  have hstable : (prefixWord ++ tailWord_794924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794924).length < 2 ^ (prefixWord ++ tailWord_794924).sum := by decide
  have hdescent : baseEnd_794924 < baseStart_794924 := by decide
  rcases family_descends (prefixWord ++ tailWord_794924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794931 : List Nat := [1, 1, 1, 2, 5, 1, 3, 2, 4]
def baseStart_794931 : Nat := 118140960795 + 794931 * 2 ^ 59
def prefixEnd_794931 : Nat := 4983230072969 + 3 ^ 40 * 794931 * 2
def baseEnd_794931 : Nat := 362828169030519611117053

theorem tailTrace_794931 : CollatzResearch.WordTrace tailWord_794931 prefixEnd_794931 362828169030519611117053 := by
  unfold tailWord_794931
  simp only [CollatzResearch.WordTrace]
  refine ⟨28993515483108225251232647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19329010322072150167488431 28993515483108225251232647)
  ·
    refine ⟨43490273224662337876848971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28993515483108225251232647 43490273224662337876848971)
    ·
      refine ⟨65235409836993506815273457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43490273224662337876848971 65235409836993506815273457)
      ·
        refine ⟨48926557377745130111455093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65235409836993506815273457 48926557377745130111455093)
        ·
          refine ⟨4586864754163605947948915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48926557377745130111455093 4586864754163605947948915)
          ·
            refine ⟨6880297131245408921923373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4586864754163605947948915 6880297131245408921923373)
            ·
              refine ⟨2580111424217028345721265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6880297131245408921923373 2580111424217028345721265)
              ·
                refine ⟨1935083568162771259290949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2580111424217028345721265 1935083568162771259290949)
                ·
                  refine ⟨362828169030519611117053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1935083568162771259290949 362828169030519611117053)
                  ·
                    rfl

theorem cell20_794931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_794931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794931 prefixEnd_794931 := by exact prefixLift 794931
  have htrace : WordTrace (prefixWord ++ tailWord_794931) baseStart_794931 baseEnd_794931 := by
    simpa [prefixWord, tailWord_794931, baseEnd_794931] using wordTrace_append hprefix tailTrace_794931
  have hstable : (prefixWord ++ tailWord_794931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794931).length < 2 ^ (prefixWord ++ tailWord_794931).sum := by decide
  have hdescent : baseEnd_794931 < baseStart_794931 := by decide
  rcases family_descends (prefixWord ++ tailWord_794931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794979 : List Nat := [1, 1, 1, 5, 2, 1, 5, 1, 3]
def baseStart_794979 : Nat := 118140960795 + 794979 * 2 ^ 59
def prefixEnd_794979 : Nat := 4983230072969 + 3 ^ 40 * 794979 * 2
def baseEnd_794979 : Nat := 362850077538444777516857

theorem tailTrace_794979 : CollatzResearch.WordTrace tailWord_794979 prefixEnd_794979 362850077538444777516857 := by
  unfold tailWord_794979
  simp only [CollatzResearch.WordTrace]
  refine ⟨28995266186934329448979991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19330177457956219632653327 28995266186934329448979991)
  ·
    refine ⟨43492899280401494173469987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28995266186934329448979991 43492899280401494173469987)
    ·
      refine ⟨65239348920602241260204981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43492899280401494173469987 65239348920602241260204981)
      ·
        refine ⟨6116188961306460118144217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65239348920602241260204981 6116188961306460118144217)
        ·
          refine ⟨4587141720979845088608163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6116188961306460118144217 4587141720979845088608163)
          ·
            refine ⟨6880712581469767632912245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4587141720979845088608163 6880712581469767632912245)
            ·
              refine ⟨645066804512790715585523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6880712581469767632912245 645066804512790715585523)
              ·
                refine ⟨967600206769186073378285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645066804512790715585523 967600206769186073378285)
                ·
                  refine ⟨362850077538444777516857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 967600206769186073378285 362850077538444777516857)
                  ·
                    rfl

theorem cell20_794979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 3].length) (baseStart_794979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794979 prefixEnd_794979 := by exact prefixLift 794979
  have htrace : WordTrace (prefixWord ++ tailWord_794979) baseStart_794979 baseEnd_794979 := by
    simpa [prefixWord, tailWord_794979, baseEnd_794979] using wordTrace_append hprefix tailTrace_794979
  have hstable : (prefixWord ++ tailWord_794979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794979).length < 2 ^ (prefixWord ++ tailWord_794979).sum := by decide
  have hdescent : baseEnd_794979 < baseStart_794979 := by decide
  rcases family_descends (prefixWord ++ tailWord_794979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794986 : List Nat := [3, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_794986 : Nat := 118140960795 + 794986 * 2 ^ 59
def prefixEnd_794986 : Nat := 4983230072969 + 3 ^ 40 * 794986 * 2
def baseEnd_794986 : Nat := 362853272529183864283495

theorem tailTrace_794986 : CollatzResearch.WordTrace tailWord_794986 prefixEnd_794986 362853272529183864283495 := by
  unfold tailWord_794986
  simp only [CollatzResearch.WordTrace]
  refine ⟨7248880374477242411121203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19330347665272646429656541 7248880374477242411121203)
  ·
    refine ⟨10873320561715863616681805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7248880374477242411121203 10873320561715863616681805)
    ·
      refine ⟨4077495210643448856255677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10873320561715863616681805 4077495210643448856255677)
      ·
        refine ⟨1529060703991293321095879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4077495210643448856255677 1529060703991293321095879)
        ·
          refine ⟨2293591055986939981643819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1529060703991293321095879 2293591055986939981643819)
          ·
            refine ⟨3440386583980409972465729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2293591055986939981643819 3440386583980409972465729)
            ·
              refine ⟨2580289937985307479349297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3440386583980409972465729 2580289937985307479349297)
              ·
                refine ⟨1935217453488980609511973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2580289937985307479349297 1935217453488980609511973)
                ·
                  refine ⟨362853272529183864283495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1935217453488980609511973 362853272529183864283495)
                  ·
                    rfl

theorem cell20_794986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_794986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_794986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_794986 prefixEnd_794986 := by exact prefixLift 794986
  have htrace : WordTrace (prefixWord ++ tailWord_794986) baseStart_794986 baseEnd_794986 := by
    simpa [prefixWord, tailWord_794986, baseEnd_794986] using wordTrace_append hprefix tailTrace_794986
  have hstable : (prefixWord ++ tailWord_794986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794986).length < 2 ^ (prefixWord ++ tailWord_794986).sum := by decide
  have hdescent : baseEnd_794986 < baseStart_794986 := by decide
  rcases family_descends (prefixWord ++ tailWord_794986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795003 : List Nat := [1, 1, 1, 1, 1, 9, 1, 3, 2]
def baseStart_795003 : Nat := 118140960795 + 795003 * 2 ^ 59
def prefixEnd_795003 : Nat := 4983230072969 + 3 ^ 40 * 795003 * 2
def baseEnd_795003 : Nat := 362861031792407360716759

theorem tailTrace_795003 : CollatzResearch.WordTrace tailWord_795003 prefixEnd_795003 362861031792407360716759 := by
  unfold tailWord_795003
  simp only [CollatzResearch.WordTrace]
  refine ⟨28996141538847381547853663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19330761025898254365235775 28996141538847381547853663)
  ·
    refine ⟨43494212308271072321780495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28996141538847381547853663 43494212308271072321780495)
    ·
      refine ⟨65241318462406608482670743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43494212308271072321780495 65241318462406608482670743)
      ·
        refine ⟨97861977693609912724006115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65241318462406608482670743 97861977693609912724006115)
        ·
          refine ⟨146792966540414869086009173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97861977693609912724006115 146792966540414869086009173)
          ·
            refine ⟨860115038322743373550835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 146792966540414869086009173 860115038322743373550835)
            ·
              refine ⟨1290172557484115060326253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860115038322743373550835 1290172557484115060326253)
              ·
                refine ⟨483814709056543147622345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1290172557484115060326253 483814709056543147622345)
                ·
                  refine ⟨362861031792407360716759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483814709056543147622345 362861031792407360716759)
                  ·
                    rfl

theorem cell20_795003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 2].length) (baseStart_795003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795003 prefixEnd_795003 := by exact prefixLift 795003
  have htrace : WordTrace (prefixWord ++ tailWord_795003) baseStart_795003 baseEnd_795003 := by
    simpa [prefixWord, tailWord_795003, baseEnd_795003] using wordTrace_append hprefix tailTrace_795003
  have hstable : (prefixWord ++ tailWord_795003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795003).length < 2 ^ (prefixWord ++ tailWord_795003).sum := by decide
  have hdescent : baseEnd_795003 < baseStart_795003 := by decide
  rcases family_descends (prefixWord ++ tailWord_795003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795030 : List Nat := [5, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_795030 : Nat := 118140960795 + 795030 * 2 ^ 59
def prefixEnd_795030 : Nat := 4983230072969 + 3 ^ 40 * 795030 * 2
def baseEnd_795030 : Nat := 362873355328115266816649

theorem tailTrace_795030 : CollatzResearch.WordTrace tailWord_795030 prefixEnd_795030 362873355328115266816649 := by
  unfold tailWord_795030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1812320394359347822442909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19331417539833043439391029 1812320394359347822442909)
  ·
    refine ⟨679620147884755433416091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1812320394359347822442909 679620147884755433416091)
    ·
      refine ⟨1019430221827133150124137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 679620147884755433416091 1019430221827133150124137)
      ·
        refine ⟨764572666370349862593103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1019430221827133150124137 764572666370349862593103)
        ·
          refine ⟨1146858999555524793889655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764572666370349862593103 1146858999555524793889655)
          ·
            refine ⟨1720288499333287190834483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146858999555524793889655 1720288499333287190834483)
            ·
              refine ⟨2580432748999930786251725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1720288499333287190834483 2580432748999930786251725)
              ·
                refine ⟨967662280874974044844397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2580432748999930786251725 967662280874974044844397)
                ·
                  refine ⟨362873355328115266816649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 967662280874974044844397 362873355328115266816649)
                  ·
                    rfl

theorem cell20_795030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_795030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795030 prefixEnd_795030 := by exact prefixLift 795030
  have htrace : WordTrace (prefixWord ++ tailWord_795030) baseStart_795030 baseEnd_795030 := by
    simpa [prefixWord, tailWord_795030, baseEnd_795030] using wordTrace_append hprefix tailTrace_795030
  have hstable : (prefixWord ++ tailWord_795030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795030).length < 2 ^ (prefixWord ++ tailWord_795030).sum := by decide
  have hdescent : baseEnd_795030 < baseStart_795030 := by decide
  rcases family_descends (prefixWord ++ tailWord_795030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795034 : List Nat := [3, 1, 1, 4, 1, 4, 2, 1, 3]
def baseStart_795034 : Nat := 118140960795 + 795034 * 2 ^ 59
def prefixEnd_795034 : Nat := 4983230072969 + 3 ^ 40 * 795034 * 2
def baseEnd_795034 : Nat := 362875181037109030683299

theorem tailTrace_795034 : CollatzResearch.WordTrace tailWord_795034 prefixEnd_795034 362875181037109030683299 := by
  unfold tailWord_795034
  simp only [CollatzResearch.WordTrace]
  refine ⟨7249318050433768460558039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19331514801156715894821437 7249318050433768460558039)
  ·
    refine ⟨10873977075650652690837059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7249318050433768460558039 10873977075650652690837059)
    ·
      refine ⟨16310965613475979036255589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10873977075650652690837059 16310965613475979036255589)
      ·
        refine ⟨3058306052526746069297923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16310965613475979036255589 3058306052526746069297923)
        ·
          refine ⟨4587459078790119103946885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3058306052526746069297923 4587459078790119103946885)
          ·
            refine ⟨860148577273147331990041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4587459078790119103946885 860148577273147331990041)
            ·
              refine ⟨645111432954860498992531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 860148577273147331990041 645111432954860498992531)
              ·
                refine ⟨967667149432290748488797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645111432954860498992531 967667149432290748488797)
                ·
                  refine ⟨362875181037109030683299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 967667149432290748488797 362875181037109030683299)
                  ·
                    rfl

theorem cell20_795034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_795034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795034 prefixEnd_795034 := by exact prefixLift 795034
  have htrace : WordTrace (prefixWord ++ tailWord_795034) baseStart_795034 baseEnd_795034 := by
    simpa [prefixWord, tailWord_795034, baseEnd_795034] using wordTrace_append hprefix tailTrace_795034
  have hstable : (prefixWord ++ tailWord_795034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795034).length < 2 ^ (prefixWord ++ tailWord_795034).sum := by decide
  have hdescent : baseEnd_795034 < baseStart_795034 := by decide
  rcases family_descends (prefixWord ++ tailWord_795034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795079 : List Nat := [1, 1, 4, 1, 1, 4, 4, 2, 2]
def baseStart_795079 : Nat := 118140960795 + 795079 * 2 ^ 59
def prefixEnd_795079 : Nat := 4983230072969 + 3 ^ 40 * 795079 * 2
def baseEnd_795079 : Nat := 362895720263288874183115

theorem tailTrace_795079 : CollatzResearch.WordTrace tailWord_795079 prefixEnd_795079 362895720263288874183115 := by
  unfold tailWord_795079
  simp only [CollatzResearch.WordTrace]
  refine ⟨28998913486572046527620291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19332608991048031018413527 28998913486572046527620291)
  ·
    refine ⟨43498370229858069791430437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28998913486572046527620291 43498370229858069791430437)
    ·
      refine ⟨8155944418098388085893207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43498370229858069791430437 8155944418098388085893207)
      ·
        refine ⟨12233916627147582128839811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8155944418098388085893207 12233916627147582128839811)
        ·
          refine ⟨18350874940721373193259717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12233916627147582128839811 18350874940721373193259717)
          ·
            refine ⟨3440789051385257473736197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18350874940721373193259717 3440789051385257473736197)
            ·
              refine ⟨645147947134735776325537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3440789051385257473736197 645147947134735776325537)
              ·
                refine ⟨483860960351051832244153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 645147947134735776325537 483860960351051832244153)
                ·
                  refine ⟨362895720263288874183115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483860960351051832244153 362895720263288874183115)
                  ·
                    rfl

theorem cell20_795079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 2].length) (baseStart_795079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795079 prefixEnd_795079 := by exact prefixLift 795079
  have htrace : WordTrace (prefixWord ++ tailWord_795079) baseStart_795079 baseEnd_795079 := by
    simpa [prefixWord, tailWord_795079, baseEnd_795079] using wordTrace_append hprefix tailTrace_795079
  have hstable : (prefixWord ++ tailWord_795079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795079).length < 2 ^ (prefixWord ++ tailWord_795079).sum := by decide
  have hdescent : baseEnd_795079 < baseStart_795079 := by decide
  rcases family_descends (prefixWord ++ tailWord_795079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795117 : List Nat := [1, 5, 1, 3, 1, 1, 1, 5, 2]
def baseStart_795117 : Nat := 118140960795 + 795117 * 2 ^ 59
def prefixEnd_795117 : Nat := 4983230072969 + 3 ^ 40 * 795117 * 2
def baseEnd_795117 : Nat := 362913064498729630916293

theorem tailTrace_795117 : CollatzResearch.WordTrace tailWord_795117 prefixEnd_795117 362913064498729630916293 := by
  unfold tailWord_795117
  simp only [CollatzResearch.WordTrace]
  refine ⟨29000299460434379017503605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19333532973622919345002403 29000299460434379017503605)
  ·
    refine ⟨2718778074415723032890963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29000299460434379017503605 2718778074415723032890963)
    ·
      refine ⟨4078167111623584549336445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2718778074415723032890963 4078167111623584549336445)
      ·
        refine ⟨1529312666858844206001167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4078167111623584549336445 1529312666858844206001167)
        ·
          refine ⟨2293969000288266309001751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1529312666858844206001167 2293969000288266309001751)
          ·
            refine ⟨3440953500432399463502627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2293969000288266309001751 3440953500432399463502627)
            ·
              refine ⟨5161430250648599195253941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3440953500432399463502627 5161430250648599195253941)
              ·
                refine ⟨483884085998306174555057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5161430250648599195253941 483884085998306174555057)
                ·
                  refine ⟨362913064498729630916293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483884085998306174555057 362913064498729630916293)
                  ·
                    rfl

theorem cell20_795117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_795117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795117 prefixEnd_795117 := by exact prefixLift 795117
  have htrace : WordTrace (prefixWord ++ tailWord_795117) baseStart_795117 baseEnd_795117 := by
    simpa [prefixWord, tailWord_795117, baseEnd_795117] using wordTrace_append hprefix tailTrace_795117
  have hstable : (prefixWord ++ tailWord_795117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795117).length < 2 ^ (prefixWord ++ tailWord_795117).sum := by decide
  have hdescent : baseEnd_795117 < baseStart_795117 := by decide
  rcases family_descends (prefixWord ++ tailWord_795117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795135 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 5]
def baseStart_795135 : Nat := 118140960795 + 795135 * 2 ^ 59
def prefixEnd_795135 : Nat := 4983230072969 + 3 ^ 40 * 795135 * 2
def baseEnd_795135 : Nat := 362921280189201568316219

theorem tailTrace_795135 : CollatzResearch.WordTrace tailWord_795135 prefixEnd_795135 362921280189201568316219 := by
  unfold tailWord_795135
  simp only [CollatzResearch.WordTrace]
  refine ⟨29000955974369168091658859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19333970649579445394439239 29000955974369168091658859)
  ·
    refine ⟨43501433961553752137488289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29000955974369168091658859 43501433961553752137488289)
    ·
      refine ⟨32626075471165314103116217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43501433961553752137488289 32626075471165314103116217)
      ·
        refine ⟨24469556603373985577337163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32626075471165314103116217 24469556603373985577337163)
        ·
          refine ⟨36704334905060978366005745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24469556603373985577337163 36704334905060978366005745)
          ·
            refine ⟨27528251178795733774504309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36704334905060978366005745 27528251178795733774504309)
            ·
              refine ⟨2580773548012100041359779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27528251178795733774504309 2580773548012100041359779)
              ·
                refine ⟨3871160322018150062039669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2580773548012100041359779 3871160322018150062039669)
                ·
                  refine ⟨362921280189201568316219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3871160322018150062039669 362921280189201568316219)
                  ·
                    rfl

theorem cell20_795135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_795135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795135 prefixEnd_795135 := by exact prefixLift 795135
  have htrace : WordTrace (prefixWord ++ tailWord_795135) baseStart_795135 baseEnd_795135 := by
    simpa [prefixWord, tailWord_795135, baseEnd_795135] using wordTrace_append hprefix tailTrace_795135
  have hstable : (prefixWord ++ tailWord_795135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795135).length < 2 ^ (prefixWord ++ tailWord_795135).sum := by decide
  have hdescent : baseEnd_795135 < baseStart_795135 := by decide
  rcases family_descends (prefixWord ++ tailWord_795135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795173 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 5]
def baseStart_795173 : Nat := 118140960795 + 795173 * 2 ^ 59
def prefixEnd_795173 : Nat := 4983230072969 + 3 ^ 40 * 795173 * 2
def baseEnd_795173 : Nat := 362938624424642325049397

theorem tailTrace_795173 : CollatzResearch.WordTrace tailWord_795173 prefixEnd_795173 362938624424642325049397 := by
  unfold tailWord_795173
  simp only [CollatzResearch.WordTrace]
  refine ⟨29002341948231500581542173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19334894632154333721028115 29002341948231500581542173)
  ·
    refine ⟨10875878230586812718078315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29002341948231500581542173 10875878230586812718078315)
    ·
      refine ⟨16313817345880219077117473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10875878230586812718078315 16313817345880219077117473)
      ·
        refine ⟨12235363009410164307838105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16313817345880219077117473 12235363009410164307838105)
        ·
          refine ⟨9176522257057623230878579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12235363009410164307838105 9176522257057623230878579)
          ·
            refine ⟨13764783385586434846317869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9176522257057623230878579 13764783385586434846317869)
            ·
              refine ⟨5161793769594913067369201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13764783385586434846317869 5161793769594913067369201)
              ·
                refine ⟨3871345327196184800526901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5161793769594913067369201 3871345327196184800526901)
                ·
                  refine ⟨362938624424642325049397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3871345327196184800526901 362938624424642325049397)
                  ·
                    rfl

theorem cell20_795173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_795173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795173 prefixEnd_795173 := by exact prefixLift 795173
  have htrace : WordTrace (prefixWord ++ tailWord_795173) baseStart_795173 baseEnd_795173 := by
    simpa [prefixWord, tailWord_795173, baseEnd_795173] using wordTrace_append hprefix tailTrace_795173
  have hstable : (prefixWord ++ tailWord_795173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795173).length < 2 ^ (prefixWord ++ tailWord_795173).sum := by decide
  have hdescent : baseEnd_795173 < baseStart_795173 := by decide
  rcases family_descends (prefixWord ++ tailWord_795173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795180 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 6]
def baseStart_795180 : Nat := 118140960795 + 795180 * 2 ^ 59
def prefixEnd_795180 : Nat := 4983230072969 + 3 ^ 40 * 795180 * 2
def baseEnd_795180 : Nat := 362941819415381411816035

theorem tailTrace_795180 : CollatzResearch.WordTrace tailWord_795180 prefixEnd_795180 362941819415381411816035 := by
  unfold tailWord_795180
  simp only [CollatzResearch.WordTrace]
  refine ⟨14501298629603070388523497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19335064839470760518031329 14501298629603070388523497)
  ·
    refine ⟨10875973972202302791392623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14501298629603070388523497 10875973972202302791392623)
    ·
      refine ⟨16313960958303454187088935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10875973972202302791392623 16313960958303454187088935)
      ·
        refine ⟨24470941437455181280633403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16313960958303454187088935 24470941437455181280633403)
        ·
          refine ⟨36706412156182771920950105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24470941437455181280633403 36706412156182771920950105)
          ·
            refine ⟨27529809117137078940712579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36706412156182771920950105 27529809117137078940712579)
            ·
              refine ⟨41294713675705618411068869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27529809117137078940712579 41294713675705618411068869)
              ·
                refine ⟨7742758814194803452075413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41294713675705618411068869 7742758814194803452075413)
                ·
                  refine ⟨362941819415381411816035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7742758814194803452075413 362941819415381411816035)
                  ·
                    rfl

theorem cell20_795180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_795180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795180 prefixEnd_795180 := by exact prefixLift 795180
  have htrace : WordTrace (prefixWord ++ tailWord_795180) baseStart_795180 baseEnd_795180 := by
    simpa [prefixWord, tailWord_795180, baseEnd_795180] using wordTrace_append hprefix tailTrace_795180
  have hstable : (prefixWord ++ tailWord_795180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795180).length < 2 ^ (prefixWord ++ tailWord_795180).sum := by decide
  have hdescent : baseEnd_795180 < baseStart_795180 := by decide
  rcases family_descends (prefixWord ++ tailWord_795180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795193 : List Nat := [1, 2, 1, 5, 1, 1, 5, 2, 2]
def baseStart_795193 : Nat := 118140960795 + 795193 * 2 ^ 59
def prefixEnd_795193 : Nat := 4983230072969 + 3 ^ 40 * 795193 * 2
def baseEnd_795193 : Nat := 362947752969611144382649

theorem tailTrace_795193 : CollatzResearch.WordTrace tailWord_795193 prefixEnd_795193 362947752969611144382649 := by
  unfold tailWord_795193
  simp only [CollatzResearch.WordTrace]
  refine ⟨29003071408159043997270233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19335380938772695998180155 29003071408159043997270233)
  ·
    refine ⟨21752303556119282997952675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29003071408159043997270233 21752303556119282997952675)
    ·
      refine ⟨32628455334178924496929013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21752303556119282997952675 32628455334178924496929013)
      ·
        refine ⟨3058917687579274171587095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32628455334178924496929013 3058917687579274171587095)
        ·
          refine ⟨4588376531368911257380643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3058917687579274171587095 4588376531368911257380643)
          ·
            refine ⟨6882564797053366886070965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4588376531368911257380643 6882564797053366886070965)
            ·
              refine ⟨645240449723753145569153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6882564797053366886070965 645240449723753145569153)
              ·
                refine ⟨483930337292814859176865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 645240449723753145569153 483930337292814859176865)
                ·
                  refine ⟨362947752969611144382649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483930337292814859176865 362947752969611144382649)
                  ·
                    rfl

theorem cell20_795193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 2, 2].length) (baseStart_795193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795193 prefixEnd_795193 := by exact prefixLift 795193
  have htrace : WordTrace (prefixWord ++ tailWord_795193) baseStart_795193 baseEnd_795193 := by
    simpa [prefixWord, tailWord_795193, baseEnd_795193] using wordTrace_append hprefix tailTrace_795193
  have hstable : (prefixWord ++ tailWord_795193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795193).length < 2 ^ (prefixWord ++ tailWord_795193).sum := by decide
  have hdescent : baseEnd_795193 < baseStart_795193 := by decide
  rcases family_descends (prefixWord ++ tailWord_795193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795207 : List Nat := [1, 1, 4, 1, 4, 1, 4, 1, 3]
def baseStart_795207 : Nat := 118140960795 + 795207 * 2 ^ 59
def prefixEnd_795207 : Nat := 4983230072969 + 3 ^ 40 * 795207 * 2
def baseEnd_795207 : Nat := 362954142951089317915925

theorem tailTrace_795207 : CollatzResearch.WordTrace tailWord_795207 prefixEnd_795207 362954142951089317915925 := by
  unfold tailWord_795207
  simp only [CollatzResearch.WordTrace]
  refine ⟨29003582030108324388279875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19335721353405549592186583 29003582030108324388279875)
  ·
    refine ⟨43505373045162486582419813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29003582030108324388279875 43505373045162486582419813)
    ·
      refine ⟨8157257445967966234203715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43505373045162486582419813 8157257445967966234203715)
      ·
        refine ⟨12235886168951949351305573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8157257445967966234203715 12235886168951949351305573)
        ·
          refine ⟨2294228656678490503369795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12235886168951949351305573 2294228656678490503369795)
          ·
            refine ⟨3441342985017735755054693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2294228656678490503369795 3441342985017735755054693)
            ·
              refine ⟨645251809690825454072755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3441342985017735755054693 645251809690825454072755)
              ·
                refine ⟨967877714536238181109133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645251809690825454072755 967877714536238181109133)
                ·
                  refine ⟨362954142951089317915925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 967877714536238181109133 362954142951089317915925)
                  ·
                    rfl

theorem cell20_795207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 4, 1, 3].length) (baseStart_795207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795207 prefixEnd_795207 := by exact prefixLift 795207
  have htrace : WordTrace (prefixWord ++ tailWord_795207) baseStart_795207 baseEnd_795207 := by
    simpa [prefixWord, tailWord_795207, baseEnd_795207] using wordTrace_append hprefix tailTrace_795207
  have hstable : (prefixWord ++ tailWord_795207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795207).length < 2 ^ (prefixWord ++ tailWord_795207).sum := by decide
  have hdescent : baseEnd_795207 < baseStart_795207 := by decide
  rcases family_descends (prefixWord ++ tailWord_795207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795245 : List Nat := [1, 5, 1, 1, 3, 2, 2, 2, 3]
def baseStart_795245 : Nat := 118140960795 + 795245 * 2 ^ 59
def prefixEnd_795245 : Nat := 4983230072969 + 3 ^ 40 * 795245 * 2
def baseEnd_795245 : Nat := 362971487186530074649103

theorem tailTrace_795245 : CollatzResearch.WordTrace tailWord_795245 prefixEnd_795245 362971487186530074649103 := by
  unfold tailWord_795245
  simp only [CollatzResearch.WordTrace]
  refine ⟨29004968003970656878163189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19336645335980437918775459 29004968003970656878163189)
  ·
    refine ⟨2719215750372249082327799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29004968003970656878163189 2719215750372249082327799)
    ·
      refine ⟨4078823625558373623491699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2719215750372249082327799 4078823625558373623491699)
      ·
        refine ⟨6118235438337560435237549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4078823625558373623491699 6118235438337560435237549)
        ·
          refine ⟨2294338289376585163214081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6118235438337560435237549 2294338289376585163214081)
          ·
            refine ⟨1720753717032438872410561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2294338289376585163214081 1720753717032438872410561)
            ·
              refine ⟨1290565287774329154307921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1720753717032438872410561 1290565287774329154307921)
              ·
                refine ⟨967923965830746865730941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1290565287774329154307921 967923965830746865730941)
                ·
                  refine ⟨362971487186530074649103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 967923965830746865730941 362971487186530074649103)
                  ·
                    rfl

theorem cell20_795245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_795245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795245 prefixEnd_795245 := by exact prefixLift 795245
  have htrace : WordTrace (prefixWord ++ tailWord_795245) baseStart_795245 baseEnd_795245 := by
    simpa [prefixWord, tailWord_795245, baseEnd_795245] using wordTrace_append hprefix tailTrace_795245
  have hstable : (prefixWord ++ tailWord_795245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795245).length < 2 ^ (prefixWord ++ tailWord_795245).sum := by decide
  have hdescent : baseEnd_795245 < baseStart_795245 := by decide
  rcases family_descends (prefixWord ++ tailWord_795245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795248 : List Nat := [2, 1, 1, 1, 7, 2, 2, 2, 2]
def baseStart_795248 : Nat := 118140960795 + 795248 * 2 ^ 59
def prefixEnd_795248 : Nat := 4983230072969 + 3 ^ 40 * 795248 * 2
def baseEnd_795248 : Nat := 362972856468275397549091

theorem tailTrace_795248 : CollatzResearch.WordTrace tailWord_795248 prefixEnd_795248 362972856468275397549091 := by
  unfold tailWord_795248
  simp only [CollatzResearch.WordTrace]
  refine ⟨14502538711479894195261199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19336718281973192260348265 14502538711479894195261199)
  ·
    refine ⟨21753808067219841292891799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14502538711479894195261199 21753808067219841292891799)
    ·
      refine ⟨32630712100829761939337699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21753808067219841292891799 32630712100829761939337699)
      ·
        refine ⟨48946068151244642909006549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32630712100829761939337699 48946068151244642909006549)
        ·
          refine ⟨1147173472294796318179841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 48946068151244642909006549 1147173472294796318179841)
          ·
            refine ⟨860380104221097238634881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1147173472294796318179841 860380104221097238634881)
            ·
              refine ⟨645285078165822928976161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 860380104221097238634881 645285078165822928976161)
              ·
                refine ⟨483963808624367196732121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 645285078165822928976161 483963808624367196732121)
                ·
                  refine ⟨362972856468275397549091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 483963808624367196732121 362972856468275397549091)
                  ·
                    rfl

theorem cell20_795248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 2].length) (baseStart_795248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795248 prefixEnd_795248 := by exact prefixLift 795248
  have htrace : WordTrace (prefixWord ++ tailWord_795248) baseStart_795248 baseEnd_795248 := by
    simpa [prefixWord, tailWord_795248, baseEnd_795248] using wordTrace_append hprefix tailTrace_795248
  have hstable : (prefixWord ++ tailWord_795248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795248).length < 2 ^ (prefixWord ++ tailWord_795248).sum := by decide
  have hdescent : baseEnd_795248 < baseStart_795248 := by decide
  rcases family_descends (prefixWord ++ tailWord_795248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795263 : List Nat := [1, 1, 2, 2, 1, 1, 1, 11]
def baseStart_795263 : Nat := 118140960795 + 795263 * 2 ^ 59
def prefixEnd_795263 : Nat := 4983230072969 + 3 ^ 40 * 795263 * 2
def baseEnd_795263 : Nat := 120993234292334004016343

theorem tailTrace_795263 : CollatzResearch.WordTrace tailWord_795263 prefixEnd_795263 120993234292334004016343 := by
  unfold tailWord_795263
  simp only [CollatzResearch.WordTrace]
  refine ⟨29005624517905445952318443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19337083011936963968212295 29005624517905445952318443)
  ·
    refine ⟨43508436776858168928477665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29005624517905445952318443 43508436776858168928477665)
    ·
      refine ⟨32631327582643626696358249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43508436776858168928477665 32631327582643626696358249)
      ·
        refine ⟨24473495686982720022268687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32631327582643626696358249 24473495686982720022268687)
        ·
          refine ⟨36710243530474080033403031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24473495686982720022268687 36710243530474080033403031)
          ·
            refine ⟨55065365295711120050104547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36710243530474080033403031 55065365295711120050104547)
            ·
              refine ⟨82598047943566680075156821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55065365295711120050104547 82598047943566680075156821)
              ·
                refine ⟨120993234292334004016343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 82598047943566680075156821 120993234292334004016343)
                ·
                  rfl

theorem cell20_795263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 11].length) (baseStart_795263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795263 prefixEnd_795263 := by exact prefixLift 795263
  have htrace : WordTrace (prefixWord ++ tailWord_795263) baseStart_795263 baseEnd_795263 := by
    simpa [prefixWord, tailWord_795263, baseEnd_795263] using wordTrace_append hprefix tailTrace_795263
  have hstable : (prefixWord ++ tailWord_795263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795263).length < 2 ^ (prefixWord ++ tailWord_795263).sum := by decide
  have hdescent : baseEnd_795263 < baseStart_795263 := by decide
  rcases family_descends (prefixWord ++ tailWord_795263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795287 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 5]
def baseStart_795287 : Nat := 118140960795 + 795287 * 2 ^ 59
def prefixEnd_795287 : Nat := 4983230072969 + 3 ^ 40 * 795287 * 2
def baseEnd_795287 : Nat := 362990657130964595248931

theorem tailTrace_795287 : CollatzResearch.WordTrace tailWord_795287 prefixEnd_795287 362990657130964595248931 := by
  unfold tailWord_795287
  simp only [CollatzResearch.WordTrace]
  refine ⟨29006499869818498051192115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19337666579878998700794743 29006499869818498051192115)
  ·
    refine ⟨43509749804727747076788173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29006499869818498051192115 43509749804727747076788173)
    ·
      refine ⟨16316156176772905153795565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43509749804727747076788173 16316156176772905153795565)
      ·
        refine ⟨6118558566289839432673337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16316156176772905153795565 6118558566289839432673337)
        ·
          refine ⟨4588918924717379574505003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6118558566289839432673337 4588918924717379574505003)
          ·
            refine ⟨6883378387076069361757505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4588918924717379574505003 6883378387076069361757505)
            ·
              refine ⟨5162533790307052021318129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6883378387076069361757505 5162533790307052021318129)
              ·
                refine ⟨3871900342730289015988597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5162533790307052021318129 3871900342730289015988597)
                ·
                  refine ⟨362990657130964595248931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3871900342730289015988597 362990657130964595248931)
                  ·
                    rfl

theorem cell20_795287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_795287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795287 prefixEnd_795287 := by exact prefixLift 795287
  have htrace : WordTrace (prefixWord ++ tailWord_795287) baseStart_795287 baseEnd_795287 := by
    simpa [prefixWord, tailWord_795287, baseEnd_795287] using wordTrace_append hprefix tailTrace_795287
  have hstable : (prefixWord ++ tailWord_795287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795287).length < 2 ^ (prefixWord ++ tailWord_795287).sum := by decide
  have hdescent : baseEnd_795287 < baseStart_795287 := by decide
  rcases family_descends (prefixWord ++ tailWord_795287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795311 : List Nat := [1, 1, 2, 1, 2, 6, 2, 1, 4]
def baseStart_795311 : Nat := 118140960795 + 795311 * 2 ^ 59
def prefixEnd_795311 : Nat := 4983230072969 + 3 ^ 40 * 795311 * 2
def baseEnd_795311 : Nat := 363001611384927178448833

theorem tailTrace_795311 : CollatzResearch.WordTrace tailWord_795311 prefixEnd_795311 363001611384927178448833 := by
  unfold tailWord_795311
  simp only [CollatzResearch.WordTrace]
  refine ⟨29007375221731550150065787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19338250147821033433377191 29007375221731550150065787)
  ·
    refine ⟨43511062832597325225098681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29007375221731550150065787 43511062832597325225098681)
    ·
      refine ⟨32633297124447993918824011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43511062832597325225098681 32633297124447993918824011)
      ·
        refine ⟨48949945686671990878236017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32633297124447993918824011 48949945686671990878236017)
        ·
          refine ⟨36712459265003993158677013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48949945686671990878236017 36712459265003993158677013)
          ·
            refine ⟨1720896528047062179312985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 36712459265003993158677013 1720896528047062179312985)
            ·
              refine ⟨1290672396035296634484739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1720896528047062179312985 1290672396035296634484739)
              ·
                refine ⟨1936008594052944951727109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290672396035296634484739 1936008594052944951727109)
                ·
                  refine ⟨363001611384927178448833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1936008594052944951727109 363001611384927178448833)
                  ·
                    rfl

theorem cell20_795311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 4].length) (baseStart_795311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795311 prefixEnd_795311 := by exact prefixLift 795311
  have htrace : WordTrace (prefixWord ++ tailWord_795311) baseStart_795311 baseEnd_795311 := by
    simpa [prefixWord, tailWord_795311, baseEnd_795311] using wordTrace_append hprefix tailTrace_795311
  have hstable : (prefixWord ++ tailWord_795311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795311).length < 2 ^ (prefixWord ++ tailWord_795311).sum := by decide
  have hdescent : baseEnd_795311 < baseStart_795311 := by decide
  rcases family_descends (prefixWord ++ tailWord_795311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795341 : List Nat := [1, 6, 2, 1, 2, 2, 1, 3, 2]
def baseStart_795341 : Nat := 118140960795 + 795341 * 2 ^ 59
def prefixEnd_795341 : Nat := 4983230072969 + 3 ^ 40 * 795341 * 2
def baseEnd_795341 : Nat := 363015304202380407448711

theorem tailTrace_795341 : CollatzResearch.WordTrace tailWord_795341 prefixEnd_795341 363015304202380407448711 := by
  unfold tailWord_795341
  simp only [CollatzResearch.WordTrace]
  refine ⟨29008469411622865273657877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19338979607748576849105251 29008469411622865273657877)
  ·
    refine ⟨1359772003669821809702713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29008469411622865273657877 1359772003669821809702713)
    ·
      refine ⟨1019829002752366357277035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1359772003669821809702713 1019829002752366357277035)
      ·
        refine ⟨1529743504128549535915553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1019829002752366357277035 1529743504128549535915553)
        ·
          refine ⟨1147307628096412151936665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1529743504128549535915553 1147307628096412151936665)
          ·
            refine ⟨860480721072309113952499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1147307628096412151936665 860480721072309113952499)
            ·
              refine ⟨1290721081608463670928749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860480721072309113952499 1290721081608463670928749)
              ·
                refine ⟨484020405603173876598281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1290721081608463670928749 484020405603173876598281)
                ·
                  refine ⟨363015304202380407448711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484020405603173876598281 363015304202380407448711)
                  ·
                    rfl

theorem cell20_795341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_795341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795341 prefixEnd_795341 := by exact prefixLift 795341
  have htrace : WordTrace (prefixWord ++ tailWord_795341) baseStart_795341 baseEnd_795341 := by
    simpa [prefixWord, tailWord_795341, baseEnd_795341] using wordTrace_append hprefix tailTrace_795341
  have hstable : (prefixWord ++ tailWord_795341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795341).length < 2 ^ (prefixWord ++ tailWord_795341).sum := by decide
  have hdescent : baseEnd_795341 < baseStart_795341 := by decide
  rcases family_descends (prefixWord ++ tailWord_795341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795415 : List Nat := [1, 1, 3, 4, 11]
def baseStart_795415 : Nat := 118140960795 + 795415 * 2 ^ 59
def prefixEnd_795415 : Nat := 4983230072969 + 3 ^ 40 * 795415 * 2
def baseEnd_795415 : Nat := 4482087405169938752861

theorem tailTrace_795415 : CollatzResearch.WordTrace tailWord_795415 prefixEnd_795415 4482087405169938752861 := by
  unfold tailWord_795415
  simp only [CollatzResearch.WordTrace]
  refine ⟨29011168413354775911851699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19340778942236517274567799 29011168413354775911851699)
  ·
    refine ⟨43516752620032163867777549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29011168413354775911851699 43516752620032163867777549)
    ·
      refine ⟨16318782232512061450416581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43516752620032163867777549 16318782232512061450416581)
      ·
        refine ⟨3059771668596011521953109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16318782232512061450416581 3059771668596011521953109)
        ·
          refine ⟨4482087405169938752861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3059771668596011521953109 4482087405169938752861)
          ·
            rfl

theorem cell20_795415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 11].length) (baseStart_795415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795415 prefixEnd_795415 := by exact prefixLift 795415
  have htrace : WordTrace (prefixWord ++ tailWord_795415) baseStart_795415 baseEnd_795415 := by
    simpa [prefixWord, tailWord_795415, baseEnd_795415] using wordTrace_append hprefix tailTrace_795415
  have hstable : (prefixWord ++ tailWord_795415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795415).length < 2 ^ (prefixWord ++ tailWord_795415).sum := by decide
  have hdescent : baseEnd_795415 < baseStart_795415 := by decide
  rcases family_descends (prefixWord ++ tailWord_795415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795418 : List Nat := [3, 1, 1, 3, 2, 1, 4, 2, 3]
def baseStart_795418 : Nat := 118140960795 + 795418 * 2 ^ 59
def prefixEnd_795418 : Nat := 4983230072969 + 3 ^ 40 * 795418 * 2
def baseEnd_795418 : Nat := 363050449100510361881729

theorem tailTrace_795418 : CollatzResearch.WordTrace tailWord_795418 prefixEnd_795418 363050449100510361881729 := by
  unfold tailWord_795418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7252819458085976856052727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19340851888229271616140605 7252819458085976856052727)
  ·
    refine ⟨10879229187128965284079091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7252819458085976856052727 10879229187128965284079091)
    ·
      refine ⟨16318843780693447926118637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10879229187128965284079091 16318843780693447926118637)
      ·
        refine ⟨6119566417760042972294489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16318843780693447926118637 6119566417760042972294489)
        ·
          refine ⟨4589674813320032229220867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6119566417760042972294489 4589674813320032229220867)
          ·
            refine ⟨6884512219980048343831301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4589674813320032229220867 6884512219980048343831301)
            ·
              refine ⟨1290846041246259064468369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6884512219980048343831301 1290846041246259064468369)
              ·
                refine ⟨968134530934694298351277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1290846041246259064468369 968134530934694298351277)
                ·
                  refine ⟨363050449100510361881729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 968134530934694298351277 363050449100510361881729)
                  ·
                    rfl

theorem cell20_795418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_795418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795418 prefixEnd_795418 := by exact prefixLift 795418
  have htrace : WordTrace (prefixWord ++ tailWord_795418) baseStart_795418 baseEnd_795418 := by
    simpa [prefixWord, tailWord_795418, baseEnd_795418] using wordTrace_append hprefix tailTrace_795418
  have hstable : (prefixWord ++ tailWord_795418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795418).length < 2 ^ (prefixWord ++ tailWord_795418).sum := by decide
  have hdescent : baseEnd_795418 < baseStart_795418 := by decide
  rcases family_descends (prefixWord ++ tailWord_795418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795428 : List Nat := [2, 3, 1, 3, 4, 1, 1, 5]
def baseStart_795428 : Nat := 118140960795 + 795428 * 2 ^ 59
def prefixEnd_795428 : Nat := 4983230072969 + 3 ^ 40 * 795428 * 2
def baseEnd_795428 : Nat := 121018337790998257182785

theorem tailTrace_795428 : CollatzResearch.WordTrace tailWord_795428 prefixEnd_795428 121018337790998257182785 := by
  unfold tailWord_795428
  simp only [CollatzResearch.WordTrace]
  refine ⟨14505821281153839566037469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19341095041538452754716625 14505821281153839566037469)
  ·
    refine ⟨5439682980432689837264051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14505821281153839566037469 5439682980432689837264051)
    ·
      refine ⟨8159524470649034755896077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5439682980432689837264051 8159524470649034755896077)
      ·
        refine ⟨3059821676493388033461029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8159524470649034755896077 3059821676493388033461029)
        ·
          refine ⟨573716564342510256273943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3059821676493388033461029 573716564342510256273943)
          ·
            refine ⟨860574846513765384410915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573716564342510256273943 860574846513765384410915)
            ·
              refine ⟨1290862269770648076616373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860574846513765384410915 1290862269770648076616373)
              ·
                refine ⟨121018337790998257182785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1290862269770648076616373 121018337790998257182785)
                ·
                  rfl

theorem cell20_795428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 5].length) (baseStart_795428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795428 prefixEnd_795428 := by exact prefixLift 795428
  have htrace : WordTrace (prefixWord ++ tailWord_795428) baseStart_795428 baseEnd_795428 := by
    simpa [prefixWord, tailWord_795428, baseEnd_795428] using wordTrace_append hprefix tailTrace_795428
  have hstable : (prefixWord ++ tailWord_795428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795428).length < 2 ^ (prefixWord ++ tailWord_795428).sum := by decide
  have hdescent : baseEnd_795428 < baseStart_795428 := by decide
  rcases family_descends (prefixWord ++ tailWord_795428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795469 : List Nat := [1, 6, 1, 2, 3, 1, 1, 2, 3]
def baseStart_795469 : Nat := 118140960795 + 795469 * 2 ^ 59
def prefixEnd_795469 : Nat := 4983230072969 + 3 ^ 40 * 795469 * 2
def baseEnd_795469 : Nat := 363073726890180851181521

theorem tailTrace_795469 : CollatzResearch.WordTrace tailWord_795469 prefixEnd_795469 363073726890180851181521 := by
  unfold tailWord_795469
  simp only [CollatzResearch.WordTrace]
  refine ⟨29013137955159143134317461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19342091970106095422878307 29013137955159143134317461)
  ·
    refine ⟨1359990841648084834421131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29013137955159143134317461 1359990841648084834421131)
    ·
      refine ⟨2039986262472127251631697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1359990841648084834421131 2039986262472127251631697)
      ·
        refine ⟨1529989696854095438723773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2039986262472127251631697 1529989696854095438723773)
        ·
          refine ⟨573746136320285789521415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1529989696854095438723773 573746136320285789521415)
          ·
            refine ⟨860619204480428684282123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573746136320285789521415 860619204480428684282123)
            ·
              refine ⟨1290928806720643026423185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860619204480428684282123 1290928806720643026423185)
              ·
                refine ⟨968196605040482269817389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1290928806720643026423185 968196605040482269817389)
                ·
                  refine ⟨363073726890180851181521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 968196605040482269817389 363073726890180851181521)
                  ·
                    rfl

theorem cell20_795469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_795469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795469 prefixEnd_795469 := by exact prefixLift 795469
  have htrace : WordTrace (prefixWord ++ tailWord_795469) baseStart_795469 baseEnd_795469 := by
    simpa [prefixWord, tailWord_795469, baseEnd_795469] using wordTrace_append hprefix tailTrace_795469
  have hstable : (prefixWord ++ tailWord_795469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795469).length < 2 ^ (prefixWord ++ tailWord_795469).sum := by decide
  have hdescent : baseEnd_795469 < baseStart_795469 := by decide
  rcases family_descends (prefixWord ++ tailWord_795469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795473 : List Nat := [1, 2, 2, 1, 6, 2, 1, 2, 3]
def baseStart_795473 : Nat := 118140960795 + 795473 * 2 ^ 59
def prefixEnd_795473 : Nat := 4983230072969 + 3 ^ 40 * 795473 * 2
def baseEnd_795473 : Nat := 363075552599174615048171

theorem tailTrace_795473 : CollatzResearch.WordTrace tailWord_795473 prefixEnd_795473 363075552599174615048171 := by
  unfold tailWord_795473
  simp only [CollatzResearch.WordTrace]
  refine ⟨29013283847144651817463073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19342189231429767878308715 29013283847144651817463073)
  ·
    refine ⟨21759962885358488863097305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29013283847144651817463073 21759962885358488863097305)
    ·
      refine ⟨16319972164018866647322979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21759962885358488863097305 16319972164018866647322979)
      ·
        refine ⟨24479958246028299970984469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16319972164018866647322979 24479958246028299970984469)
        ·
          refine ⟨1147498042782576561139897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24479958246028299970984469 1147498042782576561139897)
          ·
            refine ⟨860623532086932420854923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1147498042782576561139897 860623532086932420854923)
            ·
              refine ⟨1290935298130398631282385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860623532086932420854923 1290935298130398631282385)
              ·
                refine ⟨968201473597798973461789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1290935298130398631282385 968201473597798973461789)
                ·
                  refine ⟨363075552599174615048171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 968201473597798973461789 363075552599174615048171)
                  ·
                    rfl

theorem cell20_795473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 3].length) (baseStart_795473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795473 prefixEnd_795473 := by exact prefixLift 795473
  have htrace : WordTrace (prefixWord ++ tailWord_795473) baseStart_795473 baseEnd_795473 := by
    simpa [prefixWord, tailWord_795473, baseEnd_795473] using wordTrace_append hprefix tailTrace_795473
  have hstable : (prefixWord ++ tailWord_795473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795473).length < 2 ^ (prefixWord ++ tailWord_795473).sum := by decide
  have hdescent : baseEnd_795473 < baseStart_795473 := by decide
  rcases family_descends (prefixWord ++ tailWord_795473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795477 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 5]
def baseStart_795477 : Nat := 118140960795 + 795477 * 2 ^ 59
def prefixEnd_795477 : Nat := 4983230072969 + 3 ^ 40 * 795477 * 2
def baseEnd_795477 : Nat := 363077378308168378914821

theorem tailTrace_795477 : CollatzResearch.WordTrace tailWord_795477 prefixEnd_795477 363077378308168378914821 := by
  unfold tailWord_795477
  simp only [CollatzResearch.WordTrace]
  refine ⟨29013429739130160500608685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19342286492753440333739123 29013429739130160500608685)
  ·
    refine ⟨10880036152173810187728257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29013429739130160500608685 10880036152173810187728257)
    ·
      refine ⟨8160027114130357640796193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10880036152173810187728257 8160027114130357640796193)
      ·
        refine ⟨6120020335597768230597145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8160027114130357640796193 6120020335597768230597145)
        ·
          refine ⟨4590015251698326172947859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6120020335597768230597145 4590015251698326172947859)
          ·
            refine ⟨6885022877547489259421789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4590015251698326172947859 6885022877547489259421789)
            ·
              refine ⟨2581883579080308472283171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6885022877547489259421789 2581883579080308472283171)
              ·
                refine ⟨3872825368620462708424757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2581883579080308472283171 3872825368620462708424757)
                ·
                  refine ⟨363077378308168378914821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3872825368620462708424757 363077378308168378914821)
                  ·
                    rfl

theorem cell20_795477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_795477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795477 prefixEnd_795477 := by exact prefixLift 795477
  have htrace : WordTrace (prefixWord ++ tailWord_795477) baseStart_795477 baseEnd_795477 := by
    simpa [prefixWord, tailWord_795477, baseEnd_795477] using wordTrace_append hprefix tailTrace_795477
  have hstable : (prefixWord ++ tailWord_795477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795477).length < 2 ^ (prefixWord ++ tailWord_795477).sum := by decide
  have hdescent : baseEnd_795477 < baseStart_795477 := by decide
  rcases family_descends (prefixWord ++ tailWord_795477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795490 : List Nat := [3, 3, 2, 1, 3, 1, 3, 1, 3]
def baseStart_795490 : Nat := 118140960795 + 795490 * 2 ^ 59
def prefixEnd_795490 : Nat := 4983230072969 + 3 ^ 40 * 795490 * 2
def baseEnd_795490 : Nat := 363083311862398111481435

theorem tailTrace_795490 : CollatzResearch.WordTrace tailWord_795490 prefixEnd_795490 363083311862398111481435 := by
  unfold tailWord_795490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7253475972020765930207981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19342602592055375813887949 7253475972020765930207981)
  ·
    refine ⟨2720053489507787223827993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7253475972020765930207981 2720053489507787223827993)
    ·
      refine ⟨2040040117130840417870995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2720053489507787223827993 2040040117130840417870995)
      ·
        refine ⟨3060060175696260626806493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2040040117130840417870995 3060060175696260626806493)
        ·
          refine ⟨1147522565886097735052435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3060060175696260626806493 1147522565886097735052435)
          ·
            refine ⟨1721283848829146602578653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1147522565886097735052435 1721283848829146602578653)
            ·
              refine ⟨645481443310929975966995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1721283848829146602578653 645481443310929975966995)
              ·
                refine ⟨968222164966394963950493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645481443310929975966995 968222164966394963950493)
                ·
                  refine ⟨363083311862398111481435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 968222164966394963950493 363083311862398111481435)
                  ·
                    rfl

theorem cell20_795490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_795490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795490 prefixEnd_795490 := by exact prefixLift 795490
  have htrace : WordTrace (prefixWord ++ tailWord_795490) baseStart_795490 baseEnd_795490 := by
    simpa [prefixWord, tailWord_795490, baseEnd_795490] using wordTrace_append hprefix tailTrace_795490
  have hstable : (prefixWord ++ tailWord_795490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795490).length < 2 ^ (prefixWord ++ tailWord_795490).sum := by decide
  have hdescent : baseEnd_795490 < baseStart_795490 := by decide
  rcases family_descends (prefixWord ++ tailWord_795490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795529 : List Nat := [1, 2, 1, 1, 5, 2, 8]
def baseStart_795529 : Nat := 118140960795 + 795529 * 2 ^ 59
def prefixEnd_795529 : Nat := 4983230072969 + 3 ^ 40 * 795529 * 2
def baseEnd_795529 : Nat := 40344568058343034353475

theorem tailTrace_795529 : CollatzResearch.WordTrace tailWord_795529 prefixEnd_795529 40344568058343034353475 := by
  unfold tailWord_795529
  simp only [CollatzResearch.WordTrace]
  refine ⟨29015326334941773381501641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19343550889961182254334427 29015326334941773381501641)
  ·
    refine ⟨21761494751206330036126231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29015326334941773381501641 21761494751206330036126231)
    ·
      refine ⟨32642242126809495054189347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21761494751206330036126231 32642242126809495054189347)
      ·
        refine ⟨48963363190214242581284021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32642242126809495054189347 48963363190214242581284021)
        ·
          refine ⟨4590315299082585241995377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48963363190214242581284021 4590315299082585241995377)
          ·
            refine ⟨3442736474311938931496533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4590315299082585241995377 3442736474311938931496533)
            ·
              refine ⟨40344568058343034353475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3442736474311938931496533 40344568058343034353475)
              ·
                rfl

theorem cell20_795529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 8].length) (baseStart_795529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795529 prefixEnd_795529 := by exact prefixLift 795529
  have htrace : WordTrace (prefixWord ++ tailWord_795529) baseStart_795529 baseEnd_795529 := by
    simpa [prefixWord, tailWord_795529, baseEnd_795529] using wordTrace_append hprefix tailTrace_795529
  have hstable : (prefixWord ++ tailWord_795529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795529).length < 2 ^ (prefixWord ++ tailWord_795529).sum := by decide
  have hdescent : baseEnd_795529 < baseStart_795529 := by decide
  rcases family_descends (prefixWord ++ tailWord_795529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795536 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 9]
def baseStart_795536 : Nat := 118140960795 + 795536 * 2 ^ 59
def prefixEnd_795536 : Nat := 4983230072969 + 3 ^ 40 * 795536 * 2
def baseEnd_795536 : Nat := 363104307515826395947913

theorem tailTrace_795536 : CollatzResearch.WordTrace tailWord_795536 prefixEnd_795536 363104307515826395947913 := by
  unfold tailWord_795536
  simp only [CollatzResearch.WordTrace]
  refine ⟨14507790822958206788503231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19343721097277609051337641 14507790822958206788503231)
  ·
    refine ⟨21761686234437310182754847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14507790822958206788503231 21761686234437310182754847)
    ·
      refine ⟨32642529351655965274132271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21761686234437310182754847 32642529351655965274132271)
      ·
        refine ⟨48963794027483947911198407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32642529351655965274132271 48963794027483947911198407)
        ·
          refine ⟨73445691041225921866797611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48963794027483947911198407 73445691041225921866797611)
          ·
            refine ⟨110168536561838882800196417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73445691041225921866797611 110168536561838882800196417)
            ·
              refine ⟨82626402421379162100147313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110168536561838882800196417 82626402421379162100147313)
              ·
                refine ⟨61969801816034371575110485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82626402421379162100147313 61969801816034371575110485)
                ·
                  refine ⟨363104307515826395947913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61969801816034371575110485 363104307515826395947913)
                  ·
                    rfl

theorem cell20_795536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_795536 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795536 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795536 prefixEnd_795536 := by exact prefixLift 795536
  have htrace : WordTrace (prefixWord ++ tailWord_795536) baseStart_795536 baseEnd_795536 := by
    simpa [prefixWord, tailWord_795536, baseEnd_795536] using wordTrace_append hprefix tailTrace_795536
  have hstable : (prefixWord ++ tailWord_795536).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795536).length < 2 ^ (prefixWord ++ tailWord_795536).sum := by decide
  have hdescent : baseEnd_795536 < baseStart_795536 := by decide
  rcases family_descends (prefixWord ++ tailWord_795536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795542 : List Nat := [5, 3, 1, 1, 1, 1, 1, 7]
def baseStart_795542 : Nat := 118140960795 + 795542 * 2 ^ 59
def prefixEnd_795542 : Nat := 4983230072969 + 3 ^ 40 * 795542 * 2
def baseEnd_795542 : Nat := 121035682026439013915963

theorem tailTrace_795542 : CollatzResearch.WordTrace tailWord_795542 prefixEnd_795542 121035682026439013915963 := by
  unfold tailWord_795542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1813487530243417287607805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19343866989263117734483253 1813487530243417287607805)
  ·
    refine ⟨680057823841281482852927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1813487530243417287607805 680057823841281482852927)
    ·
      refine ⟨1020086735761922224279391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 680057823841281482852927 1020086735761922224279391)
      ·
        refine ⟨1530130103642883336419087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020086735761922224279391 1530130103642883336419087)
        ·
          refine ⟨2295195155464325004628631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1530130103642883336419087 2295195155464325004628631)
          ·
            refine ⟨3442792733196487506942947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295195155464325004628631 3442792733196487506942947)
            ·
              refine ⟨5164189099794731260414421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3442792733196487506942947 5164189099794731260414421)
              ·
                refine ⟨121035682026439013915963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5164189099794731260414421 121035682026439013915963)
                ·
                  rfl

theorem cell20_795542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_795542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795542 prefixEnd_795542 := by exact prefixLift 795542
  have htrace : WordTrace (prefixWord ++ tailWord_795542) baseStart_795542 baseEnd_795542 := by
    simpa [prefixWord, tailWord_795542, baseEnd_795542] using wordTrace_append hprefix tailTrace_795542
  have hstable : (prefixWord ++ tailWord_795542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795542).length < 2 ^ (prefixWord ++ tailWord_795542).sum := by decide
  have hdescent : baseEnd_795542 < baseStart_795542 := by decide
  rcases family_descends (prefixWord ++ tailWord_795542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795591 : List Nat := [1, 1, 4, 1, 1, 2, 3, 4, 3]
def baseStart_795591 : Nat := 118140960795 + 795591 * 2 ^ 59
def prefixEnd_795591 : Nat := 4983230072969 + 3 ^ 40 * 795591 * 2
def baseEnd_795591 : Nat := 363129411014490649114355

theorem tailTrace_795591 : CollatzResearch.WordTrace tailWord_795591 prefixEnd_795591 363129411014490649114355 := by
  unfold tailWord_795591
  simp only [CollatzResearch.WordTrace]
  refine ⟨29017587660717157970258627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19345058440478105313505751 29017587660717157970258627)
  ·
    refine ⟨43526381491075736955387941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29017587660717157970258627 43526381491075736955387941)
    ·
      refine ⟨8161196529576700679135239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43526381491075736955387941 8161196529576700679135239)
      ·
        refine ⟨12241794794365051018702859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8161196529576700679135239 12241794794365051018702859)
        ·
          refine ⟨18362692191547576528054289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12241794794365051018702859 18362692191547576528054289)
          ·
            refine ⟨13772019143660682396040717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18362692191547576528054289 13772019143660682396040717)
            ·
              refine ⟨5164507178872755898515269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13772019143660682396040717 5164507178872755898515269)
              ·
                refine ⟨968345096038641730971613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5164507178872755898515269 968345096038641730971613)
                ·
                  refine ⟨363129411014490649114355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 968345096038641730971613 363129411014490649114355)
                  ·
                    rfl

theorem cell20_795591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 3].length) (baseStart_795591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795591 prefixEnd_795591 := by exact prefixLift 795591
  have htrace : WordTrace (prefixWord ++ tailWord_795591) baseStart_795591 baseEnd_795591 := by
    simpa [prefixWord, tailWord_795591, baseEnd_795591] using wordTrace_append hprefix tailTrace_795591
  have hstable : (prefixWord ++ tailWord_795591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795591).length < 2 ^ (prefixWord ++ tailWord_795591).sum := by decide
  have hdescent : baseEnd_795591 < baseStart_795591 := by decide
  rcases family_descends (prefixWord ++ tailWord_795591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795615 : List Nat := [1, 1, 2, 3, 5, 1, 1, 2, 4]
def baseStart_795615 : Nat := 118140960795 + 795615 * 2 ^ 59
def prefixEnd_795615 : Nat := 4983230072969 + 3 ^ 40 * 795615 * 2
def baseEnd_795615 : Nat := 363140365268453232314257

theorem tailTrace_795615 : CollatzResearch.WordTrace tailWord_795615 prefixEnd_795615 363140365268453232314257 := by
  unfold tailWord_795615
  simp only [CollatzResearch.WordTrace]
  refine ⟨29018463012630210069132299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19345642008420140046088199 29018463012630210069132299)
  ·
    refine ⟨43527694518945315103698449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29018463012630210069132299 43527694518945315103698449)
    ·
      refine ⟨32645770889208986327773837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43527694518945315103698449 32645770889208986327773837)
      ·
        refine ⟨12242164083453369872915189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32645770889208986327773837 12242164083453369872915189)
        ·
          refine ⟨1147702882823753425585799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12242164083453369872915189 1147702882823753425585799)
          ·
            refine ⟨1721554324235630138378699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1147702882823753425585799 1721554324235630138378699)
            ·
              refine ⟨2582331486353445207568049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1721554324235630138378699 2582331486353445207568049)
              ·
                refine ⟨1936748614765083905676037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2582331486353445207568049 1936748614765083905676037)
                ·
                  refine ⟨363140365268453232314257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1936748614765083905676037 363140365268453232314257)
                  ·
                    rfl

theorem cell20_795615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 4].length) (baseStart_795615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795615 prefixEnd_795615 := by exact prefixLift 795615
  have htrace : WordTrace (prefixWord ++ tailWord_795615) baseStart_795615 baseEnd_795615 := by
    simpa [prefixWord, tailWord_795615, baseEnd_795615] using wordTrace_append hprefix tailTrace_795615
  have hstable : (prefixWord ++ tailWord_795615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795615).length < 2 ^ (prefixWord ++ tailWord_795615).sum := by decide
  have hdescent : baseEnd_795615 < baseStart_795615 := by decide
  rcases family_descends (prefixWord ++ tailWord_795615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795618 : List Nat := [3, 3, 3, 1, 1, 2, 3, 4]
def baseStart_795618 : Nat := 118140960795 + 795618 * 2 ^ 59
def prefixEnd_795618 : Nat := 4983230072969 + 3 ^ 40 * 795618 * 2
def baseEnd_795618 : Nat := 121047244850066185071415

theorem tailTrace_795618 : CollatzResearch.WordTrace tailWord_795618 prefixEnd_795618 121047244850066185071415 := by
  unfold tailWord_795618
  simp only [CollatzResearch.WordTrace]
  refine ⟨7254643107904835395372877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19345714954412894387661005 7254643107904835395372877)
  ·
    refine ⟨2720491165464313273264829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7254643107904835395372877 2720491165464313273264829)
    ·
      refine ⟨1020184187049117477474311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2720491165464313273264829 1020184187049117477474311)
      ·
        refine ⟨1530276280573676216211467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020184187049117477474311 1530276280573676216211467)
        ·
          refine ⟨2295414420860514324317201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1530276280573676216211467 2295414420860514324317201)
          ·
            refine ⟨1721560815645385743237901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2295414420860514324317201 1721560815645385743237901)
            ·
              refine ⟨645585305867019653714213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1721560815645385743237901 645585305867019653714213)
              ·
                refine ⟨121047244850066185071415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 645585305867019653714213 121047244850066185071415)
                ·
                  rfl

theorem cell20_795618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_795618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795618 prefixEnd_795618 := by exact prefixLift 795618
  have htrace : WordTrace (prefixWord ++ tailWord_795618) baseStart_795618 baseEnd_795618 := by
    simpa [prefixWord, tailWord_795618, baseEnd_795618] using wordTrace_append hprefix tailTrace_795618
  have hstable : (prefixWord ++ tailWord_795618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795618).length < 2 ^ (prefixWord ++ tailWord_795618).sum := by decide
  have hdescent : baseEnd_795618 < baseStart_795618 := by decide
  rcases family_descends (prefixWord ++ tailWord_795618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795653 : List Nat := [1, 3, 1, 1, 2, 3, 1, 6, 2]
def baseStart_795653 : Nat := 118140960795 + 795653 * 2 ^ 59
def prefixEnd_795653 : Nat := 4983230072969 + 3 ^ 40 * 795653 * 2
def baseEnd_795653 : Nat := 363157709503893989047435

theorem tailTrace_795653 : CollatzResearch.WordTrace tailWord_795653 prefixEnd_795653 363157709503893989047435 := by
  unfold tailWord_795653
  simp only [CollatzResearch.WordTrace]
  refine ⟨29019848986492542559015613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19346565990995028372677075 29019848986492542559015613)
  ·
    refine ⟨10882443369934703459630855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29019848986492542559015613 10882443369934703459630855)
    ·
      refine ⟨16323665054902055189446283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10882443369934703459630855 16323665054902055189446283)
      ·
        refine ⟨24485497582353082784169425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16323665054902055189446283 24485497582353082784169425)
        ·
          refine ⟨18364123186764812088127069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24485497582353082784169425 18364123186764812088127069)
          ·
            refine ⟨6886546195036804533047651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18364123186764812088127069 6886546195036804533047651)
            ·
              refine ⟨10329819292555206799571477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6886546195036804533047651 10329819292555206799571477)
              ·
                refine ⟨484210279338525318729913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10329819292555206799571477 484210279338525318729913)
                ·
                  refine ⟨363157709503893989047435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484210279338525318729913 363157709503893989047435)
                  ·
                    rfl

theorem cell20_795653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_795653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795653 prefixEnd_795653 := by exact prefixLift 795653
  have htrace : WordTrace (prefixWord ++ tailWord_795653) baseStart_795653 baseEnd_795653 := by
    simpa [prefixWord, tailWord_795653, baseEnd_795653] using wordTrace_append hprefix tailTrace_795653
  have hstable : (prefixWord ++ tailWord_795653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795653).length < 2 ^ (prefixWord ++ tailWord_795653).sum := by decide
  have hdescent : baseEnd_795653 < baseStart_795653 := by decide
  rcases family_descends (prefixWord ++ tailWord_795653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795674 : List Nat := [3, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_795674 : Nat := 118140960795 + 795674 * 2 ^ 59
def prefixEnd_795674 : Nat := 4983230072969 + 3 ^ 40 * 795674 * 2
def baseEnd_795674 : Nat := 363167294476111249347349

theorem tailTrace_795674 : CollatzResearch.WordTrace tailWord_795674 prefixEnd_795674 363167294476111249347349 := by
  unfold tailWord_795674
  simp only [CollatzResearch.WordTrace]
  refine ⟨7255153729854115786382519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19347076612944308763686717 7255153729854115786382519)
  ·
    refine ⟨10882730594781173679573779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7255153729854115786382519 10882730594781173679573779)
    ·
      refine ⟨16324095892171760519360669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10882730594781173679573779 16324095892171760519360669)
      ·
        refine ⟨6121535959564410194760251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16324095892171760519360669 6121535959564410194760251)
        ·
          refine ⟨9182303939346615292140377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6121535959564410194760251 9182303939346615292140377)
          ·
            refine ⟨6886727954509961469105283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9182303939346615292140377 6886727954509961469105283)
            ·
              refine ⟨10330091931764942203657925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6886727954509961469105283 10330091931764942203657925)
              ·
                refine ⟨1936892237205926663185861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10330091931764942203657925 1936892237205926663185861)
                ·
                  refine ⟨363167294476111249347349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1936892237205926663185861 363167294476111249347349)
                  ·
                    rfl

theorem cell20_795674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_795674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795674 prefixEnd_795674 := by exact prefixLift 795674
  have htrace : WordTrace (prefixWord ++ tailWord_795674) baseStart_795674 baseEnd_795674 := by
    simpa [prefixWord, tailWord_795674, baseEnd_795674] using wordTrace_append hprefix tailTrace_795674
  have hstable : (prefixWord ++ tailWord_795674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795674).length < 2 ^ (prefixWord ++ tailWord_795674).sum := by decide
  have hdescent : baseEnd_795674 < baseStart_795674 := by decide
  rcases family_descends (prefixWord ++ tailWord_795674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795687 : List Nat := [1, 1, 7, 1, 1, 1, 3, 3, 2]
def baseStart_795687 : Nat := 118140960795 + 795687 * 2 ^ 59
def prefixEnd_795687 : Nat := 4983230072969 + 3 ^ 40 * 795687 * 2
def baseEnd_795687 : Nat := 363173228030340981913963

theorem tailTrace_795687 : CollatzResearch.WordTrace tailWord_795687 prefixEnd_795687 363173228030340981913963 := by
  unfold tailWord_795687
  simp only [CollatzResearch.WordTrace]
  refine ⟨29021089068369366365753315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19347392712246244243835543 29021089068369366365753315)
  ·
    refine ⟨43531633602554049548629973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29021089068369366365753315 43531633602554049548629973)
    ·
      refine ⟨1020272662559860536296015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 43531633602554049548629973 1020272662559860536296015)
      ·
        refine ⟨1530408993839790804444023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020272662559860536296015 1530408993839790804444023)
        ·
          refine ⟨2295613490759686206666035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1530408993839790804444023 2295613490759686206666035)
          ·
            refine ⟨3443420236139529309999053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295613490759686206666035 3443420236139529309999053)
            ·
              refine ⟨1291282588552323491249645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3443420236139529309999053 1291282588552323491249645)
              ·
                refine ⟨484230970707121309218617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1291282588552323491249645 484230970707121309218617)
                ·
                  refine ⟨363173228030340981913963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484230970707121309218617 363173228030340981913963)
                  ·
                    rfl

theorem cell20_795687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 2].length) (baseStart_795687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795687 prefixEnd_795687 := by exact prefixLift 795687
  have htrace : WordTrace (prefixWord ++ tailWord_795687) baseStart_795687 baseEnd_795687 := by
    simpa [prefixWord, tailWord_795687, baseEnd_795687] using wordTrace_append hprefix tailTrace_795687
  have hstable : (prefixWord ++ tailWord_795687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795687).length < 2 ^ (prefixWord ++ tailWord_795687).sum := by decide
  have hdescent : baseEnd_795687 < baseStart_795687 := by decide
  rcases family_descends (prefixWord ++ tailWord_795687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795705 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 5]
def baseStart_795705 : Nat := 118140960795 + 795705 * 2 ^ 59
def prefixEnd_795705 : Nat := 4983230072969 + 3 ^ 40 * 795705 * 2
def baseEnd_795705 : Nat := 363181443720812919313889

theorem tailTrace_795705 : CollatzResearch.WordTrace tailWord_795705 prefixEnd_795705 363181443720812919313889 := by
  unfold tailWord_795705
  simp only [CollatzResearch.WordTrace]
  refine ⟨29021745582304155439908569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19347830388202770293272379 29021745582304155439908569)
  ·
    refine ⟨21766309186728116579931427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29021745582304155439908569 21766309186728116579931427)
    ·
      refine ⟨32649463780092174869897141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21766309186728116579931427 32649463780092174869897141)
      ·
        refine ⟨3060887229383641394052857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32649463780092174869897141 3060887229383641394052857)
        ·
          refine ⟨2295665422037731045539643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3060887229383641394052857 2295665422037731045539643)
          ·
            refine ⟨3443498133056596568309465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295665422037731045539643 3443498133056596568309465)
            ·
              refine ⟨2582623599792447426232099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3443498133056596568309465 2582623599792447426232099)
              ·
                refine ⟨3873935399688671139348149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2582623599792447426232099 3873935399688671139348149)
                ·
                  refine ⟨363181443720812919313889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3873935399688671139348149 363181443720812919313889)
                  ·
                    rfl

theorem cell20_795705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_795705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795705 prefixEnd_795705 := by exact prefixLift 795705
  have htrace : WordTrace (prefixWord ++ tailWord_795705) baseStart_795705 baseEnd_795705 := by
    simpa [prefixWord, tailWord_795705, baseEnd_795705] using wordTrace_append hprefix tailTrace_795705
  have hstable : (prefixWord ++ tailWord_795705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795705).length < 2 ^ (prefixWord ++ tailWord_795705).sum := by decide
  have hdescent : baseEnd_795705 < baseStart_795705 := by decide
  rcases family_descends (prefixWord ++ tailWord_795705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795718 : List Nat := [6, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_795718 : Nat := 118140960795 + 795718 * 2 ^ 59
def prefixEnd_795718 : Nat := 4983230072969 + 3 ^ 40 * 795718 * 2
def baseEnd_795718 : Nat := 363187377275042651880503

theorem tailTrace_795718 : CollatzResearch.WordTrace tailWord_795718 prefixEnd_795718 363187377275042651880503 := by
  unfold tailWord_795718
  simp only [CollatzResearch.WordTrace]
  refine ⟨906944366601783083129119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19348146487504705773421205 906944366601783083129119)
  ·
    refine ⟨1360416549902674624693679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 906944366601783083129119 1360416549902674624693679)
    ·
      refine ⟨2040624824854011937040519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1360416549902674624693679 2040624824854011937040519)
      ·
        refine ⟨3060937237281017905560779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2040624824854011937040519 3060937237281017905560779)
        ·
          refine ⟨4591405855921526858341169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3060937237281017905560779 4591405855921526858341169)
          ·
            refine ⟨3443554391941145143755877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4591405855921526858341169 3443554391941145143755877)
            ·
              refine ⟨645666448488964714454227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3443554391941145143755877 645666448488964714454227)
              ·
                refine ⟨968499672733447071681341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645666448488964714454227 968499672733447071681341)
                ·
                  refine ⟨363187377275042651880503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 968499672733447071681341 363187377275042651880503)
                  ·
                    rfl

theorem cell20_795718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_795718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795718 prefixEnd_795718 := by exact prefixLift 795718
  have htrace : WordTrace (prefixWord ++ tailWord_795718) baseStart_795718 baseEnd_795718 := by
    simpa [prefixWord, tailWord_795718, baseEnd_795718] using wordTrace_append hprefix tailTrace_795718
  have hstable : (prefixWord ++ tailWord_795718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795718).length < 2 ^ (prefixWord ++ tailWord_795718).sum := by decide
  have hdescent : baseEnd_795718 < baseStart_795718 := by decide
  rcases family_descends (prefixWord ++ tailWord_795718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795719 : List Nat := [1, 1, 4, 1, 3, 2, 1, 7]
def baseStart_795719 : Nat := 118140960795 + 795719 * 2 ^ 59
def prefixEnd_795719 : Nat := 4983230072969 + 3 ^ 40 * 795719 * 2
def baseEnd_795719 : Nat := 121062611234097030949055

theorem tailTrace_795719 : CollatzResearch.WordTrace tailWord_795719 prefixEnd_795719 121062611234097030949055 := by
  unfold tailWord_795719
  simp only [CollatzResearch.WordTrace]
  refine ⟨29022256204253435830918211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19348170802835623887278807 29022256204253435830918211)
  ·
    refine ⟨43533384306380153746377317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29022256204253435830918211 43533384306380153746377317)
    ·
      refine ⟨8162509557446278827445747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43533384306380153746377317 8162509557446278827445747)
      ·
        refine ⟨12243764336169418241168621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8162509557446278827445747 12243764336169418241168621)
        ·
          refine ⟨4591411626063531840438233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12243764336169418241168621 4591411626063531840438233)
          ·
            refine ⟨3443558719547648880328675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4591411626063531840438233 3443558719547648880328675)
            ·
              refine ⟨5165338079321473320493013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3443558719547648880328675 5165338079321473320493013)
              ·
                refine ⟨121062611234097030949055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5165338079321473320493013 121062611234097030949055)
                ·
                  rfl

theorem cell20_795719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 7].length) (baseStart_795719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795719 prefixEnd_795719 := by exact prefixLift 795719
  have htrace : WordTrace (prefixWord ++ tailWord_795719) baseStart_795719 baseEnd_795719 := by
    simpa [prefixWord, tailWord_795719, baseEnd_795719] using wordTrace_append hprefix tailTrace_795719
  have hstable : (prefixWord ++ tailWord_795719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795719).length < 2 ^ (prefixWord ++ tailWord_795719).sum := by decide
  have hdescent : baseEnd_795719 < baseStart_795719 := by decide
  rcases family_descends (prefixWord ++ tailWord_795719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795722 : List Nat := [3, 1, 2, 1, 1, 2, 6, 1, 3]
def baseStart_795722 : Nat := 118140960795 + 795722 * 2 ^ 59
def prefixEnd_795722 : Nat := 4983230072969 + 3 ^ 40 * 795722 * 2
def baseEnd_795722 : Nat := 363189202984036415747153

theorem tailTrace_795722 : CollatzResearch.WordTrace tailWord_795722 prefixEnd_795722 363189202984036415747153 := by
  unfold tailWord_795722
  simp only [CollatzResearch.WordTrace]
  refine ⟨7255591405810641835819355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19348243748828378228851613 7255591405810641835819355)
  ·
    refine ⟨10883387108715962753729033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7255591405810641835819355 10883387108715962753729033)
    ·
      refine ⟨8162540331536972065296775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10883387108715962753729033 8162540331536972065296775)
      ·
        refine ⟨12243810497305458097945163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8162540331536972065296775 12243810497305458097945163)
        ·
          refine ⟨18365715745958187146917745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12243810497305458097945163 18365715745958187146917745)
          ·
            refine ⟨13774286809468640360188309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18365715745958187146917745 13774286809468640360188309)
            ·
              refine ⟨645669694193842516883827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13774286809468640360188309 645669694193842516883827)
              ·
                refine ⟨968504541290763775325741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645669694193842516883827 968504541290763775325741)
                ·
                  refine ⟨363189202984036415747153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 968504541290763775325741 363189202984036415747153)
                  ·
                    rfl

theorem cell20_795722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_795722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795722 prefixEnd_795722 := by exact prefixLift 795722
  have htrace : WordTrace (prefixWord ++ tailWord_795722) baseStart_795722 baseEnd_795722 := by
    simpa [prefixWord, tailWord_795722, baseEnd_795722] using wordTrace_append hprefix tailTrace_795722
  have hstable : (prefixWord ++ tailWord_795722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795722).length < 2 ^ (prefixWord ++ tailWord_795722).sum := by decide
  have hdescent : baseEnd_795722 < baseStart_795722 := by decide
  rcases family_descends (prefixWord ++ tailWord_795722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795757 : List Nat := [1, 5, 1, 1, 2, 10]
def baseStart_795757 : Nat := 118140960795 + 795757 * 2 ^ 59
def prefixEnd_795757 : Nat := 4983230072969 + 3 ^ 40 * 795757 * 2
def baseEnd_795757 : Nat := 13452043627323401836309

theorem tailTrace_795757 : CollatzResearch.WordTrace tailWord_795757 prefixEnd_795757 13452043627323401836309 := by
  unfold tailWord_795757
  simp only [CollatzResearch.WordTrace]
  refine ⟨29023642178115768320801525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19349094785410512213867683 29023642178115768320801525)
  ·
    refine ⟨2720966454198353280075143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29023642178115768320801525 2720966454198353280075143)
    ·
      refine ⟨4081449681297529920112715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2720966454198353280075143 4081449681297529920112715)
      ·
        refine ⟨6122174521946294880169073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4081449681297529920112715 6122174521946294880169073)
        ·
          refine ⟨4591630891459721160126805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6122174521946294880169073 4591630891459721160126805)
          ·
            refine ⟨13452043627323401836309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4591630891459721160126805 13452043627323401836309)
            ·
              rfl

theorem cell20_795757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 10].length) (baseStart_795757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795757 prefixEnd_795757 := by exact prefixLift 795757
  have htrace : WordTrace (prefixWord ++ tailWord_795757) baseStart_795757 baseEnd_795757 := by
    simpa [prefixWord, tailWord_795757, baseEnd_795757] using wordTrace_append hprefix tailTrace_795757
  have hstable : (prefixWord ++ tailWord_795757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795757).length < 2 ^ (prefixWord ++ tailWord_795757).sum := by decide
  have hdescent : baseEnd_795757 < baseStart_795757 := by decide
  rcases family_descends (prefixWord ++ tailWord_795757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795767 : List Nat := [1, 1, 3, 1, 1, 4, 3, 4, 2]
def baseStart_795767 : Nat := 118140960795 + 795767 * 2 ^ 59
def prefixEnd_795767 : Nat := 4983230072969 + 3 ^ 40 * 795767 * 2
def baseEnd_795767 : Nat := 363209742210216259246969

theorem tailTrace_795767 : CollatzResearch.WordTrace tailWord_795767 prefixEnd_795767 363209742210216259246969 := by
  unfold tailWord_795767
  simp only [CollatzResearch.WordTrace]
  refine ⟨29024006908079540028665555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19349337938719693352443703 29024006908079540028665555)
  ·
    refine ⟨43536010362119310042998333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29024006908079540028665555 43536010362119310042998333)
    ·
      refine ⟨16326003885794741266124375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43536010362119310042998333 16326003885794741266124375)
      ·
        refine ⟨24489005828692111899186563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16326003885794741266124375 24489005828692111899186563)
        ·
          refine ⟨36733508743038167848779845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24489005828692111899186563 36733508743038167848779845)
          ·
            refine ⟨6887532889319656471646221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36733508743038167848779845 6887532889319656471646221)
            ·
              refine ⟨2582824833494871176867333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6887532889319656471646221 2582824833494871176867333)
              ·
                refine ⟨484279656280288345662625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2582824833494871176867333 484279656280288345662625)
                ·
                  refine ⟨363209742210216259246969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484279656280288345662625 363209742210216259246969)
                  ·
                    rfl

theorem cell20_795767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 4, 2].length) (baseStart_795767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795767 prefixEnd_795767 := by exact prefixLift 795767
  have htrace : WordTrace (prefixWord ++ tailWord_795767) baseStart_795767 baseEnd_795767 := by
    simpa [prefixWord, tailWord_795767, baseEnd_795767] using wordTrace_append hprefix tailTrace_795767
  have hstable : (prefixWord ++ tailWord_795767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795767).length < 2 ^ (prefixWord ++ tailWord_795767).sum := by decide
  have hdescent : baseEnd_795767 < baseStart_795767 := by decide
  rcases family_descends (prefixWord ++ tailWord_795767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795771 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 8]
def baseStart_795771 : Nat := 118140960795 + 795771 * 2 ^ 59
def prefixEnd_795771 : Nat := 4983230072969 + 3 ^ 40 * 795771 * 2
def baseEnd_795771 : Nat := 363211567919210023113619

theorem tailTrace_795771 : CollatzResearch.WordTrace tailWord_795771 prefixEnd_795771 363211567919210023113619 := by
  unfold tailWord_795771
  simp only [CollatzResearch.WordTrace]
  refine ⟨29024152800065048711811167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19349435200043365807874111 29024152800065048711811167)
  ·
    refine ⟨43536229200097573067716751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29024152800065048711811167 43536229200097573067716751)
    ·
      refine ⟨65304343800146359601575127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43536229200097573067716751 65304343800146359601575127)
      ·
        refine ⟨97956515700219539402362691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65304343800146359601575127 97956515700219539402362691)
        ·
          refine ⟨146934773550329309103544037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97956515700219539402362691 146934773550329309103544037)
          ·
            refine ⟨27550270040686745456914507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 146934773550329309103544037 27550270040686745456914507)
            ·
              refine ⟨41325405061030118185371761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27550270040686745456914507 41325405061030118185371761)
              ·
                refine ⟨30994053795772588639028821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41325405061030118185371761 30994053795772588639028821)
                ·
                  refine ⟨363211567919210023113619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30994053795772588639028821 363211567919210023113619)
                  ·
                    rfl

theorem cell20_795771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_795771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795771 prefixEnd_795771 := by exact prefixLift 795771
  have htrace : WordTrace (prefixWord ++ tailWord_795771) baseStart_795771 baseEnd_795771 := by
    simpa [prefixWord, tailWord_795771, baseEnd_795771] using wordTrace_append hprefix tailTrace_795771
  have hstable : (prefixWord ++ tailWord_795771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795771).length < 2 ^ (prefixWord ++ tailWord_795771).sum := by decide
  have hdescent : baseEnd_795771 < baseStart_795771 := by decide
  rcases family_descends (prefixWord ++ tailWord_795771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795815 : List Nat := [1, 1, 6, 2, 1, 3, 1, 2, 3]
def baseStart_795815 : Nat := 118140960795 + 795815 * 2 ^ 59
def prefixEnd_795815 : Nat := 4983230072969 + 3 ^ 40 * 795815 * 2
def baseEnd_795815 : Nat := 363231650718141425646773

theorem tailTrace_795815 : CollatzResearch.WordTrace tailWord_795815 prefixEnd_795815 363231650718141425646773 := by
  unfold tailWord_795815
  simp only [CollatzResearch.WordTrace]
  refine ⟨29025757611905644226412899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19350505074603762817608599 29025757611905644226412899)
  ·
    refine ⟨43538636417858466339619349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29025757611905644226412899 43538636417858466339619349)
    ·
      refine ⟨2040873582087115609669657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43538636417858466339619349 2040873582087115609669657)
      ·
        refine ⟨1530655186565336707252243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2040873582087115609669657 1530655186565336707252243)
        ·
          refine ⟨2295982779848005060878365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1530655186565336707252243 2295982779848005060878365)
          ·
            refine ⟨860993542443001897829387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2295982779848005060878365 860993542443001897829387)
            ·
              refine ⟨1291490313664502846744081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 860993542443001897829387 1291490313664502846744081)
              ·
                refine ⟨968617735248377135058061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1291490313664502846744081 968617735248377135058061)
                ·
                  refine ⟨363231650718141425646773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 968617735248377135058061 363231650718141425646773)
                  ·
                    rfl

theorem cell20_795815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 3].length) (baseStart_795815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795815 prefixEnd_795815 := by exact prefixLift 795815
  have htrace : WordTrace (prefixWord ++ tailWord_795815) baseStart_795815 baseEnd_795815 := by
    simpa [prefixWord, tailWord_795815, baseEnd_795815] using wordTrace_append hprefix tailTrace_795815
  have hstable : (prefixWord ++ tailWord_795815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795815).length < 2 ^ (prefixWord ++ tailWord_795815).sum := by decide
  have hdescent : baseEnd_795815 < baseStart_795815 := by decide
  rcases family_descends (prefixWord ++ tailWord_795815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795826 : List Nat := [3, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_795826 : Nat := 118140960795 + 795826 * 2 ^ 59
def prefixEnd_795826 : Nat := 4983230072969 + 3 ^ 40 * 795826 * 2
def baseEnd_795826 : Nat := 363236671417874276280061

theorem tailTrace_795826 : CollatzResearch.WordTrace tailWord_795826 prefixEnd_795826 363236671417874276280061 := by
  unfold tailWord_795826
  simp only [CollatzResearch.WordTrace]
  refine ⟨7256539703716448276265833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19350772543243862070042221 7256539703716448276265833)
  ·
    refine ⟨5442404777787336207199375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7256539703716448276265833 5442404777787336207199375)
    ·
      refine ⟨8163607166681004310799063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5442404777787336207199375 8163607166681004310799063)
      ·
        refine ⟨12245410750021506466198595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8163607166681004310799063 12245410750021506466198595)
        ·
          refine ⟨18368116125032259699297893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12245410750021506466198595 18368116125032259699297893)
          ·
            refine ⟨3444021773443548693618355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18368116125032259699297893 3444021773443548693618355)
            ·
              refine ⟨5166032660165323040427533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3444021773443548693618355 5166032660165323040427533)
              ·
                refine ⟨1937262247561996140160325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5166032660165323040427533 1937262247561996140160325)
                ·
                  refine ⟨363236671417874276280061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1937262247561996140160325 363236671417874276280061)
                  ·
                    rfl

theorem cell20_795826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_795826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795826 prefixEnd_795826 := by exact prefixLift 795826
  have htrace : WordTrace (prefixWord ++ tailWord_795826) baseStart_795826 baseEnd_795826 := by
    simpa [prefixWord, tailWord_795826, baseEnd_795826] using wordTrace_append hprefix tailTrace_795826
  have hstable : (prefixWord ++ tailWord_795826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795826).length < 2 ^ (prefixWord ++ tailWord_795826).sum := by decide
  have hdescent : baseEnd_795826 < baseStart_795826 := by decide
  rcases family_descends (prefixWord ++ tailWord_795826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795842 : List Nat := [3, 5, 1, 1, 3, 1, 2, 4]
def baseStart_795842 : Nat := 118140960795 + 795842 * 2 ^ 59
def prefixEnd_795842 : Nat := 4983230072969 + 3 ^ 40 * 795842 * 2
def baseEnd_795842 : Nat := 121081324751283110582221

theorem tailTrace_795842 : CollatzResearch.WordTrace tailWord_795842 prefixEnd_795842 121081324751283110582221 := by
  unfold tailWord_795842
  simp only [CollatzResearch.WordTrace]
  refine ⟨7256685595701956959411445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19351161588538551891763853 7256685595701956959411445)
  ·
    refine ⟨680314274597058464944823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7256685595701956959411445 680314274597058464944823)
    ·
      refine ⟨1020471411895587697417235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 680314274597058464944823 1020471411895587697417235)
      ·
        refine ⟨1530707117843381546125853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020471411895587697417235 1530707117843381546125853)
        ·
          refine ⟨574015169191268079797195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1530707117843381546125853 574015169191268079797195)
          ·
            refine ⟨861022753786902119695793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574015169191268079797195 861022753786902119695793)
            ·
              refine ⟨645767065340176589771845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 861022753786902119695793 645767065340176589771845)
              ·
                refine ⟨121081324751283110582221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 645767065340176589771845 121081324751283110582221)
                ·
                  rfl

theorem cell20_795842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_795842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795842 prefixEnd_795842 := by exact prefixLift 795842
  have htrace : WordTrace (prefixWord ++ tailWord_795842) baseStart_795842 baseEnd_795842 := by
    simpa [prefixWord, tailWord_795842, baseEnd_795842] using wordTrace_append hprefix tailTrace_795842
  have hstable : (prefixWord ++ tailWord_795842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795842).length < 2 ^ (prefixWord ++ tailWord_795842).sum := by decide
  have hdescent : baseEnd_795842 < baseStart_795842 := by decide
  rcases family_descends (prefixWord ++ tailWord_795842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795850 : List Nat := [3, 1, 2, 1, 3, 2, 4, 4]
def baseStart_795850 : Nat := 118140960795 + 795850 * 2 ^ 59
def prefixEnd_795850 : Nat := 4983230072969 + 3 ^ 40 * 795850 * 2
def baseEnd_795850 : Nat := 121082541890612286493321

theorem tailTrace_795850 : CollatzResearch.WordTrace tailWord_795850 prefixEnd_795850 121082541890612286493321 := by
  unfold tailWord_795850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7256758541694711300984251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19351356111185896802624669 7256758541694711300984251)
  ·
    refine ⟨10885137812542066951476377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7256758541694711300984251 10885137812542066951476377)
    ·
      refine ⟨8163853359406550213607283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10885137812542066951476377 8163853359406550213607283)
      ·
        refine ⟨12245780039109825320410925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8163853359406550213607283 12245780039109825320410925)
        ·
          refine ⟨4592167514666184495154097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12245780039109825320410925 4592167514666184495154097)
          ·
            refine ⟨3444125635999638371365573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4592167514666184495154097 3444125635999638371365573)
            ·
              refine ⟨645773556749932194631045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3444125635999638371365573 645773556749932194631045)
              ·
                refine ⟨121082541890612286493321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 645773556749932194631045 121082541890612286493321)
                ·
                  rfl

theorem cell20_795850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_795850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795850 prefixEnd_795850 := by exact prefixLift 795850
  have htrace : WordTrace (prefixWord ++ tailWord_795850) baseStart_795850 baseEnd_795850 := by
    simpa [prefixWord, tailWord_795850, baseEnd_795850] using wordTrace_append hprefix tailTrace_795850
  have hstable : (prefixWord ++ tailWord_795850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795850).length < 2 ^ (prefixWord ++ tailWord_795850).sum := by decide
  have hdescent : baseEnd_795850 < baseStart_795850 := by decide
  rcases family_descends (prefixWord ++ tailWord_795850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795877 : List Nat := [1, 3, 1, 4, 3, 1, 3, 2, 2]
def baseStart_795877 : Nat := 118140960795 + 795877 * 2 ^ 59
def prefixEnd_795877 : Nat := 4983230072969 + 3 ^ 40 * 795877 * 2
def baseEnd_795877 : Nat := 363259949207544765579853

theorem tailTrace_795877 : CollatzResearch.WordTrace tailWord_795877 prefixEnd_795877 363259949207544765579853 := by
  unfold tailWord_795877
  simp only [CollatzResearch.WordTrace]
  refine ⟨29028018937681028815169885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19352012625120685876779923 29028018937681028815169885)
  ·
    refine ⟨10885507101630385805688707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29028018937681028815169885 10885507101630385805688707)
    ·
      refine ⟨16328260652445578708533061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10885507101630385805688707 16328260652445578708533061)
      ·
        refine ⟨3061548872333546007849949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16328260652445578708533061 3061548872333546007849949)
        ·
          refine ⟨1148080827125079752943731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3061548872333546007849949 1148080827125079752943731)
          ·
            refine ⟨1722121240687619629415597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148080827125079752943731 1722121240687619629415597)
            ·
              refine ⟨645795465257857361030849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1722121240687619629415597 645795465257857361030849)
              ·
                refine ⟨484346598943393020773137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 645795465257857361030849 484346598943393020773137)
                ·
                  refine ⟨363259949207544765579853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484346598943393020773137 363259949207544765579853)
                  ·
                    rfl

theorem cell20_795877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 2].length) (baseStart_795877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795877 prefixEnd_795877 := by exact prefixLift 795877
  have htrace : WordTrace (prefixWord ++ tailWord_795877) baseStart_795877 baseEnd_795877 := by
    simpa [prefixWord, tailWord_795877, baseEnd_795877] using wordTrace_append hprefix tailTrace_795877
  have hstable : (prefixWord ++ tailWord_795877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795877).length < 2 ^ (prefixWord ++ tailWord_795877).sum := by decide
  have hdescent : baseEnd_795877 < baseStart_795877 := by decide
  rcases family_descends (prefixWord ++ tailWord_795877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795936 : List Nat := [2, 1, 1, 5, 3, 1, 1, 4, 2]
def baseStart_795936 : Nat := 118140960795 + 795936 * 2 ^ 59
def prefixEnd_795936 : Nat := 4983230072969 + 3 ^ 40 * 795936 * 2
def baseEnd_795936 : Nat := 363286878415202782612945

theorem tailTrace_795936 : CollatzResearch.WordTrace tailWord_795936 prefixEnd_795936 363286878415202782612945 := by
  unfold tailWord_795936
  simp only [CollatzResearch.WordTrace]
  refine ⟨14515085422233640945783831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19353447229644854594378441 14515085422233640945783831)
  ·
    refine ⟨21772628133350461418675747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14515085422233640945783831 21772628133350461418675747)
    ·
      refine ⟨32658942200025692128013621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21772628133350461418675747 32658942200025692128013621)
      ·
        refine ⟨3061775831252408637001277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32658942200025692128013621 3061775831252408637001277)
        ·
          refine ⟨1148165936719653238875479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3061775831252408637001277 1148165936719653238875479)
          ·
            refine ⟨1722248905079479858313219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148165936719653238875479 1722248905079479858313219)
            ·
              refine ⟨2583373357619219787469829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722248905079479858313219 2583373357619219787469829)
              ·
                refine ⟨484382504553603710150593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2583373357619219787469829 484382504553603710150593)
                ·
                  refine ⟨363286878415202782612945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484382504553603710150593 363286878415202782612945)
                  ·
                    rfl

theorem cell20_795936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 2].length) (baseStart_795936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795936 prefixEnd_795936 := by exact prefixLift 795936
  have htrace : WordTrace (prefixWord ++ tailWord_795936) baseStart_795936 baseEnd_795936 := by
    simpa [prefixWord, tailWord_795936, baseEnd_795936] using wordTrace_append hprefix tailTrace_795936
  have hstable : (prefixWord ++ tailWord_795936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795936).length < 2 ^ (prefixWord ++ tailWord_795936).sum := by decide
  have hdescent : baseEnd_795936 < baseStart_795936 := by decide
  rcases family_descends (prefixWord ++ tailWord_795936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795940 : List Nat := [2, 3, 1, 3, 1, 1, 2, 3, 4]
def baseStart_795940 : Nat := 118140960795 + 795940 * 2 ^ 59
def prefixEnd_795940 : Nat := 4983230072969 + 3 ^ 40 * 795940 * 2
def baseEnd_795940 : Nat := 363288704124196546479595

theorem tailTrace_795940 : CollatzResearch.WordTrace tailWord_795940 prefixEnd_795940 363288704124196546479595 := by
  unfold tailWord_795940
  simp only [CollatzResearch.WordTrace]
  refine ⟨14515158368226395287356637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19353544490968527049808849 14515158368226395287356637)
  ·
    refine ⟨5443184388084898232758739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14515158368226395287356637 5443184388084898232758739)
    ·
      refine ⟨8164776582127347349138109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5443184388084898232758739 8164776582127347349138109)
      ·
        refine ⟨3061791218297755255926791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8164776582127347349138109 3061791218297755255926791)
        ·
          refine ⟨4592686827446632883890187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3061791218297755255926791 4592686827446632883890187)
          ·
            refine ⟨6889030241169949325835281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4592686827446632883890187 6889030241169949325835281)
            ·
              refine ⟨5166772680877461994376461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6889030241169949325835281 5166772680877461994376461)
              ·
                refine ⟨1937539755329048247891173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5166772680877461994376461 1937539755329048247891173)
                ·
                  refine ⟨363288704124196546479595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1937539755329048247891173 363288704124196546479595)
                  ·
                    rfl

theorem cell20_795940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_795940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795940 prefixEnd_795940 := by exact prefixLift 795940
  have htrace : WordTrace (prefixWord ++ tailWord_795940) baseStart_795940 baseEnd_795940 := by
    simpa [prefixWord, tailWord_795940, baseEnd_795940] using wordTrace_append hprefix tailTrace_795940
  have hstable : (prefixWord ++ tailWord_795940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795940).length < 2 ^ (prefixWord ++ tailWord_795940).sum := by decide
  have hdescent : baseEnd_795940 < baseStart_795940 := by decide
  rcases family_descends (prefixWord ++ tailWord_795940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795964 : List Nat := [2, 2, 2, 2, 1, 4, 3, 4]
def baseStart_795964 : Nat := 118140960795 + 795964 * 2 ^ 59
def prefixEnd_795964 : Nat := 4983230072969 + 3 ^ 40 * 795964 * 2
def baseEnd_795964 : Nat := 121099886126053043226499

theorem tailTrace_795964 : CollatzResearch.WordTrace tailWord_795964 prefixEnd_795964 121099886126053043226499 := by
  unfold tailWord_795964
  simp only [CollatzResearch.WordTrace]
  refine ⟨14515596044182921336793473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19354128058910561782391297 14515596044182921336793473)
  ·
    refine ⟨10886697033137191002595105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14515596044182921336793473 10886697033137191002595105)
    ·
      refine ⟨8165022774852893251946329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10886697033137191002595105 8165022774852893251946329)
      ·
        refine ⟨6123767081139669938959747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8165022774852893251946329 6123767081139669938959747)
        ·
          refine ⟨9185650621709504908439621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6123767081139669938959747 9185650621709504908439621)
          ·
            refine ⟨1722309491570532170332429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9185650621709504908439621 1722309491570532170332429)
            ·
              refine ⟨645866059338949563874661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1722309491570532170332429 645866059338949563874661)
              ·
                refine ⟨121099886126053043226499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 645866059338949563874661 121099886126053043226499)
                ·
                  rfl

theorem cell20_795964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_795964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795964 prefixEnd_795964 := by exact prefixLift 795964
  have htrace : WordTrace (prefixWord ++ tailWord_795964) baseStart_795964 baseEnd_795964 := by
    simpa [prefixWord, tailWord_795964, baseEnd_795964] using wordTrace_append hprefix tailTrace_795964
  have hstable : (prefixWord ++ tailWord_795964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795964).length < 2 ^ (prefixWord ++ tailWord_795964).sum := by decide
  have hdescent : baseEnd_795964 < baseStart_795964 := by decide
  rcases family_descends (prefixWord ++ tailWord_795964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795981 : List Nat := [1, 6, 1, 3, 1, 1, 7]
def baseStart_795981 : Nat := 118140960795 + 795981 * 2 ^ 59
def prefixEnd_795981 : Nat := 4983230072969 + 3 ^ 40 * 795981 * 2
def baseEnd_795981 : Nat := 40367490849042514012529

theorem tailTrace_795981 : CollatzResearch.WordTrace tailWord_795981 prefixEnd_795981 40367490849042514012529 := by
  unfold tailWord_795981
  simp only [CollatzResearch.WordTrace]
  refine ⟨29031812129304254576955797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19354541419536169717970531 29031812129304254576955797)
  ·
    refine ⟨1360866193561136933294803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29031812129304254576955797 1360866193561136933294803)
    ·
      refine ⟨2041299290341705399942205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1360866193561136933294803 2041299290341705399942205)
      ·
        refine ⟨765487233878139524978327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2041299290341705399942205 765487233878139524978327)
        ·
          refine ⟨1148230850817209287467491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765487233878139524978327 1148230850817209287467491)
          ·
            refine ⟨1722346276225813931201237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148230850817209287467491 1722346276225813931201237)
            ·
              refine ⟨40367490849042514012529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1722346276225813931201237 40367490849042514012529)
              ·
                rfl

theorem cell20_795981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 7].length) (baseStart_795981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795981 prefixEnd_795981 := by exact prefixLift 795981
  have htrace : WordTrace (prefixWord ++ tailWord_795981) baseStart_795981 baseEnd_795981 := by
    simpa [prefixWord, tailWord_795981, baseEnd_795981] using wordTrace_append hprefix tailTrace_795981
  have hstable : (prefixWord ++ tailWord_795981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795981).length < 2 ^ (prefixWord ++ tailWord_795981).sum := by decide
  have hdescent : baseEnd_795981 < baseStart_795981 := by decide
  rcases family_descends (prefixWord ++ tailWord_795981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795992 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 5]
def baseStart_795992 : Nat := 118140960795 + 795992 * 2 ^ 59
def prefixEnd_795992 : Nat := 4983230072969 + 3 ^ 40 * 795992 * 2
def baseEnd_795992 : Nat := 363312438341115476746049

theorem tailTrace_795992 : CollatzResearch.WordTrace tailWord_795992 prefixEnd_795992 363312438341115476746049 := by
  unfold tailWord_795992
  simp only [CollatzResearch.WordTrace]
  refine ⟨14516106666132201727803115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19354808888176268970404153 14516106666132201727803115)
  ·
    refine ⟨21774159999198302591704673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14516106666132201727803115 21774159999198302591704673)
    ·
      refine ⟨16330619999398726943778505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21774159999198302591704673 16330619999398726943778505)
      ·
        refine ⟨12247964999549045207833879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16330619999398726943778505 12247964999549045207833879)
        ·
          refine ⟨18371947499323567811750819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12247964999549045207833879 18371947499323567811750819)
          ·
            refine ⟨27557921248985351717626229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18371947499323567811750819 27557921248985351717626229)
            ·
              refine ⟨2583555117092376723527459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27557921248985351717626229 2583555117092376723527459)
              ·
                refine ⟨3875332675638565085291189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2583555117092376723527459 3875332675638565085291189)
                ·
                  refine ⟨363312438341115476746049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3875332675638565085291189 363312438341115476746049)
                  ·
                    rfl

theorem cell20_795992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_795992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_795992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_795992 prefixEnd_795992 := by exact prefixLift 795992
  have htrace : WordTrace (prefixWord ++ tailWord_795992) baseStart_795992 baseEnd_795992 := by
    simpa [prefixWord, tailWord_795992, baseEnd_795992] using wordTrace_append hprefix tailTrace_795992
  have hstable : (prefixWord ++ tailWord_795992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795992).length < 2 ^ (prefixWord ++ tailWord_795992).sum := by decide
  have hdescent : baseEnd_795992 < baseStart_795992 := by decide
  rcases family_descends (prefixWord ++ tailWord_795992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796037 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 6]
def baseStart_796037 : Nat := 118140960795 + 796037 * 2 ^ 59
def prefixEnd_796037 : Nat := 4983230072969 + 3 ^ 40 * 796037 * 2
def baseEnd_796037 : Nat := 363332977567295320245865

theorem tailTrace_796037 : CollatzResearch.WordTrace tailWord_796037 prefixEnd_796037 363332977567295320245865 := by
  unfold tailWord_796037
  simp only [CollatzResearch.WordTrace]
  refine ⟨29033854617101376140994365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19355903078067584093996243 29033854617101376140994365)
  ·
    refine ⟨10887695481413016052872887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29033854617101376140994365 10887695481413016052872887)
    ·
      refine ⟨16331543222119524079309331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10887695481413016052872887 16331543222119524079309331)
      ·
        refine ⟨24497314833179286118963997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16331543222119524079309331 24497314833179286118963997)
        ·
          refine ⟨9186493062442232294611499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24497314833179286118963997 9186493062442232294611499)
          ·
            refine ⟨13779739593663348441917249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9186493062442232294611499 13779739593663348441917249)
            ·
              refine ⟨10334804695247511331437937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13779739593663348441917249 10334804695247511331437937)
              ·
                refine ⟨7751103521435633498578453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10334804695247511331437937 7751103521435633498578453)
                ·
                  refine ⟨363332977567295320245865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7751103521435633498578453 363332977567295320245865)
                  ·
                    rfl

theorem cell20_796037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_796037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796037 prefixEnd_796037 := by exact prefixLift 796037
  have htrace : WordTrace (prefixWord ++ tailWord_796037) baseStart_796037 baseEnd_796037 := by
    simpa [prefixWord, tailWord_796037, baseEnd_796037] using wordTrace_append hprefix tailTrace_796037
  have hstable : (prefixWord ++ tailWord_796037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796037).length < 2 ^ (prefixWord ++ tailWord_796037).sum := by decide
  have hdescent : baseEnd_796037 < baseStart_796037 := by decide
  rcases family_descends (prefixWord ++ tailWord_796037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796060 : List Nat := [2, 2, 3, 4, 1, 2, 2, 1, 3]
def baseStart_796060 : Nat := 118140960795 + 796060 * 2 ^ 59
def prefixEnd_796060 : Nat := 4983230072969 + 3 ^ 40 * 796060 * 2
def baseEnd_796060 : Nat := 363343475394009462479105

theorem tailTrace_796060 : CollatzResearch.WordTrace tailWord_796060 prefixEnd_796060 363343475394009462479105 := by
  unfold tailWord_796060
  simp only [CollatzResearch.WordTrace]
  refine ⟨14517346748009025534540817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19356462330678700712721089 14517346748009025534540817)
  ·
    refine ⟨10888010061006769150905613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14517346748009025534540817 10888010061006769150905613)
    ·
      refine ⟨4083003772877538431589605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10888010061006769150905613 4083003772877538431589605)
      ·
        refine ⟨765563207414538455923051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4083003772877538431589605 765563207414538455923051)
        ·
          refine ⟨1148344811121807683884577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765563207414538455923051 1148344811121807683884577)
          ·
            refine ⟨861258608341355762913433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1148344811121807683884577 861258608341355762913433)
            ·
              refine ⟨645943956256016822185075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 861258608341355762913433 645943956256016822185075)
              ·
                refine ⟨968915934384025233277613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645943956256016822185075 968915934384025233277613)
                ·
                  refine ⟨363343475394009462479105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 968915934384025233277613 363343475394009462479105)
                  ·
                    rfl

theorem cell20_796060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_796060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796060 prefixEnd_796060 := by exact prefixLift 796060
  have htrace : WordTrace (prefixWord ++ tailWord_796060) baseStart_796060 baseEnd_796060 := by
    simpa [prefixWord, tailWord_796060, baseEnd_796060] using wordTrace_append hprefix tailTrace_796060
  have hstable : (prefixWord ++ tailWord_796060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796060).length < 2 ^ (prefixWord ++ tailWord_796060).sum := by decide
  have hdescent : baseEnd_796060 < baseStart_796060 := by decide
  rcases family_descends (prefixWord ++ tailWord_796060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796061 : List Nat := [1, 4, 2, 1, 3, 1, 1, 7]
def baseStart_796061 : Nat := 118140960795 + 796061 * 2 ^ 59
def prefixEnd_796061 : Nat := 4983230072969 + 3 ^ 40 * 796061 * 2
def baseEnd_796061 : Nat := 121114643940419301148589

theorem tailTrace_796061 : CollatzResearch.WordTrace tailWord_796061 prefixEnd_796061 121114643940419301148589 := by
  unfold tailWord_796061
  simp only [CollatzResearch.WordTrace]
  refine ⟨29034729969014428239868037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19356486646009618826578691 29034729969014428239868037)
  ·
    refine ⟨5444011869190205294975257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29034729969014428239868037 5444011869190205294975257)
    ·
      refine ⟨4083008901892653971231443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5444011869190205294975257 4083008901892653971231443)
      ·
        refine ⟨6124513352838980956847165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4083008901892653971231443 6124513352838980956847165)
        ·
          refine ⟨2296692507314617858817687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6124513352838980956847165 2296692507314617858817687)
          ·
            refine ⟨3445038760971926788226531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2296692507314617858817687 3445038760971926788226531)
            ·
              refine ⟨5167558141457890182339797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3445038760971926788226531 5167558141457890182339797)
              ·
                refine ⟨121114643940419301148589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5167558141457890182339797 121114643940419301148589)
                ·
                  rfl

theorem cell20_796061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 7].length) (baseStart_796061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796061 prefixEnd_796061 := by exact prefixLift 796061
  have htrace : WordTrace (prefixWord ++ tailWord_796061) baseStart_796061 baseEnd_796061 := by
    simpa [prefixWord, tailWord_796061, baseEnd_796061] using wordTrace_append hprefix tailTrace_796061
  have hstable : (prefixWord ++ tailWord_796061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796061).length < 2 ^ (prefixWord ++ tailWord_796061).sum := by decide
  have hdescent : baseEnd_796061 < baseStart_796061 := by decide
  rcases family_descends (prefixWord ++ tailWord_796061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796161 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 5]
def baseStart_796161 : Nat := 118140960795 + 796161 * 2 ^ 59
def prefixEnd_796161 : Nat := 4983230072969 + 3 ^ 40 * 796161 * 2
def baseEnd_796161 : Nat := 363389574546102000112025

theorem tailTrace_796161 : CollatzResearch.WordTrace tailWord_796161 prefixEnd_796161 363389574546102000112025 := by
  unfold tailWord_796161
  simp only [CollatzResearch.WordTrace]
  refine ⟨29038377268652145318508337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19358918179101430212338891 29038377268652145318508337)
  ·
    refine ⟨21778782951489108988881253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29038377268652145318508337 21778782951489108988881253)
    ·
      refine ⟨4083521803404207935415235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21778782951489108988881253 4083521803404207935415235)
      ·
        refine ⟨6125282705106311903122853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4083521803404207935415235 6125282705106311903122853)
        ·
          refine ⟨1148490507207433481835535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6125282705106311903122853 1148490507207433481835535)
          ·
            refine ⟨1722735760811150222753303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148490507207433481835535 1722735760811150222753303)
            ·
              refine ⟨2584103641216725334129955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722735760811150222753303 2584103641216725334129955)
              ·
                refine ⟨3876155461825088001194933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2584103641216725334129955 3876155461825088001194933)
                ·
                  refine ⟨363389574546102000112025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3876155461825088001194933 363389574546102000112025)
                  ·
                    rfl

theorem cell20_796161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_796161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796161 prefixEnd_796161 := by exact prefixLift 796161
  have htrace : WordTrace (prefixWord ++ tailWord_796161) baseStart_796161 baseEnd_796161 := by
    simpa [prefixWord, tailWord_796161, baseEnd_796161] using wordTrace_append hprefix tailTrace_796161
  have hstable : (prefixWord ++ tailWord_796161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796161).length < 2 ^ (prefixWord ++ tailWord_796161).sum := by decide
  have hdescent : baseEnd_796161 < baseStart_796161 := by decide
  rcases family_descends (prefixWord ++ tailWord_796161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796192 : List Nat := [2, 1, 1, 6, 1, 1, 4, 4]
def baseStart_796192 : Nat := 118140960795 + 796192 * 2 ^ 59
def prefixEnd_796192 : Nat := 4983230072969 + 3 ^ 40 * 796192 * 2
def baseEnd_796192 : Nat := 121134574596934556692855

theorem tailTrace_796192 : CollatzResearch.WordTrace tailWord_796192 prefixEnd_796192 121134574596934556692855 := by
  unfold tailWord_796192
  simp only [CollatzResearch.WordTrace]
  refine ⟨14519753965769918806443415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19359671954359891741924553 14519753965769918806443415)
  ·
    refine ⟨21779630948654878209665123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14519753965769918806443415 21779630948654878209665123)
    ·
      refine ⟨32669446422982317314497685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21779630948654878209665123 32669446422982317314497685)
      ·
        refine ⟨1531380301077296124117079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32669446422982317314497685 1531380301077296124117079)
        ·
          refine ⟨2297070451615944186175619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1531380301077296124117079 2297070451615944186175619)
          ·
            refine ⟨3445605677423916279263429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2297070451615944186175619 3445605677423916279263429)
            ·
              refine ⟨646051064516984302361893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3445605677423916279263429 646051064516984302361893)
              ·
                refine ⟨121134574596934556692855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 646051064516984302361893 121134574596934556692855)
                ·
                  rfl

theorem cell20_796192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_796192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796192 prefixEnd_796192 := by exact prefixLift 796192
  have htrace : WordTrace (prefixWord ++ tailWord_796192) baseStart_796192 baseEnd_796192 := by
    simpa [prefixWord, tailWord_796192, baseEnd_796192] using wordTrace_append hprefix tailTrace_796192
  have hstable : (prefixWord ++ tailWord_796192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796192).length < 2 ^ (prefixWord ++ tailWord_796192).sum := by decide
  have hdescent : baseEnd_796192 < baseStart_796192 := by decide
  rcases family_descends (prefixWord ++ tailWord_796192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796213 : List Nat := [1, 3, 3, 1, 1, 5, 6]
def baseStart_796213 : Nat := 118140960795 + 796213 * 2 ^ 59
def prefixEnd_796213 : Nat := 4983230072969 + 3 ^ 40 * 796213 * 2
def baseEnd_796213 : Nat := 40379256529224547819831

theorem tailTrace_796213 : CollatzResearch.WordTrace tailWord_796213 prefixEnd_796213 40379256529224547819831 := by
  unfold tailWord_796213
  simp only [CollatzResearch.WordTrace]
  refine ⟨29040273864463758199401293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19360182576309172132934195 29040273864463758199401293)
  ·
    refine ⟨10890102699173909324775485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29040273864463758199401293 10890102699173909324775485)
    ·
      refine ⟨4083788512190215996790807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10890102699173909324775485 4083788512190215996790807)
      ·
        refine ⟨6125682768285323995186211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4083788512190215996790807 6125682768285323995186211)
        ·
          refine ⟨9188524152427985992779317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6125682768285323995186211 9188524152427985992779317)
          ·
            refine ⟨861424139290123686823061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9188524152427985992779317 861424139290123686823061)
            ·
              refine ⟨40379256529224547819831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 861424139290123686823061 40379256529224547819831)
              ·
                rfl

theorem cell20_796213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 6].length) (baseStart_796213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796213 prefixEnd_796213 := by exact prefixLift 796213
  have htrace : WordTrace (prefixWord ++ tailWord_796213) baseStart_796213 baseEnd_796213 := by
    simpa [prefixWord, tailWord_796213, baseEnd_796213] using wordTrace_append hprefix tailTrace_796213
  have hstable : (prefixWord ++ tailWord_796213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796213).length < 2 ^ (prefixWord ++ tailWord_796213).sum := by decide
  have hdescent : baseEnd_796213 < baseStart_796213 := by decide
  rcases family_descends (prefixWord ++ tailWord_796213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796272 : List Nat := [2, 1, 1, 1, 6, 9]
def baseStart_796272 : Nat := 118140960795 + 796272 * 2 ^ 59
def prefixEnd_796272 : Nat := 4983230072969 + 3 ^ 40 * 796272 * 2
def baseEnd_796272 : Nat := 13460749554469590644873

theorem tailTrace_796272 : CollatzResearch.WordTrace tailWord_796272 prefixEnd_796272 13460749554469590644873 := by
  unfold tailWord_796272
  simp only [CollatzResearch.WordTrace]
  refine ⟨14521212885625005637899535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19361617180833340850532713 14521212885625005637899535)
  ·
    refine ⟨21781819328437508456849303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14521212885625005637899535 21781819328437508456849303)
    ·
      refine ⟨32672728992656262685273955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21781819328437508456849303 32672728992656262685273955)
      ·
        refine ⟨49009093488984394027910933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32672728992656262685273955 49009093488984394027910933)
        ·
          refine ⟨2297301257296143470058325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49009093488984394027910933 2297301257296143470058325)
          ·
            refine ⟨13460749554469590644873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2297301257296143470058325 13460749554469590644873)
            ·
              rfl

theorem cell20_796272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 9].length) (baseStart_796272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796272 prefixEnd_796272 := by exact prefixLift 796272
  have htrace : WordTrace (prefixWord ++ tailWord_796272) baseStart_796272 baseEnd_796272 := by
    simpa [prefixWord, tailWord_796272, baseEnd_796272] using wordTrace_append hprefix tailTrace_796272
  have hstable : (prefixWord ++ tailWord_796272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796272).length < 2 ^ (prefixWord ++ tailWord_796272).sum := by decide
  have hdescent : baseEnd_796272 < baseStart_796272 := by decide
  rcases family_descends (prefixWord ++ tailWord_796272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796278 : List Nat := [5, 1, 1, 2, 2, 2, 1, 4, 2]
def baseStart_796278 : Nat := 118140960795 + 796278 * 2 ^ 59
def prefixEnd_796278 : Nat := 4983230072969 + 3 ^ 40 * 796278 * 2
def baseEnd_796278 : Nat := 363442976534169593211547

theorem tailTrace_796278 : CollatzResearch.WordTrace tailWord_796278 prefixEnd_796278 363442976534169593211547 := by
  unfold tailWord_796278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1815165288076767143782343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19361763072818849533678325 1815165288076767143782343)
  ·
    refine ⟨2722747932115150715673515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1815165288076767143782343 2722747932115150715673515)
    ·
      refine ⟨4084121898172726073510273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2722747932115150715673515 4084121898172726073510273)
      ·
        refine ⟨3063091423629544555132705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4084121898172726073510273 3063091423629544555132705)
        ·
          refine ⟨2297318567722158416349529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3063091423629544555132705 2297318567722158416349529)
          ·
            refine ⟨1722988925791618812262147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2297318567722158416349529 1722988925791618812262147)
            ·
              refine ⟨2584483388687428218393221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722988925791618812262147 2584483388687428218393221)
              ·
                refine ⟨484590635378892790948729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2584483388687428218393221 484590635378892790948729)
                ·
                  refine ⟨363442976534169593211547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484590635378892790948729 363442976534169593211547)
                  ·
                    rfl

theorem cell20_796278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_796278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796278 prefixEnd_796278 := by exact prefixLift 796278
  have htrace : WordTrace (prefixWord ++ tailWord_796278) baseStart_796278 baseEnd_796278 := by
    simpa [prefixWord, tailWord_796278, baseEnd_796278] using wordTrace_append hprefix tailTrace_796278
  have hstable : (prefixWord ++ tailWord_796278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796278).length < 2 ^ (prefixWord ++ tailWord_796278).sum := by decide
  have hdescent : baseEnd_796278 < baseStart_796278 := by decide
  rcases family_descends (prefixWord ++ tailWord_796278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796289 : List Nat := [1, 2, 4, 2, 1, 2, 3, 5]
def baseStart_796289 : Nat := 118140960795 + 796289 * 2 ^ 59
def prefixEnd_796289 : Nat := 4983230072969 + 3 ^ 40 * 796289 * 2
def baseEnd_796289 : Nat := 121149332411300814614945

theorem tailTrace_796289 : CollatzResearch.WordTrace tailWord_796289 prefixEnd_796289 121149332411300814614945 := by
  unfold tailWord_796289
  simp only [CollatzResearch.WordTrace]
  refine ⟨29043045812188423179167921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19362030541458948786111947 29043045812188423179167921)
  ·
    refine ⟨21782284359141317384375941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29043045812188423179167921 21782284359141317384375941)
    ·
      refine ⟨4084178317338997009570489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21782284359141317384375941 4084178317338997009570489)
      ·
        refine ⟨3063133738004247757177867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4084178317338997009570489 3063133738004247757177867)
        ·
          refine ⟨4594700607006371635766801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3063133738004247757177867 4594700607006371635766801)
          ·
            refine ⟨3446025455254778726825101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4594700607006371635766801 3446025455254778726825101)
            ·
              refine ⟨1292259545720542022559413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3446025455254778726825101 1292259545720542022559413)
              ·
                refine ⟨121149332411300814614945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1292259545720542022559413 121149332411300814614945)
                ·
                  rfl

theorem cell20_796289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 5].length) (baseStart_796289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796289 prefixEnd_796289 := by exact prefixLift 796289
  have htrace : WordTrace (prefixWord ++ tailWord_796289) baseStart_796289 baseEnd_796289 := by
    simpa [prefixWord, tailWord_796289, baseEnd_796289] using wordTrace_append hprefix tailTrace_796289
  have hstable : (prefixWord ++ tailWord_796289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796289).length < 2 ^ (prefixWord ++ tailWord_796289).sum := by decide
  have hdescent : baseEnd_796289 < baseStart_796289 := by decide
  rcases family_descends (prefixWord ++ tailWord_796289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796316 : List Nat := [2, 2, 3, 2, 3, 1, 2, 3, 2]
def baseStart_796316 : Nat := 118140960795 + 796316 * 2 ^ 59
def prefixEnd_796316 : Nat := 4983230072969 + 3 ^ 40 * 796316 * 2
def baseEnd_796316 : Nat := 363460320769610349944725

theorem tailTrace_796316 : CollatzResearch.WordTrace tailWord_796316 prefixEnd_796316 363460320769610349944725 := by
  unfold tailWord_796316
  simp only [CollatzResearch.WordTrace]
  refine ⟨14522015291545303395200401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19362687055393737860267201 14522015291545303395200401)
  ·
    refine ⟨10891511468658977546400301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14522015291545303395200401 10891511468658977546400301)
    ·
      refine ⟨4084316800747116579900113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10891511468658977546400301 4084316800747116579900113)
      ·
        refine ⟨3063237600560337434925085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4084316800747116579900113 3063237600560337434925085)
        ·
          refine ⟨1148714100210126538096907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3063237600560337434925085 1148714100210126538096907)
          ·
            refine ⟨1723071150315189807145361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148714100210126538096907 1723071150315189807145361)
            ·
              refine ⟨1292303362736392355359021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1723071150315189807145361 1292303362736392355359021)
              ·
                refine ⟨484613761026147133259633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1292303362736392355359021 484613761026147133259633)
                ·
                  refine ⟨363460320769610349944725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484613761026147133259633 363460320769610349944725)
                  ·
                    rfl

theorem cell20_796316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_796316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796316 prefixEnd_796316 := by exact prefixLift 796316
  have htrace : WordTrace (prefixWord ++ tailWord_796316) baseStart_796316 baseEnd_796316 := by
    simpa [prefixWord, tailWord_796316, baseEnd_796316] using wordTrace_append hprefix tailTrace_796316
  have hstable : (prefixWord ++ tailWord_796316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796316).length < 2 ^ (prefixWord ++ tailWord_796316).sum := by decide
  have hdescent : baseEnd_796316 < baseStart_796316 := by decide
  rcases family_descends (prefixWord ++ tailWord_796316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796351 : List Nat := [1, 1, 2, 2, 2, 3, 5, 1, 3]
def baseStart_796351 : Nat := 118140960795 + 796351 * 2 ^ 59
def prefixEnd_796351 : Nat := 4983230072969 + 3 ^ 40 * 796351 * 2
def baseEnd_796351 : Nat := 363476295723305783777915

theorem tailTrace_796351 : CollatzResearch.WordTrace tailWord_796351 prefixEnd_796351 363476295723305783777915 := by
  unfold tailWord_796351
  simp only [CollatzResearch.WordTrace]
  refine ⟨29045307137963807767924907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19363538091975871845283271 29045307137963807767924907)
  ·
    refine ⟨43567960706945711651887361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29045307137963807767924907 43567960706945711651887361)
    ·
      refine ⟨32675970530209283738915521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43567960706945711651887361 32675970530209283738915521)
      ·
        refine ⟨24506977897656962804186641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32675970530209283738915521 24506977897656962804186641)
        ·
          refine ⟨18380233423242722103139981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24506977897656962804186641 18380233423242722103139981)
          ·
            refine ⟨6892587533716020788677493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18380233423242722103139981 6892587533716020788677493)
            ·
              refine ⟨646180081285876948938515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6892587533716020788677493 646180081285876948938515)
              ·
                refine ⟨969270121928815423407773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646180081285876948938515 969270121928815423407773)
                ·
                  refine ⟨363476295723305783777915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 969270121928815423407773 363476295723305783777915)
                  ·
                    rfl

theorem cell20_796351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 3].length) (baseStart_796351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796351 prefixEnd_796351 := by exact prefixLift 796351
  have htrace : WordTrace (prefixWord ++ tailWord_796351) baseStart_796351 baseEnd_796351 := by
    simpa [prefixWord, tailWord_796351, baseEnd_796351] using wordTrace_append hprefix tailTrace_796351
  have hstable : (prefixWord ++ tailWord_796351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796351).length < 2 ^ (prefixWord ++ tailWord_796351).sum := by decide
  have hdescent : baseEnd_796351 < baseStart_796351 := by decide
  rcases family_descends (prefixWord ++ tailWord_796351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796392 : List Nat := [2, 1, 4, 1, 3, 2, 3, 2, 2]
def baseStart_796392 : Nat := 118140960795 + 796392 * 2 ^ 59
def prefixEnd_796392 : Nat := 4983230072969 + 3 ^ 40 * 796392 * 2
def baseEnd_796392 : Nat := 363495009240491863411081

theorem tailTrace_796392 : CollatzResearch.WordTrace tailWord_796392 prefixEnd_796392 363495009240491863411081 := by
  unfold tailWord_796392
  simp only [CollatzResearch.WordTrace]
  refine ⟨14523401265407635885083715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19364535020543514513444953 14523401265407635885083715)
  ·
    refine ⟨21785101898111453827625573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14523401265407635885083715 21785101898111453827625573)
    ·
      refine ⟨4084706605895897592679795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21785101898111453827625573 4084706605895897592679795)
      ·
        refine ⟨6127059908843846389019693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4084706605895897592679795 6127059908843846389019693)
        ·
          refine ⟨2297647465816442395882385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6127059908843846389019693 2297647465816442395882385)
          ·
            refine ⟨1723235599362331796911789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2297647465816442395882385 1723235599362331796911789)
            ·
              refine ⟨646213349760874423841921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1723235599362331796911789 646213349760874423841921)
              ·
                refine ⟨484660012320655817881441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 646213349760874423841921 484660012320655817881441)
                ·
                  refine ⟨363495009240491863411081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484660012320655817881441 363495009240491863411081)
                  ·
                    rfl

theorem cell20_796392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 2, 2].length) (baseStart_796392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796392 prefixEnd_796392 := by exact prefixLift 796392
  have htrace : WordTrace (prefixWord ++ tailWord_796392) baseStart_796392 baseEnd_796392 := by
    simpa [prefixWord, tailWord_796392, baseEnd_796392] using wordTrace_append hprefix tailTrace_796392
  have hstable : (prefixWord ++ tailWord_796392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796392).length < 2 ^ (prefixWord ++ tailWord_796392).sum := by decide
  have hdescent : baseEnd_796392 < baseStart_796392 := by decide
  rcases family_descends (prefixWord ++ tailWord_796392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796396 : List Nat := [2, 2, 1, 1, 2, 2, 2, 6, 2]
def baseStart_796396 : Nat := 118140960795 + 796396 * 2 ^ 59
def prefixEnd_796396 : Nat := 4983230072969 + 3 ^ 40 * 796396 * 2
def baseEnd_796396 : Nat := 363496834949485627277731

theorem tailTrace_796396 : CollatzResearch.WordTrace tailWord_796396 prefixEnd_796396 363496834949485627277731 := by
  unfold tailWord_796396
  simp only [CollatzResearch.WordTrace]
  refine ⟨14523474211400390226656521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19364632281867186968875361 14523474211400390226656521)
  ·
    refine ⟨10892605658550292669992391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14523474211400390226656521 10892605658550292669992391)
    ·
      refine ⟨16338908487825439004988587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10892605658550292669992391 16338908487825439004988587)
      ·
        refine ⟨24508362731738158507482881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16338908487825439004988587 24508362731738158507482881)
        ·
          refine ⟨18381272048803618880612161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24508362731738158507482881 18381272048803618880612161)
          ·
            refine ⟨13785954036602714160459121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18381272048803618880612161 13785954036602714160459121)
            ·
              refine ⟨10339465527452035620344341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13785954036602714160459121 10339465527452035620344341)
              ·
                refine ⟨484662446599314169703641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10339465527452035620344341 484662446599314169703641)
                ·
                  refine ⟨363496834949485627277731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 484662446599314169703641 363496834949485627277731)
                  ·
                    rfl

theorem cell20_796396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_796396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796396 prefixEnd_796396 := by exact prefixLift 796396
  have htrace : WordTrace (prefixWord ++ tailWord_796396) baseStart_796396 baseEnd_796396 := by
    simpa [prefixWord, tailWord_796396, baseEnd_796396] using wordTrace_append hprefix tailTrace_796396
  have hstable : (prefixWord ++ tailWord_796396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796396).length < 2 ^ (prefixWord ++ tailWord_796396).sum := by decide
  have hdescent : baseEnd_796396 < baseStart_796396 := by decide
  rcases family_descends (prefixWord ++ tailWord_796396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796406 : List Nat := [5, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_796406 : Nat := 118140960795 + 796406 * 2 ^ 59
def prefixEnd_796406 : Nat := 4983230072969 + 3 ^ 40 * 796406 * 2
def baseEnd_796406 : Nat := 363501399221970036944357

theorem tailTrace_796406 : CollatzResearch.WordTrace tailWord_796406 prefixEnd_796406 363501399221970036944357 := by
  unfold tailWord_796406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1815457072047784510073567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19364875435176368107451381 1815457072047784510073567)
  ·
    refine ⟨2723185608071676765110351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1815457072047784510073567 2723185608071676765110351)
    ·
      refine ⟨4084778412107515147665527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2723185608071676765110351 4084778412107515147665527)
      ·
        refine ⟨6127167618161272721498291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4084778412107515147665527 6127167618161272721498291)
        ·
          refine ⟨9190751427241909082247437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6127167618161272721498291 9190751427241909082247437)
          ·
            refine ⟨3446531785215715905842789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9190751427241909082247437 3446531785215715905842789)
            ·
              refine ⟨646224709727946732345523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3446531785215715905842789 646224709727946732345523)
              ·
                refine ⟨969337064591920098518285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646224709727946732345523 969337064591920098518285)
                ·
                  refine ⟨363501399221970036944357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 969337064591920098518285 363501399221970036944357)
                  ·
                    rfl

theorem cell20_796406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_796406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796406 prefixEnd_796406 := by exact prefixLift 796406
  have htrace : WordTrace (prefixWord ++ tailWord_796406) baseStart_796406 baseEnd_796406 := by
    simpa [prefixWord, tailWord_796406, baseEnd_796406] using wordTrace_append hprefix tailTrace_796406
  have hstable : (prefixWord ++ tailWord_796406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796406).length < 2 ^ (prefixWord ++ tailWord_796406).sum := by decide
  have hdescent : baseEnd_796406 < baseStart_796406 := by decide
  rcases family_descends (prefixWord ++ tailWord_796406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796417 : List Nat := [1, 2, 4, 1, 1, 1, 2, 4, 4]
def baseStart_796417 : Nat := 118140960795 + 796417 * 2 ^ 59
def prefixEnd_796417 : Nat := 4983230072969 + 3 ^ 40 * 796417 * 2
def baseEnd_796417 : Nat := 363506419921702887577645

theorem tailTrace_796417 : CollatzResearch.WordTrace tailWord_796417 prefixEnd_796417 363506419921702887577645 := by
  unfold tailWord_796417
  simp only [CollatzResearch.WordTrace]
  refine ⟨29047714355724701039827505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19365142903816467359885003 29047714355724701039827505)
  ·
    refine ⟨21785785766793525779870629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29047714355724701039827505 21785785766793525779870629)
    ·
      refine ⟨4084834831273786083725743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21785785766793525779870629 4084834831273786083725743)
      ·
        refine ⟨6127252246910679125588615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4084834831273786083725743 6127252246910679125588615)
        ·
          refine ⟨9190878370366018688382923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6127252246910679125588615 9190878370366018688382923)
          ·
            refine ⟨13786317555549028032574385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9190878370366018688382923 13786317555549028032574385)
            ·
              refine ⟨10339738166661771024430789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13786317555549028032574385 10339738166661771024430789)
              ·
                refine ⟨1938700906249082067080773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10339738166661771024430789 1938700906249082067080773)
                ·
                  refine ⟨363506419921702887577645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1938700906249082067080773 363506419921702887577645)
                  ·
                    rfl

theorem cell20_796417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 4].length) (baseStart_796417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796417 prefixEnd_796417 := by exact prefixLift 796417
  have htrace : WordTrace (prefixWord ++ tailWord_796417) baseStart_796417 baseEnd_796417 := by
    simpa [prefixWord, tailWord_796417, baseEnd_796417] using wordTrace_append hprefix tailTrace_796417
  have hstable : (prefixWord ++ tailWord_796417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796417).length < 2 ^ (prefixWord ++ tailWord_796417).sum := by decide
  have hdescent : baseEnd_796417 < baseStart_796417 := by decide
  rcases family_descends (prefixWord ++ tailWord_796417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796424 : List Nat := [2, 1, 3, 2, 2, 1, 1, 8]
def baseStart_796424 : Nat := 118140960795 + 796424 * 2 ^ 59
def prefixEnd_796424 : Nat := 4983230072969 + 3 ^ 40 * 796424 * 2
def baseEnd_796424 : Nat := 121169871637480658114761

theorem tailTrace_796424 : CollatzResearch.WordTrace tailWord_796424 prefixEnd_796424 121169871637480658114761 := by
  unfold tailWord_796424
  simp only [CollatzResearch.WordTrace]
  refine ⟨14523984833349670617666163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19365313111132894156888217 14523984833349670617666163)
  ·
    refine ⟨21785977250024505926499245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14523984833349670617666163 21785977250024505926499245)
    ·
      refine ⟨8169741468759189722437217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21785977250024505926499245 8169741468759189722437217)
      ·
        refine ⟨6127306101569392291827913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8169741468759189722437217 6127306101569392291827913)
        ·
          refine ⟨4595479576177044218870935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6127306101569392291827913 4595479576177044218870935)
          ·
            refine ⟨6893219364265566328306403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4595479576177044218870935 6893219364265566328306403)
            ·
              refine ⟨10339829046398349492459605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6893219364265566328306403 10339829046398349492459605)
              ·
                refine ⟨121169871637480658114761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10339829046398349492459605 121169871637480658114761)
                ·
                  rfl

theorem cell20_796424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_796424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796424 prefixEnd_796424 := by exact prefixLift 796424
  have htrace : WordTrace (prefixWord ++ tailWord_796424) baseStart_796424 baseEnd_796424 := by
    simpa [prefixWord, tailWord_796424, baseEnd_796424] using wordTrace_append hprefix tailTrace_796424
  have hstable : (prefixWord ++ tailWord_796424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796424).length < 2 ^ (prefixWord ++ tailWord_796424).sum := by decide
  have hdescent : baseEnd_796424 < baseStart_796424 := by decide
  rcases family_descends (prefixWord ++ tailWord_796424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796431 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 5]
def baseStart_796431 : Nat := 118140960795 + 796431 * 2 ^ 59
def prefixEnd_796431 : Nat := 4983230072969 + 3 ^ 40 * 796431 * 2
def baseEnd_796431 : Nat := 363512809903181061110921

theorem tailTrace_796431 : CollatzResearch.WordTrace tailWord_796431 prefixEnd_796431 363512809903181061110921 := by
  unfold tailWord_796431
  simp only [CollatzResearch.WordTrace]
  refine ⟨29048224977673981430837147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19365483318449320953891431 29048224977673981430837147)
  ·
    refine ⟨43572337466510972146255721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29048224977673981430837147 43572337466510972146255721)
    ·
      refine ⟨32679253099883229109691791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43572337466510972146255721 32679253099883229109691791)
      ·
        refine ⟨49018879649824843664537687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32679253099883229109691791 49018879649824843664537687)
        ·
          refine ⟨73528319474737265496806531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49018879649824843664537687 73528319474737265496806531)
          ·
            refine ⟨110292479212105898245209797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73528319474737265496806531 110292479212105898245209797)
            ·
              refine ⟨20679839852269855920976837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110292479212105898245209797 20679839852269855920976837)
              ·
                refine ⟨3877469972300597985183157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20679839852269855920976837 3877469972300597985183157)
                ·
                  refine ⟨363512809903181061110921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3877469972300597985183157 363512809903181061110921)
                  ·
                    rfl

theorem cell20_796431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_796431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_796431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_796431 prefixEnd_796431 := by exact prefixLift 796431
  have htrace : WordTrace (prefixWord ++ tailWord_796431) baseStart_796431 baseEnd_796431 := by
    simpa [prefixWord, tailWord_796431, baseEnd_796431] using wordTrace_append hprefix tailTrace_796431
  have hstable : (prefixWord ++ tailWord_796431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796431).length < 2 ^ (prefixWord ++ tailWord_796431).sum := by decide
  have hdescent : baseEnd_796431 < baseStart_796431 := by decide
  rcases family_descends (prefixWord ++ tailWord_796431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
