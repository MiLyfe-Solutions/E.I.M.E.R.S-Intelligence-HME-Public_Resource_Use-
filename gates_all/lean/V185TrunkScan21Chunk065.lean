import V185TrunkScan21Chunk064

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_784807 : List Nat := [1, 1, 6, 1, 1, 2, 2, 3, 4]
def baseStart_784807 : Nat := 118140960795 + 784807 * 2 ^ 59
def prefixEnd_784807 : Nat := 4983230072969 + 3 ^ 40 * 784807 * 2
def baseEnd_784807 : Nat := 179103649783651632312553

theorem tailTrace_784807 : CollatzResearch.WordTrace tailWord_784807 prefixEnd_784807 179103649783651632312553 := by
  unfold tailWord_784807
  simp only [CollatzResearch.WordTrace]
  refine ⟨28624262867785748209688675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19082841911857165473125783 28624262867785748209688675)
  ·
    refine ⟨42936394301678622314533013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28624262867785748209688675 42936394301678622314533013)
    ·
      refine ⟨2012643482891185420993735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42936394301678622314533013 2012643482891185420993735)
      ·
        refine ⟨3018965224336778131490603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2012643482891185420993735 3018965224336778131490603)
        ·
          refine ⟨4528447836505167197235905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3018965224336778131490603 4528447836505167197235905)
          ·
            refine ⟨3396335877378875397926929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4528447836505167197235905 3396335877378875397926929)
            ·
              refine ⟨2547251908034156548445197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3396335877378875397926929 2547251908034156548445197)
              ·
                refine ⟨955219465512808705666949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2547251908034156548445197 955219465512808705666949)
                ·
                  refine ⟨179103649783651632312553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 955219465512808705666949 179103649783651632312553)
                  ·
                    rfl

theorem cell21_784807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 4].length) (baseStart_784807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_784807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_784807 prefixEnd_784807 := by exact prefixLift 784807
  have htrace : WordTrace (prefixWord ++ tailWord_784807) baseStart_784807 baseEnd_784807 := by
    simpa [prefixWord, tailWord_784807, baseEnd_784807] using wordTrace_append hprefix tailTrace_784807
  have hstable : (prefixWord ++ tailWord_784807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784807).length < 2 ^ (prefixWord ++ tailWord_784807).sum := by decide
  have hdescent : baseEnd_784807 < baseStart_784807 := by decide
  rcases family_descends (prefixWord ++ tailWord_784807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784852 : List Nat := [2, 4, 1, 2, 2, 1, 1, 3, 5]
def baseStart_784852 : Nat := 118140960795 + 784852 * 2 ^ 59
def prefixEnd_784852 : Nat := 4983230072969 + 3 ^ 40 * 784852 * 2
def baseEnd_784852 : Nat := 179113919396741554062461

theorem tailTrace_784852 : CollatzResearch.WordTrace tailWord_784852 prefixEnd_784852 179113919396741554062461 := by
  unfold tailWord_784852
  simp only [CollatzResearch.WordTrace]
  refine ⟨14312952076311360447538405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19083936101748480596717873 14312952076311360447538405)
  ·
    refine ⟨2683678514308380083913451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14312952076311360447538405 2683678514308380083913451)
    ·
      refine ⟨4025517771462570125870177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2683678514308380083913451 4025517771462570125870177)
      ·
        refine ⟨3019138328596927594402633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4025517771462570125870177 3019138328596927594402633)
        ·
          refine ⟨2264353746447695695801975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3019138328596927594402633 2264353746447695695801975)
          ·
            refine ⟨3396530619671543543702963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2264353746447695695801975 3396530619671543543702963)
            ·
              refine ⟨5094795929507315315554445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3396530619671543543702963 5094795929507315315554445)
              ·
                refine ⟨1910548473565243243332917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5094795929507315315554445 1910548473565243243332917)
                ·
                  refine ⟨179113919396741554062461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1910548473565243243332917 179113919396741554062461)
                  ·
                    rfl

theorem cell21_784852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_784852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_784852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_784852 prefixEnd_784852 := by exact prefixLift 784852
  have htrace : WordTrace (prefixWord ++ tailWord_784852) baseStart_784852 baseEnd_784852 := by
    simpa [prefixWord, tailWord_784852, baseEnd_784852] using wordTrace_append hprefix tailTrace_784852
  have hstable : (prefixWord ++ tailWord_784852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784852).length < 2 ^ (prefixWord ++ tailWord_784852).sum := by decide
  have hdescent : baseEnd_784852 < baseStart_784852 := by decide
  rcases family_descends (prefixWord ++ tailWord_784852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784880 : List Nat := [2, 1, 1, 1, 3, 3, 3, 7]
def baseStart_784880 : Nat := 118140960795 + 784880 * 2 ^ 59
def prefixEnd_784880 : Nat := 4983230072969 + 3 ^ 40 * 784880 * 2
def baseEnd_784880 : Nat := 59706769792739909198579

theorem tailTrace_784880 : CollatzResearch.WordTrace tailWord_784880 prefixEnd_784880 59706769792739909198579 := by
  unfold tailWord_784880
  simp only [CollatzResearch.WordTrace]
  refine ⟨14313462698260640838548047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19084616931014187784730729 14313462698260640838548047)
  ·
    refine ⟨21470194047390961257822071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14313462698260640838548047 21470194047390961257822071)
    ·
      refine ⟨32205291071086441886733107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21470194047390961257822071 32205291071086441886733107)
      ·
        refine ⟨48307936606629662830099661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32205291071086441886733107 48307936606629662830099661)
        ·
          refine ⟨18115476227486123561287373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48307936606629662830099661 18115476227486123561287373)
          ·
            refine ⟨6793303585307296335482765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18115476227486123561287373 6793303585307296335482765)
            ·
              refine ⟨2547488844490236125806037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6793303585307296335482765 2547488844490236125806037)
              ·
                refine ⟨59706769792739909198579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2547488844490236125806037 59706769792739909198579)
                ·
                  rfl

theorem cell21_784880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 7].length) (baseStart_784880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_784880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_784880 prefixEnd_784880 := by exact prefixLift 784880
  have htrace : WordTrace (prefixWord ++ tailWord_784880) baseStart_784880 baseEnd_784880 := by
    simpa [prefixWord, tailWord_784880, baseEnd_784880] using wordTrace_append hprefix tailTrace_784880
  have hstable : (prefixWord ++ tailWord_784880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784880).length < 2 ^ (prefixWord ++ tailWord_784880).sum := by decide
  have hdescent : baseEnd_784880 < baseStart_784880 := by decide
  rcases family_descends (prefixWord ++ tailWord_784880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784897 : List Nat := [1, 2, 4, 1, 3, 3, 7]
def baseStart_784897 : Nat := 118140960795 + 784897 * 2 ^ 59
def prefixEnd_784897 : Nat := 4983230072969 + 3 ^ 40 * 784897 * 2
def baseEnd_784897 : Nat := 19902687667759052868041

theorem tailTrace_784897 : CollatzResearch.WordTrace tailWord_784897 prefixEnd_784897 19902687667759052868041 := by
  unfold tailWord_784897
  simp only [CollatzResearch.WordTrace]
  refine ⟨28627545437459693580464945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19085030291639795720309963 28627545437459693580464945)
  ·
    refine ⟨21470659078094770185348709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28627545437459693580464945 21470659078094770185348709)
    ·
      refine ⟨4025748577142769409752883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21470659078094770185348709 4025748577142769409752883)
      ·
        refine ⟨6038622865714154114629325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4025748577142769409752883 6038622865714154114629325)
        ·
          refine ⟨2264483574642807792985997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6038622865714154114629325 2264483574642807792985997)
          ·
            refine ⟨849181340491052922369749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2264483574642807792985997 849181340491052922369749)
            ·
              refine ⟨19902687667759052868041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 849181340491052922369749 19902687667759052868041)
              ·
                rfl

theorem cell21_784897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 7].length) (baseStart_784897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_784897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_784897 prefixEnd_784897 := by exact prefixLift 784897
  have htrace : WordTrace (prefixWord ++ tailWord_784897) baseStart_784897 baseEnd_784897 := by
    simpa [prefixWord, tailWord_784897, baseEnd_784897] using wordTrace_append hprefix tailTrace_784897
  have hstable : (prefixWord ++ tailWord_784897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784897).length < 2 ^ (prefixWord ++ tailWord_784897).sum := by decide
  have hdescent : baseEnd_784897 < baseStart_784897 := by decide
  rcases family_descends (prefixWord ++ tailWord_784897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_784956 : List Nat := [2, 2, 2, 2, 3, 10]
def baseStart_784956 : Nat := 118140960795 + 784956 * 2 ^ 59
def prefixEnd_784956 : Nat := 4983230072969 + 3 ^ 40 * 784956 * 2
def baseEnd_784956 : Nat := 6634727911617054975145

theorem tailTrace_784956 : CollatzResearch.WordTrace tailWord_784956 prefixEnd_784956 6634727911617054975145 := by
  unfold tailWord_784956
  simp only [CollatzResearch.WordTrace]
  refine ⟨14314848672122973328431361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19086464896163964437908481 14314848672122973328431361)
  ·
    refine ⟨10736136504092229996323521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14314848672122973328431361 10736136504092229996323521)
    ·
      refine ⟨8052102378069172497242641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10736136504092229996323521 8052102378069172497242641)
      ·
        refine ⟨6039076783551879372931981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8052102378069172497242641 6039076783551879372931981)
        ·
          refine ⟨2264653793831954764849493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6039076783551879372931981 2264653793831954764849493)
          ·
            refine ⟨6634727911617054975145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2264653793831954764849493 6634727911617054975145)
            ·
              rfl

theorem cell21_784956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 10].length) (baseStart_784956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_784956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_784956 prefixEnd_784956 := by exact prefixLift 784956
  have htrace : WordTrace (prefixWord ++ tailWord_784956) baseStart_784956 baseEnd_784956 := by
    simpa [prefixWord, tailWord_784956, baseEnd_784956] using wordTrace_append hprefix tailTrace_784956
  have hstable : (prefixWord ++ tailWord_784956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_784956).length < 2 ^ (prefixWord ++ tailWord_784956).sum := by decide
  have hdescent : baseEnd_784956 < baseStart_784956 := by decide
  rcases family_descends (prefixWord ++ tailWord_784956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785001 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 6]
def baseStart_785001 : Nat := 118140960795 + 785001 * 2 ^ 59
def prefixEnd_785001 : Nat := 4983230072969 + 3 ^ 40 * 785001 * 2
def baseEnd_785001 : Nat := 179147923226750406078823

theorem tailTrace_785001 : CollatzResearch.WordTrace tailWord_785001 prefixEnd_785001 179147923226750406078823 := by
  unfold tailWord_785001
  simp only [CollatzResearch.WordTrace]
  refine ⟨28631338629082919342250857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19087559086055279561500571 28631338629082919342250857)
  ·
    refine ⟨21473503971812189506688143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28631338629082919342250857 21473503971812189506688143)
    ·
      refine ⟨32210255957718284260032215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21473503971812189506688143 32210255957718284260032215)
      ·
        refine ⟨48315383936577426390048323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32210255957718284260032215 48315383936577426390048323)
        ·
          refine ⟨72473075904866139585072485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48315383936577426390048323 72473075904866139585072485)
          ·
            refine ⟨13588701732162401172201091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72473075904866139585072485 13588701732162401172201091)
            ·
              refine ⟨20383052598243601758301637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13588701732162401172201091 20383052598243601758301637)
              ·
                refine ⟨3821822362170675329681557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20383052598243601758301637 3821822362170675329681557)
                ·
                  refine ⟨179147923226750406078823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3821822362170675329681557 179147923226750406078823)
                  ·
                    rfl

theorem cell21_785001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_785001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785001 prefixEnd_785001 := by exact prefixLift 785001
  have htrace : WordTrace (prefixWord ++ tailWord_785001) baseStart_785001 baseEnd_785001 := by
    simpa [prefixWord, tailWord_785001, baseEnd_785001] using wordTrace_append hprefix tailTrace_785001
  have hstable : (prefixWord ++ tailWord_785001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785001).length < 2 ^ (prefixWord ++ tailWord_785001).sum := by decide
  have hdescent : baseEnd_785001 < baseStart_785001 := by decide
  rcases family_descends (prefixWord ++ tailWord_785001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785004 : List Nat := [2, 2, 1, 1, 3, 1, 3, 5, 3]
def baseStart_785004 : Nat := 118140960795 + 785004 * 2 ^ 59
def prefixEnd_785004 : Nat := 4983230072969 + 3 ^ 40 * 785004 * 2
def baseEnd_785004 : Nat := 179148607867623067528817

theorem tailTrace_785004 : CollatzResearch.WordTrace tailWord_785004 prefixEnd_785004 179148607867623067528817 := by
  unfold tailWord_785004
  simp only [CollatzResearch.WordTrace]
  refine ⟨14315724024036025427305033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19087632032048033903073377 14315724024036025427305033)
  ·
    refine ⟨10736793018027019070478775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14315724024036025427305033 10736793018027019070478775)
    ·
      refine ⟨16105189527040528605718163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10736793018027019070478775 16105189527040528605718163)
      ·
        refine ⟨24157784290560792908577245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16105189527040528605718163 24157784290560792908577245)
        ·
          refine ⟨9059169108960297340716467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24157784290560792908577245 9059169108960297340716467)
          ·
            refine ⟨13588753663440446011074701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9059169108960297340716467 13588753663440446011074701)
            ·
              refine ⟨5095782623790167254153013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13588753663440446011074701 5095782623790167254153013)
              ·
                refine ⟨477729620980328180076845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5095782623790167254153013 477729620980328180076845)
                ·
                  refine ⟨179148607867623067528817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 477729620980328180076845 179148607867623067528817)
                  ·
                    rfl

theorem cell21_785004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_785004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785004 prefixEnd_785004 := by exact prefixLift 785004
  have htrace : WordTrace (prefixWord ++ tailWord_785004) baseStart_785004 baseEnd_785004 := by
    simpa [prefixWord, tailWord_785004, baseEnd_785004] using wordTrace_append hprefix tailTrace_785004
  have hstable : (prefixWord ++ tailWord_785004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785004).length < 2 ^ (prefixWord ++ tailWord_785004).sum := by decide
  have hdescent : baseEnd_785004 < baseStart_785004 := by decide
  rcases family_descends (prefixWord ++ tailWord_785004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785153 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 8]
def baseStart_785153 : Nat := 118140960795 + 785153 * 2 ^ 59
def prefixEnd_785153 : Nat := 4983230072969 + 3 ^ 40 * 785153 * 2
def baseEnd_785153 : Nat := 179182611697631919545179

theorem tailTrace_785153 : CollatzResearch.WordTrace tailWord_785153 prefixEnd_785153 179182611697631919545179 := by
  unfold tailWord_785153
  simp only [CollatzResearch.WordTrace]
  refine ⟨28636882524532249301784113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19091255016354832867856075 28636882524532249301784113)
  ·
    refine ⟨21477661893399186976338085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28636882524532249301784113 21477661893399186976338085)
    ·
      refine ⟨4027061605012347558063391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21477661893399186976338085 4027061605012347558063391)
      ·
        refine ⟨6040592407518521337095087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4027061605012347558063391 6040592407518521337095087)
        ·
          refine ⟨9060888611277782005642631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6040592407518521337095087 9060888611277782005642631)
          ·
            refine ⟨13591332916916673008463947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9060888611277782005642631 13591332916916673008463947)
            ·
              refine ⟨20386999375375009512695921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13591332916916673008463947 20386999375375009512695921)
              ·
                refine ⟨15290249531531257134521941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20386999375375009512695921 15290249531531257134521941)
                ·
                  refine ⟨179182611697631919545179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15290249531531257134521941 179182611697631919545179)
                  ·
                    rfl

theorem cell21_785153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 8].length) (baseStart_785153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785153 prefixEnd_785153 := by exact prefixLift 785153
  have htrace : WordTrace (prefixWord ++ tailWord_785153) baseStart_785153 baseEnd_785153 := by
    simpa [prefixWord, tailWord_785153, baseEnd_785153] using wordTrace_append hprefix tailTrace_785153
  have hstable : (prefixWord ++ tailWord_785153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785153).length < 2 ^ (prefixWord ++ tailWord_785153).sum := by decide
  have hdescent : baseEnd_785153 < baseStart_785153 := by decide
  rcases family_descends (prefixWord ++ tailWord_785153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785184 : List Nat := [2, 1, 1, 5, 1, 3, 8]
def baseStart_785184 : Nat := 118140960795 + 785184 * 2 ^ 59
def prefixEnd_785184 : Nat := 4983230072969 + 3 ^ 40 * 785184 * 2
def baseEnd_785184 : Nat := 19909965146664750503161

theorem tailTrace_785184 : CollatzResearch.WordTrace tailWord_785184 prefixEnd_785184 19909965146664750503161 := by
  unfold tailWord_785184
  simp only [CollatzResearch.WordTrace]
  refine ⟨14319006593709970798081303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19092008791613294397441737 14319006593709970798081303)
  ·
    refine ⟨21478509890564956197121955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14319006593709970798081303 21478509890564956197121955)
    ·
      refine ⟨32217764835847434295682933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21478509890564956197121955 32217764835847434295682933)
      ·
        refine ⟨3020415453360696965220275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32217764835847434295682933 3020415453360696965220275)
        ·
          refine ⟨4530623180041045447830413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3020415453360696965220275 4530623180041045447830413)
          ·
            refine ⟨1698983692515392042936405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4530623180041045447830413 1698983692515392042936405)
            ·
              refine ⟨19909965146664750503161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1698983692515392042936405 19909965146664750503161)
              ·
                rfl

theorem cell21_785184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 8].length) (baseStart_785184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785184 prefixEnd_785184 := by exact prefixLift 785184
  have htrace : WordTrace (prefixWord ++ tailWord_785184) baseStart_785184 baseEnd_785184 := by
    simpa [prefixWord, tailWord_785184, baseEnd_785184] using wordTrace_append hprefix tailTrace_785184
  have hstable : (prefixWord ++ tailWord_785184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785184).length < 2 ^ (prefixWord ++ tailWord_785184).sum := by decide
  have hdescent : baseEnd_785184 < baseStart_785184 := by decide
  rcases family_descends (prefixWord ++ tailWord_785184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785215 : List Nat := [1, 1, 2, 2, 5, 1, 2, 2, 5]
def baseStart_785215 : Nat := 118140960795 + 785215 * 2 ^ 59
def prefixEnd_785215 : Nat := 4983230072969 + 3 ^ 40 * 785215 * 2
def baseEnd_785215 : Nat := 179196760942333589511719

theorem tailTrace_785215 : CollatzResearch.WordTrace tailWord_785215 prefixEnd_785215 179196760942333589511719 := by
  unfold tailWord_785215
  simp only [CollatzResearch.WordTrace]
  refine ⟨28639143850307633890541099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19092762566871755927027399 28639143850307633890541099)
  ·
    refine ⟨42958715775461450835811649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28639143850307633890541099 42958715775461450835811649)
    ·
      refine ⟨32219036831596088126858737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42958715775461450835811649 32219036831596088126858737)
      ·
        refine ⟨24164277623697066095144053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32219036831596088126858737 24164277623697066095144053)
        ·
          refine ⟨2265401027221599946419755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24164277623697066095144053 2265401027221599946419755)
          ·
            refine ⟨3398101540832399919629633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2265401027221599946419755 3398101540832399919629633)
            ·
              refine ⟨2548576155624299939722225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3398101540832399919629633 2548576155624299939722225)
              ·
                refine ⟨1911432116718224954791669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2548576155624299939722225 1911432116718224954791669)
                ·
                  refine ⟨179196760942333589511719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1911432116718224954791669 179196760942333589511719)
                  ·
                    rfl

theorem cell21_785215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 5].length) (baseStart_785215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785215 prefixEnd_785215 := by exact prefixLift 785215
  have htrace : WordTrace (prefixWord ++ tailWord_785215) baseStart_785215 baseEnd_785215 := by
    simpa [prefixWord, tailWord_785215, baseEnd_785215] using wordTrace_append hprefix tailTrace_785215
  have hstable : (prefixWord ++ tailWord_785215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785215).length < 2 ^ (prefixWord ++ tailWord_785215).sum := by decide
  have hdescent : baseEnd_785215 < baseStart_785215 := by decide
  rcases family_descends (prefixWord ++ tailWord_785215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785232 : List Nat := [2, 1, 1, 1, 1, 4, 5, 3, 3]
def baseStart_785232 : Nat := 118140960795 + 785232 * 2 ^ 59
def prefixEnd_785232 : Nat := 4983230072969 + 3 ^ 40 * 785232 * 2
def baseEnd_785232 : Nat := 179200640573945337728351

theorem tailTrace_785232 : CollatzResearch.WordTrace tailWord_785232 prefixEnd_785232 179200640573945337728351 := by
  unfold tailWord_785232
  simp only [CollatzResearch.WordTrace]
  refine ⟨14319881945623022896954975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19093175927497363862606633 14319881945623022896954975)
  ·
    refine ⟨21479822918434534345432463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14319881945623022896954975 21479822918434534345432463)
    ·
      refine ⟨32219734377651801518148695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21479822918434534345432463 32219734377651801518148695)
      ·
        refine ⟨48329601566477702277223043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32219734377651801518148695 48329601566477702277223043)
        ·
          refine ⟨72494402349716553415834565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48329601566477702277223043 72494402349716553415834565)
          ·
            refine ⟨13592700440571853765468981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72494402349716553415834565 13592700440571853765468981)
            ·
              refine ⟨1274315666303611290512717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13592700440571853765468981 1274315666303611290512717)
              ·
                refine ⟨477868374863854233942269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1274315666303611290512717 477868374863854233942269)
                ·
                  refine ⟨179200640573945337728351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 477868374863854233942269 179200640573945337728351)
                  ·
                    rfl

theorem cell21_785232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 3].length) (baseStart_785232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785232 prefixEnd_785232 := by exact prefixLift 785232
  have htrace : WordTrace (prefixWord ++ tailWord_785232) baseStart_785232 baseEnd_785232 := by
    simpa [prefixWord, tailWord_785232, baseEnd_785232] using wordTrace_append hprefix tailTrace_785232
  have hstable : (prefixWord ++ tailWord_785232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785232).length < 2 ^ (prefixWord ++ tailWord_785232).sum := by decide
  have hdescent : baseEnd_785232 < baseStart_785232 := by decide
  rcases family_descends (prefixWord ++ tailWord_785232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785260 : List Nat := [2, 2, 1, 1, 4, 1, 4, 6]
def baseStart_785260 : Nat := 118140960795 + 785260 * 2 ^ 59
def prefixEnd_785260 : Nat := 4983230072969 + 3 ^ 40 * 785260 * 2
def baseEnd_785260 : Nat := 59735676851807837087209

theorem tailTrace_785260 : CollatzResearch.WordTrace tailWord_785260 prefixEnd_785260 59735676851807837087209 := by
  unfold tailWord_785260
  simp only [CollatzResearch.WordTrace]
  refine ⟨14320392567572303287964617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19093856756763071050619489 14320392567572303287964617)
  ·
    refine ⟨10740294425679227465973463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14320392567572303287964617 10740294425679227465973463)
    ·
      refine ⟨16110441638518841198960195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10740294425679227465973463 16110441638518841198960195)
      ·
        refine ⟨24165662457778261798440293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16110441638518841198960195 24165662457778261798440293)
        ·
          refine ⟨4531061710833424087207555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24165662457778261798440293 4531061710833424087207555)
          ·
            refine ⟨6796592566250136130811333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4531061710833424087207555 6796592566250136130811333)
            ·
              refine ⟨1274361106171900524527125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6796592566250136130811333 1274361106171900524527125)
              ·
                refine ⟨59735676851807837087209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1274361106171900524527125 59735676851807837087209)
                ·
                  rfl

theorem cell21_785260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 6].length) (baseStart_785260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785260 prefixEnd_785260 := by exact prefixLift 785260
  have htrace : WordTrace (prefixWord ++ tailWord_785260) baseStart_785260 baseEnd_785260 := by
    simpa [prefixWord, tailWord_785260, baseEnd_785260] using wordTrace_append hprefix tailTrace_785260
  have hstable : (prefixWord ++ tailWord_785260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785260).length < 2 ^ (prefixWord ++ tailWord_785260).sum := by decide
  have hdescent : baseEnd_785260 < baseStart_785260 := by decide
  rcases family_descends (prefixWord ++ tailWord_785260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785274 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 7]
def baseStart_785274 : Nat := 118140960795 + 785274 * 2 ^ 59
def prefixEnd_785274 : Nat := 4983230072969 + 3 ^ 40 * 785274 * 2
def baseEnd_785274 : Nat := 179210225546162598028265

theorem tailTrace_785274 : CollatzResearch.WordTrace tailWord_785274 prefixEnd_785274 179210225546162598028265 := by
  unfold tailWord_785274
  simp only [CollatzResearch.WordTrace]
  refine ⟨7160323939273471741734719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19094197171395924644625917 7160323939273471741734719)
  ·
    refine ⟨10740485908910207612602079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7160323939273471741734719 10740485908910207612602079)
    ·
      refine ⟨16110728863365311418903119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10740485908910207612602079 16110728863365311418903119)
      ·
        refine ⟨24166093295047967128354679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16110728863365311418903119 24166093295047967128354679)
        ·
          refine ⟨36249139942571950692532019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24166093295047967128354679 36249139942571950692532019)
          ·
            refine ⟨54373709913857926038798029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36249139942571950692532019 54373709913857926038798029)
            ·
              refine ⟨20390141217696722264549261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54373709913857926038798029 20390141217696722264549261)
              ·
                refine ⟨7646302956636270849205973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20390141217696722264549261 7646302956636270849205973)
                ·
                  refine ⟨179210225546162598028265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7646302956636270849205973 179210225546162598028265)
                  ·
                    rfl

theorem cell21_785274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_785274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785274 prefixEnd_785274 := by exact prefixLift 785274
  have htrace : WordTrace (prefixWord ++ tailWord_785274) baseStart_785274 baseEnd_785274 := by
    simpa [prefixWord, tailWord_785274, baseEnd_785274] using wordTrace_append hprefix tailTrace_785274
  have hstable : (prefixWord ++ tailWord_785274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785274).length < 2 ^ (prefixWord ++ tailWord_785274).sum := by decide
  have hdescent : baseEnd_785274 < baseStart_785274 := by decide
  rcases family_descends (prefixWord ++ tailWord_785274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785325 : List Nat := [1, 5, 2, 3, 1, 1, 1, 2, 5]
def baseStart_785325 : Nat := 118140960795 + 785325 * 2 ^ 59
def prefixEnd_785325 : Nat := 4983230072969 + 3 ^ 40 * 785325 * 2
def baseEnd_785325 : Nat := 179221864440997842678161

theorem tailTrace_785325 : CollatzResearch.WordTrace tailWord_785325 prefixEnd_785325 179221864440997842678161 := by
  unfold tailWord_785325
  simp only [CollatzResearch.WordTrace]
  refine ⟨28643155879909122677045429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19095437253272748451363619 28643155879909122677045429)
  ·
    refine ⟨2685295863741480250973009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28643155879909122677045429 2685295863741480250973009)
    ·
      refine ⟨2013971897806110188229757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2685295863741480250973009 2013971897806110188229757)
      ·
        refine ⟨755239461677291320586159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2013971897806110188229757 755239461677291320586159)
        ·
          refine ⟨1132859192515936980879239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 755239461677291320586159 1132859192515936980879239)
          ·
            refine ⟨1699288788773905471318859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1132859192515936980879239 1699288788773905471318859)
            ·
              refine ⟨2548933183160858206978289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1699288788773905471318859 2548933183160858206978289)
              ·
                refine ⟨1911699887370643655233717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2548933183160858206978289 1911699887370643655233717)
                ·
                  refine ⟨179221864440997842678161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1911699887370643655233717 179221864440997842678161)
                  ·
                    rfl

theorem cell21_785325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_785325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785325 prefixEnd_785325 := by exact prefixLift 785325
  have htrace : WordTrace (prefixWord ++ tailWord_785325) baseStart_785325 baseEnd_785325 := by
    simpa [prefixWord, tailWord_785325, baseEnd_785325] using wordTrace_append hprefix tailTrace_785325
  have hstable : (prefixWord ++ tailWord_785325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785325).length < 2 ^ (prefixWord ++ tailWord_785325).sum := by decide
  have hdescent : baseEnd_785325 < baseStart_785325 := by decide
  rcases family_descends (prefixWord ++ tailWord_785325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785398 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_785398 : Nat := 118140960795 + 785398 * 2 ^ 59
def prefixEnd_785398 : Nat := 4983230072969 + 3 ^ 40 * 785398 * 2
def baseEnd_785398 : Nat := 179238524035565937961345

theorem tailTrace_785398 : CollatzResearch.WordTrace tailWord_785398 prefixEnd_785398 179238524035565937961345 := by
  unfold tailWord_785398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1790363650540291009028303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19097212272429770762968565 1790363650540291009028303)
  ·
    refine ⟨2685545475810436513542455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1790363650540291009028303 2685545475810436513542455)
    ·
      refine ⟨4028318213715654770313683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2685545475810436513542455 4028318213715654770313683)
      ·
        refine ⟨6042477320573482155470525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4028318213715654770313683 6042477320573482155470525)
        ·
          refine ⟨2265928995215055808301447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6042477320573482155470525 2265928995215055808301447)
          ·
            refine ⟨3398893492822583712452171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2265928995215055808301447 3398893492822583712452171)
            ·
              refine ⟨5098340239233875568678257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3398893492822583712452171 5098340239233875568678257)
              ·
                refine ⟨3823755179425406676508693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5098340239233875568678257 3823755179425406676508693)
                ·
                  refine ⟨179238524035565937961345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3823755179425406676508693 179238524035565937961345)
                  ·
                    rfl

theorem cell21_785398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_785398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785398 prefixEnd_785398 := by exact prefixLift 785398
  have htrace : WordTrace (prefixWord ++ tailWord_785398) baseStart_785398 baseEnd_785398 := by
    simpa [prefixWord, tailWord_785398, baseEnd_785398] using wordTrace_append hprefix tailTrace_785398
  have hstable : (prefixWord ++ tailWord_785398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785398).length < 2 ^ (prefixWord ++ tailWord_785398).sum := by decide
  have hdescent : baseEnd_785398 < baseStart_785398 := by decide
  rcases family_descends (prefixWord ++ tailWord_785398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785525 : List Nat := [1, 3, 4, 3, 2, 1, 1, 2, 4]
def baseStart_785525 : Nat := 118140960795 + 785525 * 2 ^ 59
def prefixEnd_785525 : Nat := 4983230072969 + 3 ^ 40 * 785525 * 2
def baseEnd_785525 : Nat := 179267507165841939344419

theorem tailTrace_785525 : CollatzResearch.WordTrace tailWord_785525 prefixEnd_785525 179267507165841939344419 := by
  unfold tailWord_785525
  simp only [CollatzResearch.WordTrace]
  refine ⟨28650450479184556834326029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19100300319456371222884019 28650450479184556834326029)
  ·
    refine ⟨10743918929694208812872261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28650450479184556834326029 10743918929694208812872261)
    ·
      refine ⟨2014484799317664152413549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10743918929694208812872261 2014484799317664152413549)
      ·
        refine ⟨755431799744124057155081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2014484799317664152413549 755431799744124057155081)
        ·
          refine ⟨566573849808093042866311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 755431799744124057155081 566573849808093042866311)
          ·
            refine ⟨849860774712139564299467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566573849808093042866311 849860774712139564299467)
            ·
              refine ⟨1274791162068209346449201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849860774712139564299467 1274791162068209346449201)
              ·
                refine ⟨956093371551157009836901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1274791162068209346449201 956093371551157009836901)
                ·
                  refine ⟨179267507165841939344419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 956093371551157009836901 179267507165841939344419)
                  ·
                    rfl

theorem cell21_785525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 4].length) (baseStart_785525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785525 prefixEnd_785525 := by exact prefixLift 785525
  have htrace : WordTrace (prefixWord ++ tailWord_785525) baseStart_785525 baseEnd_785525 := by
    simpa [prefixWord, tailWord_785525, baseEnd_785525] using wordTrace_append hprefix tailTrace_785525
  have hstable : (prefixWord ++ tailWord_785525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785525).length < 2 ^ (prefixWord ++ tailWord_785525).sum := by decide
  have hdescent : baseEnd_785525 < baseStart_785525 := by decide
  rcases family_descends (prefixWord ++ tailWord_785525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785533 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 6]
def baseStart_785533 : Nat := 118140960795 + 785533 * 2 ^ 59
def prefixEnd_785533 : Nat := 4983230072969 + 3 ^ 40 * 785533 * 2
def baseEnd_785533 : Nat := 179269332874835703211069

theorem tailTrace_785533 : CollatzResearch.WordTrace tailWord_785533 prefixEnd_785533 179269332874835703211069 := by
  unfold tailWord_785533
  simp only [CollatzResearch.WordTrace]
  refine ⟨28650742263155574200617253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19100494842103716133744835 28650742263155574200617253)
  ·
    refine ⟨5372014174341670162615735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28650742263155574200617253 5372014174341670162615735)
    ·
      refine ⟨8058021261512505243923603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5372014174341670162615735 8058021261512505243923603)
      ·
        refine ⟨12087031892268757865885405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8058021261512505243923603 12087031892268757865885405)
        ·
          refine ⟨4532636959600784199707027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12087031892268757865885405 4532636959600784199707027)
          ·
            refine ⟨6798955439401176299560541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4532636959600784199707027 6798955439401176299560541)
            ·
              refine ⟨2549608289775441112335203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6798955439401176299560541 2549608289775441112335203)
              ·
                refine ⟨3824412434663161668502805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2549608289775441112335203 3824412434663161668502805)
                ·
                  refine ⟨179269332874835703211069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3824412434663161668502805 179269332874835703211069)
                  ·
                    rfl

theorem cell21_785533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_785533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785533 prefixEnd_785533 := by exact prefixLift 785533
  have htrace : WordTrace (prefixWord ++ tailWord_785533) baseStart_785533 baseEnd_785533 := by
    simpa [prefixWord, tailWord_785533, baseEnd_785533] using wordTrace_append hprefix tailTrace_785533
  have hstable : (prefixWord ++ tailWord_785533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785533).length < 2 ^ (prefixWord ++ tailWord_785533).sum := by decide
  have hdescent : baseEnd_785533 < baseStart_785533 := by decide
  rcases family_descends (prefixWord ++ tailWord_785533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785564 : List Nat := [2, 2, 3, 2, 1, 3, 1, 7]
def baseStart_785564 : Nat := 118140960795 + 785564 * 2 ^ 59
def prefixEnd_785564 : Nat := 4983230072969 + 3 ^ 40 * 785564 * 2
def baseEnd_785564 : Nat := 59758802499062179398113

theorem tailTrace_785564 : CollatzResearch.WordTrace tailWord_785564 prefixEnd_785564 59758802499062179398113 := by
  unfold tailWord_785564
  simp only [CollatzResearch.WordTrace]
  refine ⟨14325936463021633247497873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19101248617362177663330497 14325936463021633247497873)
  ·
    refine ⟨10744452347266224935623405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14325936463021633247497873 10744452347266224935623405)
    ·
      refine ⟨4029169630224834350858777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10744452347266224935623405 4029169630224834350858777)
      ·
        refine ⟨3021877222668625763144083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4029169630224834350858777 3021877222668625763144083)
        ·
          refine ⟨4532815834002938644716125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3021877222668625763144083 4532815834002938644716125)
          ·
            refine ⟨1699805937751101991768547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4532815834002938644716125 1699805937751101991768547)
            ·
              refine ⟨2549708906626652987652821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1699805937751101991768547 2549708906626652987652821)
              ·
                refine ⟨59758802499062179398113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2549708906626652987652821 59758802499062179398113)
                ·
                  rfl

theorem cell21_785564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 7].length) (baseStart_785564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785564 prefixEnd_785564 := by exact prefixLift 785564
  have htrace : WordTrace (prefixWord ++ tailWord_785564) baseStart_785564 baseEnd_785564 := by
    simpa [prefixWord, tailWord_785564, baseEnd_785564] using wordTrace_append hprefix tailTrace_785564
  have hstable : (prefixWord ++ tailWord_785564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785564).length < 2 ^ (prefixWord ++ tailWord_785564).sum := by decide
  have hdescent : baseEnd_785564 < baseStart_785564 := by decide
  rcases family_descends (prefixWord ++ tailWord_785564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785570 : List Nat := [3, 3, 1, 3, 2, 2, 1, 3, 3]
def baseStart_785570 : Nat := 118140960795 + 785570 * 2 ^ 59
def prefixEnd_785570 : Nat := 4983230072969 + 3 ^ 40 * 785570 * 2
def baseEnd_785570 : Nat := 179277776778931861094327

theorem tailTrace_785570 : CollatzResearch.WordTrace tailWord_785570 prefixEnd_785570 179277776778931861094327 := by
  unfold tailWord_785570
  simp only [CollatzResearch.WordTrace]
  refine ⟨7163022941005382379928541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19101394509347686346476109 7163022941005382379928541)
  ·
    refine ⟨2686133602877018392473203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7163022941005382379928541 2686133602877018392473203)
    ·
      refine ⟨4029200404315527588709805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2686133602877018392473203 4029200404315527588709805)
      ·
        refine ⟨1510950151618322845766177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4029200404315527588709805 1510950151618322845766177)
        ·
          refine ⟨1133212613713742134324633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1510950151618322845766177 1133212613713742134324633)
          ·
            refine ⟨849909460285306600743475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1133212613713742134324633 849909460285306600743475)
            ·
              refine ⟨1274864190427959901115213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849909460285306600743475 1274864190427959901115213)
              ·
                refine ⟨478074071410484962918205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1274864190427959901115213 478074071410484962918205)
                ·
                  refine ⟨179277776778931861094327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 478074071410484962918205 179277776778931861094327)
                  ·
                    rfl

theorem cell21_785570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_785570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785570 prefixEnd_785570 := by exact prefixLift 785570
  have htrace : WordTrace (prefixWord ++ tailWord_785570) baseStart_785570 baseEnd_785570 := by
    simpa [prefixWord, tailWord_785570, baseEnd_785570] using wordTrace_append hprefix tailTrace_785570
  have hstable : (prefixWord ++ tailWord_785570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785570).length < 2 ^ (prefixWord ++ tailWord_785570).sum := by decide
  have hdescent : baseEnd_785570 < baseStart_785570 := by decide
  rcases family_descends (prefixWord ++ tailWord_785570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785581 : List Nat := [1, 5, 2, 1, 3, 2, 7]
def baseStart_785581 : Nat := 118140960795 + 785581 * 2 ^ 59
def prefixEnd_785581 : Nat := 4983230072969 + 3 ^ 40 * 785581 * 2
def baseEnd_785581 : Nat := 19920031903199809601219

theorem tailTrace_785581 : CollatzResearch.WordTrace tailWord_785581 prefixEnd_785581 19920031903199809601219 := by
  unfold tailWord_785581
  simp only [CollatzResearch.WordTrace]
  refine ⟨28652492966981678398364597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19101661977987785598909731 28652492966981678398364597)
  ·
    refine ⟨2686171215654532349846681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28652492966981678398364597 2686171215654532349846681)
    ·
      refine ⟨2014628411740899262385011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2686171215654532349846681 2014628411740899262385011)
      ·
        refine ⟨3021942617611348893577517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2014628411740899262385011 3021942617611348893577517)
        ·
          refine ⟨1133228481604255835091569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3021942617611348893577517 1133228481604255835091569)
          ·
            refine ⟨849921361203191876318677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1133228481604255835091569 849921361203191876318677)
            ·
              refine ⟨19920031903199809601219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 849921361203191876318677 19920031903199809601219)
              ·
                rfl

theorem cell21_785581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 7].length) (baseStart_785581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785581 prefixEnd_785581 := by exact prefixLift 785581
  have htrace : WordTrace (prefixWord ++ tailWord_785581) baseStart_785581 baseEnd_785581 := by
    simpa [prefixWord, tailWord_785581, baseEnd_785581] using wordTrace_append hprefix tailTrace_785581
  have hstable : (prefixWord ++ tailWord_785581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785581).length < 2 ^ (prefixWord ++ tailWord_785581).sum := by decide
  have hdescent : baseEnd_785581 < baseStart_785581 := by decide
  rcases family_descends (prefixWord ++ tailWord_785581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785623 : List Nat := [1, 1, 3, 2, 1, 2, 4, 7]
def baseStart_785623 : Nat := 118140960795 + 785623 * 2 ^ 59
def prefixEnd_785623 : Nat := 4983230072969 + 3 ^ 40 * 785623 * 2
def baseEnd_785623 : Nat := 59763290700338515570295

theorem tailTrace_785623 : CollatzResearch.WordTrace tailWord_785623 prefixEnd_785623 59763290700338515570295 := by
  unfold tailWord_785623
  simp only [CollatzResearch.WordTrace]
  refine ⟨28654024832829519571393523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19102683221886346380929015 28654024832829519571393523)
  ·
    refine ⟨42981037249244279357090285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28654024832829519571393523 42981037249244279357090285)
    ·
      refine ⟨16117888968466604758908857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42981037249244279357090285 16117888968466604758908857)
      ·
        refine ⟨12088416726349953569181643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16117888968466604758908857 12088416726349953569181643)
        ·
          refine ⟨18132625089524930353772465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12088416726349953569181643 18132625089524930353772465)
          ·
            refine ⟨13599468817143697765329349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18132625089524930353772465 13599468817143697765329349)
            ·
              refine ⟨2549900403214443330999253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13599468817143697765329349 2549900403214443330999253)
              ·
                refine ⟨59763290700338515570295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2549900403214443330999253 59763290700338515570295)
                ·
                  rfl

theorem cell21_785623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 7].length) (baseStart_785623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785623 prefixEnd_785623 := by exact prefixLift 785623
  have htrace : WordTrace (prefixWord ++ tailWord_785623) baseStart_785623 baseEnd_785623 := by
    simpa [prefixWord, tailWord_785623, baseEnd_785623] using wordTrace_append hprefix tailTrace_785623
  have hstable : (prefixWord ++ tailWord_785623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785623).length < 2 ^ (prefixWord ++ tailWord_785623).sum := by decide
  have hdescent : baseEnd_785623 < baseStart_785623 := by decide
  rcases family_descends (prefixWord ++ tailWord_785623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785688 : List Nat := [2, 1, 2, 3, 1, 4, 2, 3, 3]
def baseStart_785688 : Nat := 118140960795 + 785688 * 2 ^ 59
def prefixEnd_785688 : Nat := 4983230072969 + 3 ^ 40 * 785688 * 2
def baseEnd_785688 : Nat := 179304705986589878127419

theorem tailTrace_785688 : CollatzResearch.WordTrace tailWord_785688 prefixEnd_785688 179304705986589878127419 := by
  unfold tailWord_785688
  simp only [CollatzResearch.WordTrace]
  refine ⟨14328197788797017836254859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19104263718396023781673145 14328197788797017836254859)
  ·
    refine ⟨21492296683195526754382289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14328197788797017836254859 21492296683195526754382289)
    ·
      refine ⟨16119222512396645065786717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21492296683195526754382289 16119222512396645065786717)
      ·
        refine ⟨6044708442148741899670019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16119222512396645065786717 6044708442148741899670019)
        ·
          refine ⟨9067062663223112849505029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6044708442148741899670019 9067062663223112849505029)
          ·
            refine ⟨1700074249354333659282193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9067062663223112849505029 1700074249354333659282193)
            ·
              refine ⟨1275055687015750244461645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1700074249354333659282193 1275055687015750244461645)
              ·
                refine ⟨478145882630906341673117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1275055687015750244461645 478145882630906341673117)
                ·
                  refine ⟨179304705986589878127419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 478145882630906341673117 179304705986589878127419)
                  ·
                    rfl

theorem cell21_785688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 3].length) (baseStart_785688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785688 prefixEnd_785688 := by exact prefixLift 785688
  have htrace : WordTrace (prefixWord ++ tailWord_785688) baseStart_785688 baseEnd_785688 := by
    simpa [prefixWord, tailWord_785688, baseEnd_785688] using wordTrace_append hprefix tailTrace_785688
  have hstable : (prefixWord ++ tailWord_785688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785688).length < 2 ^ (prefixWord ++ tailWord_785688).sum := by decide
  have hdescent : baseEnd_785688 < baseStart_785688 := by decide
  rcases family_descends (prefixWord ++ tailWord_785688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785699 : List Nat := [1, 1, 1, 4, 2, 4, 8]
def baseStart_785699 : Nat := 118140960795 + 785699 * 2 ^ 59
def prefixEnd_785699 : Nat := 4983230072969 + 3 ^ 40 * 785699 * 2
def baseEnd_785699 : Nat := 19923024037384033716007

theorem tailTrace_785699 : CollatzResearch.WordTrace tailWord_785699 prefixEnd_785699 19923024037384033716007 := by
  unfold tailWord_785699
  simp only [CollatzResearch.WordTrace]
  refine ⟨28656796780554184551160151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19104531187036123034106767 28656796780554184551160151)
  ·
    refine ⟨42985195170831276826740227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28656796780554184551160151 42985195170831276826740227)
    ·
      refine ⟨64477792756246915240110341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42985195170831276826740227 64477792756246915240110341)
      ·
        refine ⟨12089586141796296607520689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64477792756246915240110341 12089586141796296607520689)
        ·
          refine ⟨9067189606347222455640517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12089586141796296607520689 9067189606347222455640517)
          ·
            refine ⟨1700098051190104210432597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9067189606347222455640517 1700098051190104210432597)
            ·
              refine ⟨19923024037384033716007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1700098051190104210432597 19923024037384033716007)
              ·
                rfl

theorem cell21_785699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 8].length) (baseStart_785699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785699 prefixEnd_785699 := by exact prefixLift 785699
  have htrace : WordTrace (prefixWord ++ tailWord_785699) baseStart_785699 baseEnd_785699 := by
    simpa [prefixWord, tailWord_785699, baseEnd_785699] using wordTrace_append hprefix tailTrace_785699
  have hstable : (prefixWord ++ tailWord_785699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785699).length < 2 ^ (prefixWord ++ tailWord_785699).sum := by decide
  have hdescent : baseEnd_785699 < baseStart_785699 := by decide
  rcases family_descends (prefixWord ++ tailWord_785699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785716 : List Nat := [2, 5, 1, 1, 1, 1, 2, 8]
def baseStart_785716 : Nat := 118140960795 + 785716 * 2 ^ 59
def prefixEnd_785716 : Nat := 4983230072969 + 3 ^ 40 * 785716 * 2
def baseEnd_785716 : Nat := 59770365322689350553565

theorem tailTrace_785716 : CollatzResearch.WordTrace tailWord_785716 prefixEnd_785716 59770365322689350553565 := by
  unfold tailWord_785716
  simp only [CollatzResearch.WordTrace]
  refine ⟨14328708410746298227264501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19104944547661730969686001 14328708410746298227264501)
  ·
    refine ⟨1343316413507465458806047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14328708410746298227264501 1343316413507465458806047)
    ·
      refine ⟨2014974620261198188209071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1343316413507465458806047 2014974620261198188209071)
      ·
        refine ⟨3022461930391797282313607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2014974620261198188209071 3022461930391797282313607)
        ·
          refine ⟨4533692895587695923470411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3022461930391797282313607 4533692895587695923470411)
          ·
            refine ⟨6800539343381543885205617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4533692895587695923470411 6800539343381543885205617)
            ·
              refine ⟨5100404507536157913904213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6800539343381543885205617 5100404507536157913904213)
              ·
                refine ⟨59770365322689350553565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5100404507536157913904213 59770365322689350553565)
                ·
                  rfl

theorem cell21_785716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 8].length) (baseStart_785716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785716 prefixEnd_785716 := by exact prefixLift 785716
  have htrace : WordTrace (prefixWord ++ tailWord_785716) baseStart_785716 baseEnd_785716 := by
    simpa [prefixWord, tailWord_785716, baseEnd_785716] using wordTrace_append hprefix tailTrace_785716
  have hstable : (prefixWord ++ tailWord_785716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785716).length < 2 ^ (prefixWord ++ tailWord_785716).sum := by decide
  have hdescent : baseEnd_785716 < baseStart_785716 := by decide
  rcases family_descends (prefixWord ++ tailWord_785716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785744 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 8]
def baseStart_785744 : Nat := 118140960795 + 785744 * 2 ^ 59
def prefixEnd_785744 : Nat := 4983230072969 + 3 ^ 40 * 785744 * 2
def baseEnd_785744 : Nat := 179317485949546225193971

theorem tailTrace_785744 : CollatzResearch.WordTrace tailWord_785744 prefixEnd_785744 179317485949546225193971 := by
  unfold tailWord_785744
  simp only [CollatzResearch.WordTrace]
  refine ⟨14329219032695578618274143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19105625376927438157698857 14329219032695578618274143)
  ·
    refine ⟨21493828549043367927411215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14329219032695578618274143 21493828549043367927411215)
    ·
      refine ⟨32240742823565051891116823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21493828549043367927411215 32240742823565051891116823)
      ·
        refine ⟨48361114235347577836675235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32240742823565051891116823 48361114235347577836675235)
        ·
          refine ⟨72541671353021366755012853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48361114235347577836675235 72541671353021366755012853)
          ·
            refine ⟨6800781689345753133282455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72541671353021366755012853 6800781689345753133282455)
            ·
              refine ⟨10201172534018629699923683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6800781689345753133282455 10201172534018629699923683)
              ·
                refine ⟨15301758801027944549885525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10201172534018629699923683 15301758801027944549885525)
                ·
                  refine ⟨179317485949546225193971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15301758801027944549885525 179317485949546225193971)
                  ·
                    rfl

theorem cell21_785744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_785744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785744 prefixEnd_785744 := by exact prefixLift 785744
  have htrace : WordTrace (prefixWord ++ tailWord_785744) baseStart_785744 baseEnd_785744 := by
    simpa [prefixWord, tailWord_785744, baseEnd_785744] using wordTrace_append hprefix tailTrace_785744
  have hstable : (prefixWord ++ tailWord_785744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785744).length < 2 ^ (prefixWord ++ tailWord_785744).sum := by decide
  have hdescent : baseEnd_785744 < baseStart_785744 := by decide
  rcases family_descends (prefixWord ++ tailWord_785744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785775 : List Nat := [1, 1, 2, 1, 3, 1, 6, 6]
def baseStart_785775 : Nat := 118140960795 + 785775 * 2 ^ 59
def prefixEnd_785775 : Nat := 4983230072969 + 3 ^ 40 * 785775 * 2
def baseEnd_785775 : Nat := 59774853523965686725747

theorem tailTrace_785775 : CollatzResearch.WordTrace tailWord_785775 prefixEnd_785775 59774853523965686725747 := by
  unfold tailWord_785775
  simp only [CollatzResearch.WordTrace]
  refine ⟨28659568728278849530926779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19106379152185899687284519 28659568728278849530926779)
  ·
    refine ⟨42989353092418274296390169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28659568728278849530926779 42989353092418274296390169)
    ·
      refine ⟨32242014819313705722292627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42989353092418274296390169 32242014819313705722292627)
      ·
        refine ⟨48363022228970558583438941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32242014819313705722292627 48363022228970558583438941)
        ·
          refine ⟨18136133335863959468789603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48363022228970558583438941 18136133335863959468789603)
          ·
            refine ⟨27204200003795939203184405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18136133335863959468789603 27204200003795939203184405)
            ·
              refine ⟨1275196875177934650149269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27204200003795939203184405 1275196875177934650149269)
              ·
                refine ⟨59774853523965686725747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1275196875177934650149269 59774853523965686725747)
                ·
                  rfl

theorem cell21_785775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 6].length) (baseStart_785775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785775 prefixEnd_785775 := by exact prefixLift 785775
  have htrace : WordTrace (prefixWord ++ tailWord_785775) baseStart_785775 baseEnd_785775 := by
    simpa [prefixWord, tailWord_785775, baseEnd_785775] using wordTrace_append hprefix tailTrace_785775
  have hstable : (prefixWord ++ tailWord_785775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785775).length < 2 ^ (prefixWord ++ tailWord_785775).sum := by decide
  have hdescent : baseEnd_785775 < baseStart_785775 := by decide
  rcases family_descends (prefixWord ++ tailWord_785775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785865 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 9]
def baseStart_785865 : Nat := 118140960795 + 785865 * 2 ^ 59
def prefixEnd_785865 : Nat := 4983230072969 + 3 ^ 40 * 785865 * 2
def baseEnd_785865 : Nat := 179345099798076903677057

theorem tailTrace_785865 : CollatzResearch.WordTrace tailWord_785865 prefixEnd_785865 179345099798076903677057 := by
  unfold tailWord_785865
  simp only [CollatzResearch.WordTrace]
  refine ⟨28662851297952794901703049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19108567531968529934468699 28662851297952794901703049)
  ·
    refine ⟨21497138473464596176277287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28662851297952794901703049 21497138473464596176277287)
    ·
      refine ⟨32245707710196894264415931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21497138473464596176277287 32245707710196894264415931)
      ·
        refine ⟨48368561565295341396623897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32245707710196894264415931 48368561565295341396623897)
        ·
          refine ⟨36276421173971506047467923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48368561565295341396623897 36276421173971506047467923)
          ·
            refine ⟨54414631760957259071201885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36276421173971506047467923 54414631760957259071201885)
            ·
              refine ⟨20405486910358972151700707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54414631760957259071201885 20405486910358972151700707)
              ·
                refine ⟨30608230365538458227551061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20405486910358972151700707 30608230365538458227551061)
                ·
                  refine ⟨179345099798076903677057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30608230365538458227551061 179345099798076903677057)
                  ·
                    rfl

theorem cell21_785865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_785865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785865 prefixEnd_785865 := by exact prefixLift 785865
  have htrace : WordTrace (prefixWord ++ tailWord_785865) baseStart_785865 baseEnd_785865 := by
    simpa [prefixWord, tailWord_785865, baseEnd_785865] using wordTrace_append hprefix tailTrace_785865
  have hstable : (prefixWord ++ tailWord_785865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785865).length < 2 ^ (prefixWord ++ tailWord_785865).sum := by decide
  have hdescent : baseEnd_785865 < baseStart_785865 := by decide
  rcases family_descends (prefixWord ++ tailWord_785865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785882 : List Nat := [3, 1, 1, 2, 3, 2, 1, 3, 5]
def baseStart_785882 : Nat := 118140960795 + 785882 * 2 ^ 59
def prefixEnd_785882 : Nat := 4983230072969 + 3 ^ 40 * 785882 * 2
def baseEnd_785882 : Nat := 179348979429688651893689

theorem tailTrace_785882 : CollatzResearch.WordTrace tailWord_785882 prefixEnd_785882 179348979429688651893689 := by
  unfold tailWord_785882
  simp only [CollatzResearch.WordTrace]
  refine ⟨7165867834722801701267975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19108980892594137870047933 7165867834722801701267975)
  ·
    refine ⟨10748801752084202551901963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7165867834722801701267975 10748801752084202551901963)
    ·
      refine ⟨16123202628126303827852945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10748801752084202551901963 16123202628126303827852945)
      ·
        refine ⟨12092401971094727870889709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16123202628126303827852945 12092401971094727870889709)
        ·
          refine ⟨4534650739160522951583641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12092401971094727870889709 4534650739160522951583641)
          ·
            refine ⟨3400988054370392213687731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4534650739160522951583641 3400988054370392213687731)
            ·
              refine ⟨5101482081555588320531597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3400988054370392213687731 5101482081555588320531597)
              ·
                refine ⟨1913055780583345620199349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5101482081555588320531597 1913055780583345620199349)
                ·
                  refine ⟨179348979429688651893689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1913055780583345620199349 179348979429688651893689)
                  ·
                    rfl

theorem cell21_785882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_785882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785882 prefixEnd_785882 := by exact prefixLift 785882
  have htrace : WordTrace (prefixWord ++ tailWord_785882) baseStart_785882 baseEnd_785882 := by
    simpa [prefixWord, tailWord_785882, baseEnd_785882] using wordTrace_append hprefix tailTrace_785882
  have hstable : (prefixWord ++ tailWord_785882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785882).length < 2 ^ (prefixWord ++ tailWord_785882).sum := by decide
  have hdescent : baseEnd_785882 < baseStart_785882 := by decide
  rcases family_descends (prefixWord ++ tailWord_785882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785927 : List Nat := [1, 1, 4, 3, 2, 1, 9]
def baseStart_785927 : Nat := 118140960795 + 785927 * 2 ^ 59
def prefixEnd_785927 : Nat := 4983230072969 + 3 ^ 40 * 785927 * 2
def baseEnd_785927 : Nat := 19928805449197619293733

theorem tailTrace_785927 : CollatzResearch.WordTrace tailWord_785927 prefixEnd_785927 19928805449197619293733 := by
  unfold tailWord_785927
  simp only [CollatzResearch.WordTrace]
  refine ⟨28665112623728179490460035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19110075082485452993640023 28665112623728179490460035)
  ·
    refine ⟨42997668935592269235690053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28665112623728179490460035 42997668935592269235690053)
    ·
      refine ⟨8062062925423550481691885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42997668935592269235690053 8062062925423550481691885)
      ·
        refine ⟨3023273597033831430634457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8062062925423550481691885 3023273597033831430634457)
        ·
          refine ⟨2267455197775373572975843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3023273597033831430634457 2267455197775373572975843)
          ·
            refine ⟨3401182796663060359463765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2267455197775373572975843 3401182796663060359463765)
            ·
              refine ⟨19928805449197619293733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3401182796663060359463765 19928805449197619293733)
              ·
                rfl

theorem cell21_785927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 9].length) (baseStart_785927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785927 prefixEnd_785927 := by exact prefixLift 785927
  have htrace : WordTrace (prefixWord ++ tailWord_785927) baseStart_785927 baseEnd_785927 := by
    simpa [prefixWord, tailWord_785927, baseEnd_785927] using wordTrace_append hprefix tailTrace_785927
  have hstable : (prefixWord ++ tailWord_785927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785927).length < 2 ^ (prefixWord ++ tailWord_785927).sum := by decide
  have hdescent : baseEnd_785927 < baseStart_785927 := by decide
  rcases family_descends (prefixWord ++ tailWord_785927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785944 : List Nat := [2, 1, 2, 3, 4, 1, 2, 6]
def baseStart_785944 : Nat := 118140960795 + 785944 * 2 ^ 59
def prefixEnd_785944 : Nat := 4983230072969 + 3 ^ 40 * 785944 * 2
def baseEnd_785944 : Nat := 59787709558130107286743

theorem tailTrace_785944 : CollatzResearch.WordTrace tailWord_785944 prefixEnd_785944 59787709558130107286743 := by
  unfold tailWord_785944
  simp only [CollatzResearch.WordTrace]
  refine ⟨14332866332333295696914443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19110488443111060929219257 14332866332333295696914443)
  ·
    refine ⟨21499299498499943545371665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14332866332333295696914443 21499299498499943545371665)
    ·
      refine ⟨16124474623874957659028749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21499299498499943545371665 16124474623874957659028749)
      ·
        refine ⟨6046677983953109122135781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16124474623874957659028749 6046677983953109122135781)
        ·
          refine ⟨1133752121991207960400459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6046677983953109122135781 1133752121991207960400459)
          ·
            refine ⟨1700628182986811940600689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1133752121991207960400459 1700628182986811940600689)
            ·
              refine ⟨1275471137240108955450517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1700628182986811940600689 1275471137240108955450517)
              ·
                refine ⟨59787709558130107286743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1275471137240108955450517 59787709558130107286743)
                ·
                  rfl

theorem cell21_785944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 6].length) (baseStart_785944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785944 prefixEnd_785944 := by exact prefixLift 785944
  have htrace : WordTrace (prefixWord ++ tailWord_785944) baseStart_785944 baseEnd_785944 := by
    simpa [prefixWord, tailWord_785944, baseEnd_785944] using wordTrace_append hprefix tailTrace_785944
  have hstable : (prefixWord ++ tailWord_785944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785944).length < 2 ^ (prefixWord ++ tailWord_785944).sum := by decide
  have hdescent : baseEnd_785944 < baseStart_785944 := by decide
  rcases family_descends (prefixWord ++ tailWord_785944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_785989 : List Nat := [1, 3, 1, 1, 1, 4, 4, 2, 4]
def baseStart_785989 : Nat := 118140960795 + 785989 * 2 ^ 59
def prefixEnd_785989 : Nat := 4983230072969 + 3 ^ 40 * 785989 * 2
def baseEnd_785989 : Nat := 179373398287480243610137

theorem tailTrace_785989 : CollatzResearch.WordTrace tailWord_785989 prefixEnd_785989 179373398287480243610137 := by
  unfold tailWord_785989
  simp only [CollatzResearch.WordTrace]
  refine ⟨28667373949503564079217021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19111582633002376052811347 28667373949503564079217021)
  ·
    refine ⟨10750265231063836529706383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28667373949503564079217021 10750265231063836529706383)
    ·
      refine ⟨16125397846595754794559575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10750265231063836529706383 16125397846595754794559575)
      ·
        refine ⟨24188096769893632191839363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16125397846595754794559575 24188096769893632191839363)
        ·
          refine ⟨36282145154840448287759045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24188096769893632191839363 36282145154840448287759045)
          ·
            refine ⟨6802902216532584053954821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36282145154840448287759045 6802902216532584053954821)
            ·
              refine ⟨1275544165599859510116529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6802902216532584053954821 1275544165599859510116529)
              ·
                refine ⟨956658124199894632587397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1275544165599859510116529 956658124199894632587397)
                ·
                  refine ⟨179373398287480243610137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 956658124199894632587397 179373398287480243610137)
                  ·
                    rfl

theorem cell21_785989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_785989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_785989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_785989 prefixEnd_785989 := by exact prefixLift 785989
  have htrace : WordTrace (prefixWord ++ tailWord_785989) baseStart_785989 baseEnd_785989 := by
    simpa [prefixWord, tailWord_785989, baseEnd_785989] using wordTrace_append hprefix tailTrace_785989
  have hstable : (prefixWord ++ tailWord_785989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_785989).length < 2 ^ (prefixWord ++ tailWord_785989).sum := by decide
  have hdescent : baseEnd_785989 < baseStart_785989 := by decide
  rcases family_descends (prefixWord ++ tailWord_785989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786020 : List Nat := [2, 3, 1, 1, 2, 4, 3, 5]
def baseStart_786020 : Nat := 118140960795 + 786020 * 2 ^ 59
def prefixEnd_786020 : Nat := 4983230072969 + 3 ^ 40 * 786020 * 2
def baseEnd_786020 : Nat := 59793490969943692864469

theorem tailTrace_786020 : CollatzResearch.WordTrace tailWord_786020 prefixEnd_786020 59793490969943692864469 := by
  unfold tailWord_786020
  simp only [CollatzResearch.WordTrace]
  refine ⟨14334252306195628186797757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19112336408260837582397009 14334252306195628186797757)
  ·
    refine ⟨5375344614823360570049159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14334252306195628186797757 5375344614823360570049159)
    ·
      refine ⟨8063016922235040855073739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5375344614823360570049159 8063016922235040855073739)
      ·
        refine ⟨12094525383352561282610609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8063016922235040855073739 12094525383352561282610609)
        ·
          refine ⟨9070894037514420961957957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12094525383352561282610609 9070894037514420961957957)
          ·
            refine ⟨1700792632033953930367117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9070894037514420961957957 1700792632033953930367117)
            ·
              refine ⟨637797237012732723887669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1700792632033953930367117 637797237012732723887669)
              ·
                refine ⟨59793490969943692864469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 637797237012732723887669 59793490969943692864469)
                ·
                  rfl

theorem cell21_786020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 5].length) (baseStart_786020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_786020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_786020 prefixEnd_786020 := by exact prefixLift 786020
  have htrace : WordTrace (prefixWord ++ tailWord_786020) baseStart_786020 baseEnd_786020 := by
    simpa [prefixWord, tailWord_786020, baseEnd_786020] using wordTrace_append hprefix tailTrace_786020
  have hstable : (prefixWord ++ tailWord_786020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786020).length < 2 ^ (prefixWord ++ tailWord_786020).sum := by decide
  have hdescent : baseEnd_786020 < baseStart_786020 := by decide
  rcases family_descends (prefixWord ++ tailWord_786020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786048 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 6]
def baseStart_786048 : Nat := 118140960795 + 786048 * 2 ^ 59
def prefixEnd_786048 : Nat := 4983230072969 + 3 ^ 40 * 786048 * 2
def baseEnd_786048 : Nat := 179386862891309252126683

theorem tailTrace_786048 : CollatzResearch.WordTrace tailWord_786048 prefixEnd_786048 179386862891309252126683 := by
  unfold tailWord_786048
  simp only [CollatzResearch.WordTrace]
  refine ⟨14334762928144908577807399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19113017237526544770409865 14334762928144908577807399)
  ·
    refine ⟨21502144392217362866711099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14334762928144908577807399 21502144392217362866711099)
    ·
      refine ⟨32253216588326044300066649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21502144392217362866711099 32253216588326044300066649)
      ·
        refine ⟨24189912441244533225049987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32253216588326044300066649 24189912441244533225049987)
        ·
          refine ⟨36284868661866799837574981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24189912441244533225049987 36284868661866799837574981)
          ·
            refine ⟨6803412874100024969545309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36284868661866799837574981 6803412874100024969545309)
            ·
              refine ⟨2551279827787509363579491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6803412874100024969545309 2551279827787509363579491)
              ·
                refine ⟨3826919741681264045369237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2551279827787509363579491 3826919741681264045369237)
                ·
                  refine ⟨179386862891309252126683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3826919741681264045369237 179386862891309252126683)
                  ·
                    rfl

theorem cell21_786048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_786048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_786048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_786048 prefixEnd_786048 := by exact prefixLift 786048
  have htrace : WordTrace (prefixWord ++ tailWord_786048) baseStart_786048 baseEnd_786048 := by
    simpa [prefixWord, tailWord_786048, baseEnd_786048] using wordTrace_append hprefix tailTrace_786048
  have hstable : (prefixWord ++ tailWord_786048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786048).length < 2 ^ (prefixWord ++ tailWord_786048).sum := by decide
  have hdescent : baseEnd_786048 < baseStart_786048 := by decide
  rcases family_descends (prefixWord ++ tailWord_786048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786102 : List Nat := [5, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_786102 : Nat := 118140960795 + 786102 * 2 ^ 59
def prefixEnd_786102 : Nat := 4983230072969 + 3 ^ 40 * 786102 * 2
def baseEnd_786102 : Nat := 179399186427017158226573

theorem tailTrace_786102 : CollatzResearch.WordTrace tailWord_786102 prefixEnd_786102 179399186427017158226573 := by
  unfold tailWord_786102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1791968462380886523630035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19114330265396122918720373 1791968462380886523630035)
  ·
    refine ⟨2687952693571329785445053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1791968462380886523630035 2687952693571329785445053)
    ·
      refine ⟨1007982260089248669541895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2687952693571329785445053 1007982260089248669541895)
      ·
        refine ⟨1511973390133873004312843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1007982260089248669541895 1511973390133873004312843)
        ·
          refine ⟨2267960085200809506469265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1511973390133873004312843 2267960085200809506469265)
          ·
            refine ⟨1700970063900607129851949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2267960085200809506469265 1700970063900607129851949)
            ·
              refine ⟨637863773962727673694481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1700970063900607129851949 637863773962727673694481)
              ·
                refine ⟨478397830472045755270861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 637863773962727673694481 478397830472045755270861)
                ·
                  refine ⟨179399186427017158226573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 478397830472045755270861 179399186427017158226573)
                  ·
                    rfl

theorem cell21_786102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_786102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_786102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_786102 prefixEnd_786102 := by exact prefixLift 786102
  have htrace : WordTrace (prefixWord ++ tailWord_786102) baseStart_786102 baseEnd_786102 := by
    simpa [prefixWord, tailWord_786102, baseEnd_786102] using wordTrace_append hprefix tailTrace_786102
  have hstable : (prefixWord ++ tailWord_786102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786102).length < 2 ^ (prefixWord ++ tailWord_786102).sum := by decide
  have hdescent : baseEnd_786102 < baseStart_786102 := by decide
  rcases family_descends (prefixWord ++ tailWord_786102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786186 : List Nat := [3, 1, 2, 2, 1, 4, 1, 2, 5]
def baseStart_786186 : Nat := 118140960795 + 786186 * 2 ^ 59
def prefixEnd_786186 : Nat := 4983230072969 + 3 ^ 40 * 786186 * 2
def baseEnd_786186 : Nat := 179418356371451678826401

theorem tailTrace_786186 : CollatzResearch.WordTrace tailWord_786186 prefixEnd_786186 179418356371451678826401 := by
  unfold tailWord_786186
  simp only [CollatzResearch.WordTrace]
  refine ⟨7168639782447466681034603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19116372753193244482758941 7168639782447466681034603)
  ·
    refine ⟨10752959673671200021551905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7168639782447466681034603 10752959673671200021551905)
    ·
      refine ⟨8064719755253400016163929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10752959673671200021551905 8064719755253400016163929)
      ·
        refine ⟨6048539816440050012122947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8064719755253400016163929 6048539816440050012122947)
        ·
          refine ⟨9072809724660075018184421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6048539816440050012122947 9072809724660075018184421)
          ·
            refine ⟨1701151823373764065909579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9072809724660075018184421 1701151823373764065909579)
            ·
              refine ⟨2551727735060646098864369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1701151823373764065909579 2551727735060646098864369)
              ·
                refine ⟨1913795801295484574148277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2551727735060646098864369 1913795801295484574148277)
                ·
                  refine ⟨179418356371451678826401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1913795801295484574148277 179418356371451678826401)
                  ·
                    rfl

theorem cell21_786186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_786186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_786186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_786186 prefixEnd_786186 := by exact prefixLift 786186
  have htrace : WordTrace (prefixWord ++ tailWord_786186) baseStart_786186 baseEnd_786186 := by
    simpa [prefixWord, tailWord_786186, baseEnd_786186] using wordTrace_append hprefix tailTrace_786186
  have hstable : (prefixWord ++ tailWord_786186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786186).length < 2 ^ (prefixWord ++ tailWord_786186).sum := by decide
  have hdescent : baseEnd_786186 < baseStart_786186 := by decide
  rcases family_descends (prefixWord ++ tailWord_786186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786234 : List Nat := [3, 1, 1, 1, 5, 2, 3, 1, 4]
def baseStart_786234 : Nat := 118140960795 + 786234 * 2 ^ 59
def prefixEnd_786234 : Nat := 4983230072969 + 3 ^ 40 * 786234 * 2
def baseEnd_786234 : Nat := 179429310625414262026303

theorem tailTrace_786234 : CollatzResearch.WordTrace tailWord_786234 prefixEnd_786234 179429310625414262026303 := by
  unfold tailWord_786234
  simp only [CollatzResearch.WordTrace]
  refine ⟨7169077458403992730471439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19117539889077313947923837 7169077458403992730471439)
  ·
    refine ⟨10753616187605989095707159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7169077458403992730471439 10753616187605989095707159)
    ·
      refine ⟨16130424281408983643560739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10753616187605989095707159 16130424281408983643560739)
      ·
        refine ⟨24195636422113475465341109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16130424281408983643560739 24195636422113475465341109)
        ·
          refine ⟨2268340914573138324875729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24195636422113475465341109 2268340914573138324875729)
          ·
            refine ⟨1701255685929853743656797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2268340914573138324875729 1701255685929853743656797)
            ·
              refine ⟨637970882223695153871299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1701255685929853743656797 637970882223695153871299)
              ·
                refine ⟨956956323335542730806949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 637970882223695153871299 956956323335542730806949)
                ·
                  refine ⟨179429310625414262026303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 956956323335542730806949 179429310625414262026303)
                  ·
                    rfl

theorem cell21_786234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_786234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_786234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_786234 prefixEnd_786234 := by exact prefixLift 786234
  have htrace : WordTrace (prefixWord ++ tailWord_786234) baseStart_786234 baseEnd_786234 := by
    simpa [prefixWord, tailWord_786234, baseEnd_786234] using wordTrace_append hprefix tailTrace_786234
  have hstable : (prefixWord ++ tailWord_786234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786234).length < 2 ^ (prefixWord ++ tailWord_786234).sum := by decide
  have hdescent : baseEnd_786234 < baseStart_786234 := by decide
  rcases family_descends (prefixWord ++ tailWord_786234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786245 : List Nat := [1, 3, 1, 1, 1, 2, 3, 4, 5]
def baseStart_786245 : Nat := 118140960795 + 786245 * 2 ^ 59
def prefixEnd_786245 : Nat := 4983230072969 + 3 ^ 40 * 786245 * 2
def baseEnd_786245 : Nat := 179431820975280687342947

theorem tailTrace_786245 : CollatzResearch.WordTrace tailWord_786245 prefixEnd_786245 179431820975280687342947 := by
  unfold tailWord_786245
  simp only [CollatzResearch.WordTrace]
  refine ⟨28676711036576119800536189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19117807357717413200357459 28676711036576119800536189)
  ·
    refine ⟨10753766638716044925201071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28676711036576119800536189 10753766638716044925201071)
    ·
      refine ⟨16130649958074067387801607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10753766638716044925201071 16130649958074067387801607)
      ·
        refine ⟨24195974937111101081702411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16130649958074067387801607 24195974937111101081702411)
        ·
          refine ⟨36293962405666651622553617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24195974937111101081702411 36293962405666651622553617)
          ·
            refine ⟨27220471804249988716915213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36293962405666651622553617 27220471804249988716915213)
            ·
              refine ⟨10207676926593745768843205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27220471804249988716915213 10207676926593745768843205)
              ·
                refine ⟨1913939423736327331658101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10207676926593745768843205 1913939423736327331658101)
                ·
                  refine ⟨179431820975280687342947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1913939423736327331658101 179431820975280687342947)
                  ·
                    rfl

theorem cell21_786245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_786245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_786245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_786245 prefixEnd_786245 := by exact prefixLift 786245
  have htrace : WordTrace (prefixWord ++ tailWord_786245) baseStart_786245 baseEnd_786245 := by
    simpa [prefixWord, tailWord_786245, baseEnd_786245] using wordTrace_append hprefix tailTrace_786245
  have hstable : (prefixWord ++ tailWord_786245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786245).length < 2 ^ (prefixWord ++ tailWord_786245).sum := by decide
  have hdescent : baseEnd_786245 < baseStart_786245 := by decide
  rcases family_descends (prefixWord ++ tailWord_786245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786248 : List Nat := [2, 1, 3, 1, 1, 6, 2, 5]
def baseStart_786248 : Nat := 118140960795 + 786248 * 2 ^ 59
def prefixEnd_786248 : Nat := 4983230072969 + 3 ^ 40 * 786248 * 2
def baseEnd_786248 : Nat := 59810835205384449597647

theorem tailTrace_786248 : CollatzResearch.WordTrace tailWord_786248 prefixEnd_786248 59810835205384449597647 := by
  unfold tailWord_786248
  simp only [CollatzResearch.WordTrace]
  refine ⟨14338410227782625656447699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19117880303710167541930265 14338410227782625656447699)
  ·
    refine ⟨21507615341673938484671549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14338410227782625656447699 21507615341673938484671549)
    ·
      refine ⟨8065355753127726931751831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21507615341673938484671549 8065355753127726931751831)
      ·
        refine ⟨12098033629691590397627747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8065355753127726931751831 12098033629691590397627747)
        ·
          refine ⟨18147050444537385596441621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12098033629691590397627747 18147050444537385596441621)
          ·
            refine ⟨850642989587689949833201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18147050444537385596441621 850642989587689949833201)
            ·
              refine ⟨637982242190767462374901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 850642989587689949833201 637982242190767462374901)
              ·
                refine ⟨59810835205384449597647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 637982242190767462374901 59810835205384449597647)
                ·
                  rfl

theorem cell21_786248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 5].length) (baseStart_786248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_786248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_786248 prefixEnd_786248 := by exact prefixLift 786248
  have htrace : WordTrace (prefixWord ++ tailWord_786248) baseStart_786248 baseEnd_786248 := by
    simpa [prefixWord, tailWord_786248, baseEnd_786248] using wordTrace_append hprefix tailTrace_786248
  have hstable : (prefixWord ++ tailWord_786248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786248).length < 2 ^ (prefixWord ++ tailWord_786248).sum := by decide
  have hdescent : baseEnd_786248 < baseStart_786248 := by decide
  rcases family_descends (prefixWord ++ tailWord_786248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786293 : List Nat := [1, 3, 4, 1, 1, 1, 3, 3, 4]
def baseStart_786293 : Nat := 118140960795 + 786293 * 2 ^ 59
def prefixEnd_786293 : Nat := 4983230072969 + 3 ^ 40 * 786293 * 2
def baseEnd_786293 : Nat := 179442775229243270542849

theorem tailTrace_786293 : CollatzResearch.WordTrace tailWord_786293 prefixEnd_786293 179442775229243270542849 := by
  unfold tailWord_786293
  simp only [CollatzResearch.WordTrace]
  refine ⟨28678461740402223998283533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19118974493601482665522355 28678461740402223998283533)
  ·
    refine ⟨10754423152650833999356325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28678461740402223998283533 10754423152650833999356325)
    ·
      refine ⟨2016454341122031374879311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10754423152650833999356325 2016454341122031374879311)
      ·
        refine ⟨3024681511683047062318967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2016454341122031374879311 3024681511683047062318967)
        ·
          refine ⟨4537022267524570593478451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3024681511683047062318967 4537022267524570593478451)
          ·
            refine ⟨6805533401286855890217677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4537022267524570593478451 6805533401286855890217677)
            ·
              refine ⟨2552075025482570958831629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6805533401286855890217677 2552075025482570958831629)
              ·
                refine ⟨957028134555964109561861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2552075025482570958831629 957028134555964109561861)
                ·
                  refine ⟨179442775229243270542849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 957028134555964109561861 179442775229243270542849)
                  ·
                    rfl

theorem cell21_786293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_786293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_786293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_786293 prefixEnd_786293 := by exact prefixLift 786293
  have htrace : WordTrace (prefixWord ++ tailWord_786293) baseStart_786293 baseEnd_786293 := by
    simpa [prefixWord, tailWord_786293, baseEnd_786293] using wordTrace_append hprefix tailTrace_786293
  have hstable : (prefixWord ++ tailWord_786293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786293).length < 2 ^ (prefixWord ++ tailWord_786293).sum := by decide
  have hdescent : baseEnd_786293 < baseStart_786293 := by decide
  rcases family_descends (prefixWord ++ tailWord_786293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786414 : List Nat := [4, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_786414 : Nat := 118140960795 + 786414 * 2 ^ 59
def prefixEnd_786414 : Nat := 4983230072969 + 3 ^ 40 * 786414 * 2
def baseEnd_786414 : Nat := 179470389077773949025935

theorem tailTrace_786414 : CollatzResearch.WordTrace tailWord_786414 prefixEnd_786414 179470389077773949025935 := by
  unfold tailWord_786414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3585359371620482707929787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19121916648642574442292197 3585359371620482707929787)
  ·
    refine ⟨5378039057430724061894681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3585359371620482707929787 5378039057430724061894681)
    ·
      refine ⟨4033529293073043046421011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5378039057430724061894681 4033529293073043046421011)
      ·
        refine ⟨6050293939609564569631517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4033529293073043046421011 6050293939609564569631517)
        ·
          refine ⟨2268860227353586713611819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6050293939609564569631517 2268860227353586713611819)
          ·
            refine ⟨3403290341030380070417729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2268860227353586713611819 3403290341030380070417729)
            ·
              refine ⟨2552467755772785052813297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3403290341030380070417729 2552467755772785052813297)
              ·
                refine ⟨1914350816829588789609973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2552467755772785052813297 1914350816829588789609973)
                ·
                  refine ⟨179470389077773949025935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1914350816829588789609973 179470389077773949025935)
                  ·
                    rfl

theorem cell21_786414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_786414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_786414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_786414 prefixEnd_786414 := by exact prefixLift 786414
  have htrace : WordTrace (prefixWord ++ tailWord_786414) baseStart_786414 baseEnd_786414 := by
    simpa [prefixWord, tailWord_786414, baseEnd_786414] using wordTrace_append hprefix tailTrace_786414
  have hstable : (prefixWord ++ tailWord_786414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786414).length < 2 ^ (prefixWord ++ tailWord_786414).sum := by decide
  have hdescent : baseEnd_786414 < baseStart_786414 := by decide
  rcases family_descends (prefixWord ++ tailWord_786414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786417 : List Nat := [1, 2, 2, 2, 6, 1, 2, 5]
def baseStart_786417 : Nat := 118140960795 + 786417 * 2 ^ 59
def prefixEnd_786417 : Nat := 4983230072969 + 3 ^ 40 * 786417 * 2
def baseEnd_786417 : Nat := 59823691239548870158643

theorem tailTrace_786417 : CollatzResearch.WordTrace tailWord_786417 prefixEnd_786417 59823691239548870158643 := by
  unfold tailWord_786417
  simp only [CollatzResearch.WordTrace]
  refine ⟨28682984391952993175797505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19121989594635328783865003 28682984391952993175797505)
  ·
    refine ⟨21512238293964744881848129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28682984391952993175797505 21512238293964744881848129)
    ·
      refine ⟨16134178720473558661386097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21512238293964744881848129 16134178720473558661386097)
      ·
        refine ⟨12100634040355168996039573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16134178720473558661386097 12100634040355168996039573)
        ·
          refine ⟨567217220641648546689355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12100634040355168996039573 567217220641648546689355)
          ·
            refine ⟨850825830962472820034033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567217220641648546689355 850825830962472820034033)
            ·
              refine ⟨638119373221854615025525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 850825830962472820034033 638119373221854615025525)
              ·
                refine ⟨59823691239548870158643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 638119373221854615025525 59823691239548870158643)
                ·
                  rfl

theorem cell21_786417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 5].length) (baseStart_786417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_786417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_786417 prefixEnd_786417 := by exact prefixLift 786417
  have htrace : WordTrace (prefixWord ++ tailWord_786417) baseStart_786417 baseEnd_786417 := by
    simpa [prefixWord, tailWord_786417, baseEnd_786417] using wordTrace_append hprefix tailTrace_786417
  have hstable : (prefixWord ++ tailWord_786417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786417).length < 2 ^ (prefixWord ++ tailWord_786417).sum := by decide
  have hdescent : baseEnd_786417 < baseStart_786417 := by decide
  rcases family_descends (prefixWord ++ tailWord_786417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786487 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 8]
def baseStart_786487 : Nat := 118140960795 + 786487 * 2 ^ 59
def prefixEnd_786487 : Nat := 4983230072969 + 3 ^ 40 * 786487 * 2
def baseEnd_786487 : Nat := 179487048672342044309119

theorem tailTrace_786487 : CollatzResearch.WordTrace tailWord_786487 prefixEnd_786487 179487048672342044309119 := by
  unfold tailWord_786487
  simp only [CollatzResearch.WordTrace]
  refine ⟨28685537501699395130845715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19123691667799596753897143 28685537501699395130845715)
  ·
    refine ⟨43028306252549092696268573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28685537501699395130845715 43028306252549092696268573)
    ·
      refine ⟨16135614844705909761100715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43028306252549092696268573 16135614844705909761100715)
      ·
        refine ⟨24203422267058864641651073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16135614844705909761100715 24203422267058864641651073)
        ·
          refine ⟨18152566700294148481238305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24203422267058864641651073 18152566700294148481238305)
          ·
            refine ⟨13614425025220611360928729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18152566700294148481238305 13614425025220611360928729)
            ·
              refine ⟨10210818768915458520696547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13614425025220611360928729 10210818768915458520696547)
              ·
                refine ⟨15316228153373187781044821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10210818768915458520696547 15316228153373187781044821)
                ·
                  refine ⟨179487048672342044309119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15316228153373187781044821 179487048672342044309119)
                  ·
                    rfl

theorem cell21_786487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 8].length) (baseStart_786487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_786487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_786487 prefixEnd_786487 := by exact prefixLift 786487
  have htrace : WordTrace (prefixWord ++ tailWord_786487) baseStart_786487 baseEnd_786487 := by
    simpa [prefixWord, tailWord_786487, baseEnd_786487] using wordTrace_append hprefix tailTrace_786487
  have hstable : (prefixWord ++ tailWord_786487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786487).length < 2 ^ (prefixWord ++ tailWord_786487).sum := by decide
  have hdescent : baseEnd_786487 < baseStart_786487 := by decide
  rcases family_descends (prefixWord ++ tailWord_786487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786490 : List Nat := [3, 1, 1, 1, 3, 1, 1, 7, 3]
def baseStart_786490 : Nat := 118140960795 + 786490 * 2 ^ 59
def prefixEnd_786490 : Nat := 4983230072969 + 3 ^ 40 * 786490 * 2
def baseEnd_786490 : Nat := 179487733313214705759113

theorem tailTrace_786490 : CollatzResearch.WordTrace tailWord_786490 prefixEnd_786490 179487733313214705759113 := by
  unfold tailWord_786490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7171411730172131660801231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19123764613792351095469949 7171411730172131660801231)
  ·
    refine ⟨10757117595258197491201847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7171411730172131660801231 10757117595258197491201847)
    ·
      refine ⟨16135676392887296236802771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10757117595258197491201847 16135676392887296236802771)
      ·
        refine ⟨24203514589330944355204157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16135676392887296236802771 24203514589330944355204157)
        ·
          refine ⟨9076317970999104133201559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24203514589330944355204157 9076317970999104133201559)
          ·
            refine ⟨13614476956498656199802339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9076317970999104133201559 13614476956498656199802339)
            ·
              refine ⟨20421715434747984299703509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13614476956498656199802339 20421715434747984299703509)
              ·
                refine ⟨478633955501905882024301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20421715434747984299703509 478633955501905882024301)
                ·
                  refine ⟨179487733313214705759113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 478633955501905882024301 179487733313214705759113)
                  ·
                    rfl

theorem cell21_786490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_786490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_786490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_786490 prefixEnd_786490 := by exact prefixLift 786490
  have htrace : WordTrace (prefixWord ++ tailWord_786490) baseStart_786490 baseEnd_786490 := by
    simpa [prefixWord, tailWord_786490, baseEnd_786490] using wordTrace_append hprefix tailTrace_786490
  have hstable : (prefixWord ++ tailWord_786490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786490).length < 2 ^ (prefixWord ++ tailWord_786490).sum := by decide
  have hdescent : baseEnd_786490 < baseStart_786490 := by decide
  rcases family_descends (prefixWord ++ tailWord_786490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786535 : List Nat := [1, 1, 5, 1, 1, 2, 5, 5]
def baseStart_786535 : Nat := 118140960795 + 786535 * 2 ^ 59
def prefixEnd_786535 : Nat := 4983230072969 + 3 ^ 40 * 786535 * 2
def baseEnd_786535 : Nat := 59832667642101542503007

theorem tailTrace_786535 : CollatzResearch.WordTrace tailWord_786535 prefixEnd_786535 59832667642101542503007 := by
  unfold tailWord_786535
  simp only [CollatzResearch.WordTrace]
  refine ⟨28687288205525499328593059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19124858803683666219062039 28687288205525499328593059)
  ·
    refine ⟨43030932308288248992889589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28687288205525499328593059 43030932308288248992889589)
    ·
      refine ⟨4034149903902023343083399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43030932308288248992889589 4034149903902023343083399)
      ·
        refine ⟨6051224855853035014625099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4034149903902023343083399 6051224855853035014625099)
        ·
          refine ⟨9076837283779552521937649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6051224855853035014625099 9076837283779552521937649)
          ·
            refine ⟨6807627962834664391453237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9076837283779552521937649 6807627962834664391453237)
            ·
              refine ⟨638215121515749786698741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6807627962834664391453237 638215121515749786698741)
              ·
                refine ⟨59832667642101542503007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 638215121515749786698741 59832667642101542503007)
                ·
                  rfl

theorem cell21_786535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 5].length) (baseStart_786535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_786535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_786535 prefixEnd_786535 := by exact prefixLift 786535
  have htrace : WordTrace (prefixWord ++ tailWord_786535) baseStart_786535 baseEnd_786535 := by
    simpa [prefixWord, tailWord_786535, baseEnd_786535] using wordTrace_append hprefix tailTrace_786535
  have hstable : (prefixWord ++ tailWord_786535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786535).length < 2 ^ (prefixWord ++ tailWord_786535).sum := by decide
  have hdescent : baseEnd_786535 < baseStart_786535 := by decide
  rcases family_descends (prefixWord ++ tailWord_786535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786732 : List Nat := [2, 2, 1, 1, 1, 3, 5, 2, 4]
def baseStart_786732 : Nat := 118140960795 + 786732 * 2 ^ 59
def prefixEnd_786732 : Nat := 4983230072969 + 3 ^ 40 * 786732 * 2
def baseEnd_786732 : Nat := 179542961010276062725285

theorem tailTrace_786732 : CollatzResearch.WordTrace tailWord_786732 prefixEnd_786732 179542961010276062725285 := by
  unfold tailWord_786732
  simp only [CollatzResearch.WordTrace]
  refine ⟨14347236692905900986757225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19129648923874534649009633 14347236692905900986757225)
  ·
    refine ⟨10760427519679425740067919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14347236692905900986757225 10760427519679425740067919)
    ·
      refine ⟨16140641279519138610101879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10760427519679425740067919 16140641279519138610101879)
      ·
        refine ⟨24210961919278707915152819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16140641279519138610101879 24210961919278707915152819)
        ·
          refine ⟨36316442878918061872729229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24210961919278707915152819 36316442878918061872729229)
          ·
            refine ⟨13618666079594273202273461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36316442878918061872729229 13618666079594273202273461)
            ·
              refine ⟨1276749944961963112713137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13618666079594273202273461 1276749944961963112713137)
              ·
                refine ⟨957562458721472334534853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1276749944961963112713137 957562458721472334534853)
                ·
                  refine ⟨179542961010276062725285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 957562458721472334534853 179542961010276062725285)
                  ·
                    rfl

theorem cell21_786732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_786732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_786732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_786732 prefixEnd_786732 := by exact prefixLift 786732
  have htrace : WordTrace (prefixWord ++ tailWord_786732) baseStart_786732 baseEnd_786732 := by
    simpa [prefixWord, tailWord_786732, baseEnd_786732] using wordTrace_append hprefix tailTrace_786732
  have hstable : (prefixWord ++ tailWord_786732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786732).length < 2 ^ (prefixWord ++ tailWord_786732).sum := by decide
  have hdescent : baseEnd_786732 < baseStart_786732 := by decide
  rcases family_descends (prefixWord ++ tailWord_786732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786780 : List Nat := [2, 2, 4, 3, 1, 2, 7]
def baseStart_786780 : Nat := 118140960795 + 786780 * 2 ^ 59
def prefixEnd_786780 : Nat := 4983230072969 + 3 ^ 40 * 786780 * 2
def baseEnd_786780 : Nat := 19950435029359849547243

theorem tailTrace_786780 : CollatzResearch.WordTrace tailWord_786780 prefixEnd_786780 19950435029359849547243 := by
  unfold tailWord_786780
  simp only [CollatzResearch.WordTrace]
  refine ⟨14348112044818953085630897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19130816059758604114174529 14348112044818953085630897)
  ·
    refine ⟨10761084033614214814223173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14348112044818953085630897 10761084033614214814223173)
    ·
      refine ⟨2017703256302665277666845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10761084033614214814223173 2017703256302665277666845)
      ·
        refine ⟨756638721113499479125067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2017703256302665277666845 756638721113499479125067)
        ·
          refine ⟨1134958081670249218687601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 756638721113499479125067 1134958081670249218687601)
          ·
            refine ⟨851218561252686914015701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1134958081670249218687601 851218561252686914015701)
            ·
              refine ⟨19950435029359849547243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 851218561252686914015701 19950435029359849547243)
              ·
                rfl

theorem cell21_786780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 7].length) (baseStart_786780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_786780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_786780 prefixEnd_786780 := by exact prefixLift 786780
  have htrace : WordTrace (prefixWord ++ tailWord_786780) baseStart_786780 baseEnd_786780 := by
    simpa [prefixWord, tailWord_786780, baseEnd_786780] using wordTrace_append hprefix tailTrace_786780
  have hstable : (prefixWord ++ tailWord_786780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786780).length < 2 ^ (prefixWord ++ tailWord_786780).sum := by decide
  have hdescent : baseEnd_786780 < baseStart_786780 := by decide
  rcases family_descends (prefixWord ++ tailWord_786780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786794 : List Nat := [3, 1, 3, 3, 1, 1, 3, 1, 5]
def baseStart_786794 : Nat := 118140960795 + 786794 * 2 ^ 59
def prefixEnd_786794 : Nat := 4983230072969 + 3 ^ 40 * 786794 * 2
def baseEnd_786794 : Nat := 179557110254977732691825

theorem tailTrace_786794 : CollatzResearch.WordTrace tailWord_786794 prefixEnd_786794 179557110254977732691825 := by
  unfold tailWord_786794
  simp only [CollatzResearch.WordTrace]
  refine ⟨7174183677896796640567859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19131156474391457708180957 7174183677896796640567859)
  ·
    refine ⟨10761275516845194960851789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7174183677896796640567859 10761275516845194960851789)
    ·
      refine ⟨4035478318816948110319421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10761275516845194960851789 4035478318816948110319421)
      ·
        refine ⟨1513304369556355541369783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4035478318816948110319421 1513304369556355541369783)
        ·
          refine ⟨2269956554334533312054675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1513304369556355541369783 2269956554334533312054675)
          ·
            refine ⟨3404934831501799968082013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2269956554334533312054675 3404934831501799968082013)
            ·
              refine ⟨1276850561813174988030755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3404934831501799968082013 1276850561813174988030755)
              ·
                refine ⟨1915275842719762482046133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1276850561813174988030755 1915275842719762482046133)
                ·
                  refine ⟨179557110254977732691825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1915275842719762482046133 179557110254977732691825)
                  ·
                    rfl

theorem cell21_786794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_786794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_786794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_786794 prefixEnd_786794 := by exact prefixLift 786794
  have htrace : WordTrace (prefixWord ++ tailWord_786794) baseStart_786794 baseEnd_786794 := by
    simpa [prefixWord, tailWord_786794, baseEnd_786794] using wordTrace_append hprefix tailTrace_786794
  have hstable : (prefixWord ++ tailWord_786794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786794).length < 2 ^ (prefixWord ++ tailWord_786794).sum := by decide
  have hdescent : baseEnd_786794 < baseStart_786794 := by decide
  rcases family_descends (prefixWord ++ tailWord_786794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786845 : List Nat := [1, 4, 2, 1, 5, 1, 2, 2, 3]
def baseStart_786845 : Nat := 118140960795 + 786845 * 2 ^ 59
def prefixEnd_786845 : Nat := 4983230072969 + 3 ^ 40 * 786845 * 2
def baseEnd_786845 : Nat := 179568749149812977341721

theorem tailTrace_786845 : CollatzResearch.WordTrace tailWord_786845 prefixEnd_786845 179568749149812977341721 := by
  unfold tailWord_786845
  simp only [CollatzResearch.WordTrace]
  refine ⟨28698594834402422272377989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19132396556268281514918659 28698594834402422272377989)
  ·
    refine ⟨5380986531450454176070873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28698594834402422272377989 5380986531450454176070873)
    ·
      refine ⟨4035739898587840632053155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5380986531450454176070873 4035739898587840632053155)
      ·
        refine ⟨6053609847881760948079733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4035739898587840632053155 6053609847881760948079733)
        ·
          refine ⟨567525923238915088882475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6053609847881760948079733 567525923238915088882475)
          ·
            refine ⟨851288884858372633323713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567525923238915088882475 851288884858372633323713)
            ·
              refine ⟨638466663643779474992785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 851288884858372633323713 638466663643779474992785)
              ·
                refine ⟨478849997732834606244589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 638466663643779474992785 478849997732834606244589)
                ·
                  refine ⟨179568749149812977341721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 478849997732834606244589 179568749149812977341721)
                  ·
                    rfl

theorem cell21_786845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_786845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_786845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_786845 prefixEnd_786845 := by exact prefixLift 786845
  have htrace : WordTrace (prefixWord ++ tailWord_786845) baseStart_786845 baseEnd_786845 := by
    simpa [prefixWord, tailWord_786845, baseEnd_786845] using wordTrace_append hprefix tailTrace_786845
  have hstable : (prefixWord ++ tailWord_786845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786845).length < 2 ^ (prefixWord ++ tailWord_786845).sum := by decide
  have hdescent : baseEnd_786845 < baseStart_786845 := by decide
  rcases family_descends (prefixWord ++ tailWord_786845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786856 : List Nat := [2, 1, 6, 1, 1, 3, 1, 6]
def baseStart_786856 : Nat := 118140960795 + 786856 * 2 ^ 59
def prefixEnd_786856 : Nat := 4983230072969 + 3 ^ 40 * 786856 * 2
def baseEnd_786856 : Nat := 59857086499893134219455

theorem tailTrace_786856 : CollatzResearch.WordTrace tailWord_786856 prefixEnd_786856 59857086499893134219455 := by
  unfold tailWord_786856
  simp only [CollatzResearch.WordTrace]
  refine ⟨14349498018681285575514211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19132664024908380767352281 14349498018681285575514211)
  ·
    refine ⟨21524247028021928363271317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14349498018681285575514211 21524247028021928363271317)
    ·
      refine ⟨1008949079438527892028343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21524247028021928363271317 1008949079438527892028343)
      ·
        refine ⟨1513423619157791838042515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1008949079438527892028343 1513423619157791838042515)
        ·
          refine ⟨2270135428736687757063773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1513423619157791838042515 2270135428736687757063773)
          ·
            refine ⟨851300785776257908898915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2270135428736687757063773 851300785776257908898915)
            ·
              refine ⟨1276951178664386863348373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851300785776257908898915 1276951178664386863348373)
              ·
                refine ⟨59857086499893134219455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1276951178664386863348373 59857086499893134219455)
                ·
                  rfl

theorem cell21_786856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 6].length) (baseStart_786856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_786856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_786856 prefixEnd_786856 := by exact prefixLift 786856
  have htrace : WordTrace (prefixWord ++ tailWord_786856) baseStart_786856 baseEnd_786856 := by
    simpa [prefixWord, tailWord_786856, baseEnd_786856] using wordTrace_append hprefix tailTrace_786856
  have hstable : (prefixWord ++ tailWord_786856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786856).length < 2 ^ (prefixWord ++ tailWord_786856).sum := by decide
  have hdescent : baseEnd_786856 < baseStart_786856 := by decide
  rcases family_descends (prefixWord ++ tailWord_786856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786901 : List Nat := [1, 3, 2, 3, 1, 4, 1, 2, 4]
def baseStart_786901 : Nat := 118140960795 + 786901 * 2 ^ 59
def prefixEnd_786901 : Nat := 4983230072969 + 3 ^ 40 * 786901 * 2
def baseEnd_786901 : Nat := 179581529112769324408273

theorem tailTrace_786901 : CollatzResearch.WordTrace tailWord_786901 prefixEnd_786901 179581529112769324408273 := by
  unfold tailWord_786901
  simp only [CollatzResearch.WordTrace]
  refine ⟨28700637322199543836416557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19133758214799695890944371 28700637322199543836416557)
  ·
    refine ⟨10762738995824828938656209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28700637322199543836416557 10762738995824828938656209)
    ·
      refine ⟨8072054246868621703992157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10762738995824828938656209 8072054246868621703992157)
      ·
        refine ⟨3027020342575733138997059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8072054246868621703992157 3027020342575733138997059)
        ·
          refine ⟨4540530513863599708495589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3027020342575733138997059 4540530513863599708495589)
          ·
            refine ⟨851349471349424945342923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4540530513863599708495589 851349471349424945342923)
            ·
              refine ⟨1277024207024137418014385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851349471349424945342923 1277024207024137418014385)
              ·
                refine ⟨957768155268103063510789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1277024207024137418014385 957768155268103063510789)
                ·
                  refine ⟨179581529112769324408273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 957768155268103063510789 179581529112769324408273)
                  ·
                    rfl

theorem cell21_786901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_786901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_786901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_786901 prefixEnd_786901 := by exact prefixLift 786901
  have htrace : WordTrace (prefixWord ++ tailWord_786901) baseStart_786901 baseEnd_786901 := by
    simpa [prefixWord, tailWord_786901, baseEnd_786901] using wordTrace_append hprefix tailTrace_786901
  have hstable : (prefixWord ++ tailWord_786901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786901).length < 2 ^ (prefixWord ++ tailWord_786901).sum := by decide
  have hdescent : baseEnd_786901 < baseStart_786901 := by decide
  rcases family_descends (prefixWord ++ tailWord_786901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_786988 : List Nat := [2, 2, 1, 1, 1, 2, 1, 6, 5]
def baseStart_786988 : Nat := 118140960795 + 786988 * 2 ^ 59
def prefixEnd_786988 : Nat := 4983230072969 + 3 ^ 40 * 786988 * 2
def baseEnd_786988 : Nat := 179601383698076506458095

theorem tailTrace_786988 : CollatzResearch.WordTrace tailWord_786988 prefixEnd_786988 179601383698076506458095 := by
  unfold tailWord_786988
  simp only [CollatzResearch.WordTrace]
  refine ⟨14351905236442178847416809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19135873648589571796555745 14351905236442178847416809)
  ·
    refine ⟨10763928927331634135562607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14351905236442178847416809 10763928927331634135562607)
    ·
      refine ⟨16145893390997451203343911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10763928927331634135562607 16145893390997451203343911)
      ·
        refine ⟨24218840086496176805015867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16145893390997451203343911 24218840086496176805015867)
        ·
          refine ⟨36328260129744265207523801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24218840086496176805015867 36328260129744265207523801)
          ·
            refine ⟨27246195097308198905642851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36328260129744265207523801 27246195097308198905642851)
            ·
              refine ⟨40869292645962298358464277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27246195097308198905642851 40869292645962298358464277)
              ·
                refine ⟨1915748092779482735553013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40869292645962298358464277 1915748092779482735553013)
                ·
                  refine ⟨179601383698076506458095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1915748092779482735553013 179601383698076506458095)
                  ·
                    rfl

theorem cell21_786988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_786988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_786988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_786988 prefixEnd_786988 := by exact prefixLift 786988
  have htrace : WordTrace (prefixWord ++ tailWord_786988) baseStart_786988 baseEnd_786988 := by
    simpa [prefixWord, tailWord_786988, baseEnd_786988] using wordTrace_append hprefix tailTrace_786988
  have hstable : (prefixWord ++ tailWord_786988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_786988).length < 2 ^ (prefixWord ++ tailWord_786988).sum := by decide
  have hdescent : baseEnd_786988 < baseStart_786988 := by decide
  rcases family_descends (prefixWord ++ tailWord_786988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787019 : List Nat := [1, 1, 1, 1, 3, 1, 5, 4, 4]
def baseStart_787019 : Nat := 118140960795 + 787019 * 2 ^ 59
def prefixEnd_787019 : Nat := 4983230072969 + 3 ^ 40 * 787019 * 2
def baseEnd_787019 : Nat := 179608458320427341441365

theorem tailTrace_787019 : CollatzResearch.WordTrace tailWord_787019 prefixEnd_787019 179608458320427341441365 := by
  unfold tailWord_787019
  simp only [CollatzResearch.WordTrace]
  refine ⟨28704941135772049989212111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19136627423848033326141407 28704941135772049989212111)
  ·
    refine ⟨43057411703658074983818167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28704941135772049989212111 43057411703658074983818167)
    ·
      refine ⟨64586117555487112475727251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43057411703658074983818167 64586117555487112475727251)
      ·
        refine ⟨96879176333230668713590877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64586117555487112475727251 96879176333230668713590877)
        ·
          refine ⟨36329691124961500767596579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96879176333230668713590877 36329691124961500767596579)
          ·
            refine ⟨54494536687442251151394869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36329691124961500767596579 54494536687442251151394869)
            ·
              refine ⟨5108862814447711045443269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54494536687442251151394869 5108862814447711045443269)
              ·
                refine ⟨957911777708945821020613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5108862814447711045443269 957911777708945821020613)
                ·
                  refine ⟨179608458320427341441365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 957911777708945821020613 179608458320427341441365)
                  ·
                    rfl

theorem cell21_787019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 4].length) (baseStart_787019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_787019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_787019 prefixEnd_787019 := by exact prefixLift 787019
  have htrace : WordTrace (prefixWord ++ tailWord_787019) baseStart_787019 baseEnd_787019 := by
    simpa [prefixWord, tailWord_787019, baseEnd_787019] using wordTrace_append hprefix tailTrace_787019
  have hstable : (prefixWord ++ tailWord_787019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787019).length < 2 ^ (prefixWord ++ tailWord_787019).sum := by decide
  have hdescent : baseEnd_787019 < baseStart_787019 := by decide
  rcases family_descends (prefixWord ++ tailWord_787019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787270 : List Nat := [6, 1, 1, 2, 3, 1, 2, 5]
def baseStart_787270 : Nat := 118140960795 + 787270 * 2 ^ 59
def prefixEnd_787270 : Nat := 4983230072969 + 3 ^ 40 * 787270 * 2
def baseEnd_787270 : Nat := 59888579980035560919173

theorem tailTrace_787270 : CollatzResearch.WordTrace tailWord_787270 prefixEnd_787270 59888579980035560919173 := by
  unfold tailWord_787270
  simp only [CollatzResearch.WordTrace]
  refine ⟨897315495558209995518727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19142730571908479904399509 897315495558209995518727)
  ·
    refine ⟨1345973243337314993278091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 897315495558209995518727 1345973243337314993278091)
    ·
      refine ⟨2018959865005972489917137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1345973243337314993278091 2018959865005972489917137)
      ·
        refine ⟨1514219898754479367437853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2018959865005972489917137 1514219898754479367437853)
        ·
          refine ⟨567832462032929762789195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1514219898754479367437853 567832462032929762789195)
          ·
            refine ⟨851748693049394644183793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567832462032929762789195 851748693049394644183793)
            ·
              refine ⟨638811519787045983137845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 851748693049394644183793 638811519787045983137845)
              ·
                refine ⟨59888579980035560919173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 638811519787045983137845 59888579980035560919173)
                ·
                  rfl

theorem cell21_787270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_787270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_787270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_787270 prefixEnd_787270 := by exact prefixLift 787270
  have htrace : WordTrace (prefixWord ++ tailWord_787270) baseStart_787270 baseEnd_787270 := by
    simpa [prefixWord, tailWord_787270, baseEnd_787270] using wordTrace_append hprefix tailTrace_787270
  have hstable : (prefixWord ++ tailWord_787270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787270).length < 2 ^ (prefixWord ++ tailWord_787270).sum := by decide
  have hdescent : baseEnd_787270 < baseStart_787270 := by decide
  rcases family_descends (prefixWord ++ tailWord_787270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787284 : List Nat := [2, 4, 1, 1, 5, 1, 1, 3, 3]
def baseStart_787284 : Nat := 118140960795 + 787284 * 2 ^ 59
def prefixEnd_787284 : Nat := 4983230072969 + 3 ^ 40 * 787284 * 2
def baseEnd_787284 : Nat := 179668934930845769524157

theorem tailTrace_787284 : CollatzResearch.WordTrace tailWord_787284 prefixEnd_787284 179668934930845769524157 := by
  unfold tailWord_787284
  simp only [CollatzResearch.WordTrace]
  refine ⟨14357303239906000123804453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19143070986541333498405937 14357303239906000123804453)
  ·
    refine ⟨2691994357482375023213335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14357303239906000123804453 2691994357482375023213335)
    ·
      refine ⟨4037991536223562534820003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2691994357482375023213335 4037991536223562534820003)
      ·
        refine ⟨6056987304335343802230005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4037991536223562534820003 6056987304335343802230005)
        ·
          refine ⟨567842559781438481459063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6056987304335343802230005 567842559781438481459063)
          ·
            refine ⟨851763839672157722188595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567842559781438481459063 851763839672157722188595)
            ·
              refine ⟨1277645759508236583282893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851763839672157722188595 1277645759508236583282893)
              ·
                refine ⟨479117159815588718731085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1277645759508236583282893 479117159815588718731085)
                ·
                  refine ⟨179668934930845769524157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479117159815588718731085 179668934930845769524157)
                  ·
                    rfl

theorem cell21_787284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_787284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_787284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_787284 prefixEnd_787284 := by exact prefixLift 787284
  have htrace : WordTrace (prefixWord ++ tailWord_787284) baseStart_787284 baseEnd_787284 := by
    simpa [prefixWord, tailWord_787284, baseEnd_787284] using wordTrace_append hprefix tailTrace_787284
  have hstable : (prefixWord ++ tailWord_787284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787284).length < 2 ^ (prefixWord ++ tailWord_787284).sum := by decide
  have hdescent : baseEnd_787284 < baseStart_787284 := by decide
  rcases family_descends (prefixWord ++ tailWord_787284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787337 : List Nat := [1, 2, 1, 1, 5, 2, 2, 7]
def baseStart_787337 : Nat := 118140960795 + 787337 * 2 ^ 59
def prefixEnd_787337 : Nat := 4983230072969 + 3 ^ 40 * 787337 * 2
def baseEnd_787337 : Nat := 59893676750976485046905

theorem tailTrace_787337 : CollatzResearch.WordTrace tailWord_787337 prefixEnd_787337 59893676750976485046905 := by
  unfold tailWord_787337
  simp only [CollatzResearch.WordTrace]
  refine ⟨28716539548619990299288265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19144359699079993532858843 28716539548619990299288265)
  ·
    refine ⟨21537404661464992724466199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28716539548619990299288265 21537404661464992724466199)
    ·
      refine ⟨32306106992197489086699299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21537404661464992724466199 32306106992197489086699299)
      ·
        refine ⟨48459160488296233630048949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32306106992197489086699299 48459160488296233630048949)
        ·
          refine ⟨4543046295777771902817089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48459160488296233630048949 4543046295777771902817089)
          ·
            refine ⟨3407284721833328927112817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4543046295777771902817089 3407284721833328927112817)
            ·
              refine ⟨2555463541374996695334613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3407284721833328927112817 2555463541374996695334613)
              ·
                refine ⟨59893676750976485046905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2555463541374996695334613 59893676750976485046905)
                ·
                  rfl

theorem cell21_787337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 7].length) (baseStart_787337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_787337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_787337 prefixEnd_787337 := by exact prefixLift 787337
  have htrace : WordTrace (prefixWord ++ tailWord_787337) baseStart_787337 baseEnd_787337 := by
    simpa [prefixWord, tailWord_787337, baseEnd_787337] using wordTrace_append hprefix tailTrace_787337
  have hstable : (prefixWord ++ tailWord_787337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787337).length < 2 ^ (prefixWord ++ tailWord_787337).sum := by decide
  have hdescent : baseEnd_787337 < baseStart_787337 := by decide
  rcases family_descends (prefixWord ++ tailWord_787337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787354 : List Nat := [3, 1, 1, 4, 4, 8]
def baseStart_787354 : Nat := 118140960795 + 787354 * 2 ^ 59
def prefixEnd_787354 : Nat := 4983230072969 + 3 ^ 40 * 787354 * 2
def baseEnd_787354 : Nat := 6654996662390414939161

theorem tailTrace_787354 : CollatzResearch.WordTrace tailWord_787354 prefixEnd_787354 6654996662390414939161 := by
  unfold tailWord_787354
  simp only [CollatzResearch.WordTrace]
  refine ⟨7179289897389600550664279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19144773059705601468438077 7179289897389600550664279)
  ·
    refine ⟨10768934846084400825996419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7179289897389600550664279 10768934846084400825996419)
    ·
      refine ⟨16153402269126601238994629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10768934846084400825996419 16153402269126601238994629)
      ·
        refine ⟨3028762925461237732311493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16153402269126601238994629 3028762925461237732311493)
        ·
          refine ⟨567893048523982074808405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3028762925461237732311493 567893048523982074808405)
          ·
            refine ⟨6654996662390414939161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 567893048523982074808405 6654996662390414939161)
            ·
              rfl

theorem cell21_787354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 8].length) (baseStart_787354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_787354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_787354 prefixEnd_787354 := by exact prefixLift 787354
  have htrace : WordTrace (prefixWord ++ tailWord_787354) baseStart_787354 baseEnd_787354 := by
    simpa [prefixWord, tailWord_787354, baseEnd_787354] using wordTrace_append hprefix tailTrace_787354
  have hstable : (prefixWord ++ tailWord_787354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787354).length < 2 ^ (prefixWord ++ tailWord_787354).sum := by decide
  have hdescent : baseEnd_787354 < baseStart_787354 := by decide
  rcases family_descends (prefixWord ++ tailWord_787354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787416 : List Nat := [2, 1, 2, 2, 2, 5, 1, 2, 4]
def baseStart_787416 : Nat := 118140960795 + 787416 * 2 ^ 59
def prefixEnd_787416 : Nat := 4983230072969 + 3 ^ 40 * 787416 * 2
def baseEnd_787416 : Nat := 179699059129242873323887

theorem tailTrace_787416 : CollatzResearch.WordTrace tailWord_787416 prefixEnd_787416 179699059129242873323887 := by
  unfold tailWord_787416
  simp only [CollatzResearch.WordTrace]
  refine ⟨14359710457666893395707051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19146280610222524527609401 14359710457666893395707051)
  ·
    refine ⟨21539565686500340093560577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14359710457666893395707051 21539565686500340093560577)
    ·
      refine ⟨16154674264875255070170433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21539565686500340093560577 16154674264875255070170433)
      ·
        refine ⟨12116005698656441302627825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16154674264875255070170433 12116005698656441302627825)
        ·
          refine ⟨9087004273992330976970869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12116005698656441302627825 9087004273992330976970869)
          ·
            refine ⟨851906650686781029091019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9087004273992330976970869 851906650686781029091019)
            ·
              refine ⟨1277859976030171543636529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851906650686781029091019 1277859976030171543636529)
              ·
                refine ⟨958394982022628657727397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1277859976030171543636529 958394982022628657727397)
                ·
                  refine ⟨179699059129242873323887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 958394982022628657727397 179699059129242873323887)
                  ·
                    rfl

theorem cell21_787416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 4].length) (baseStart_787416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_787416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_787416 prefixEnd_787416 := by exact prefixLift 787416
  have htrace : WordTrace (prefixWord ++ tailWord_787416) baseStart_787416 baseEnd_787416 := by
    simpa [prefixWord, tailWord_787416, baseEnd_787416] using wordTrace_append hprefix tailTrace_787416
  have hstable : (prefixWord ++ tailWord_787416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787416).length < 2 ^ (prefixWord ++ tailWord_787416).sum := by decide
  have hdescent : baseEnd_787416 < baseStart_787416 := by decide
  rcases family_descends (prefixWord ++ tailWord_787416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787489 : List Nat := [1, 2, 3, 2, 3, 1, 1, 8]
def baseStart_787489 : Nat := 118140960795 + 787489 * 2 ^ 59
def prefixEnd_787489 : Nat := 4983230072969 + 3 ^ 40 * 787489 * 2
def baseEnd_787489 : Nat := 59905239574603656202357

theorem tailTrace_787489 : CollatzResearch.WordTrace tailWord_787489 prefixEnd_787489 59905239574603656202357 := by
  unfold tailWord_787489
  simp only [CollatzResearch.WordTrace]
  refine ⟨28722083444069320258821521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19148055629379546839214347 28722083444069320258821521)
  ·
    refine ⟨21541562583051990194116141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28722083444069320258821521 21541562583051990194116141)
    ·
      refine ⟨8078085968644496322793553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21541562583051990194116141 8078085968644496322793553)
      ·
        refine ⟨6058564476483372242095165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8078085968644496322793553 6058564476483372242095165)
        ·
          refine ⟨2271961678681264590785687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6058564476483372242095165 2271961678681264590785687)
          ·
            refine ⟨3407942518021896886178531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271961678681264590785687 3407942518021896886178531)
            ·
              refine ⟨5111913777032845329267797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3407942518021896886178531 5111913777032845329267797)
              ·
                refine ⟨59905239574603656202357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5111913777032845329267797 59905239574603656202357)
                ·
                  rfl

theorem cell21_787489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 8].length) (baseStart_787489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_787489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_787489 prefixEnd_787489 := by exact prefixLift 787489
  have htrace : WordTrace (prefixWord ++ tailWord_787489) baseStart_787489 baseEnd_787489 := by
    simpa [prefixWord, tailWord_787489, baseEnd_787489] using wordTrace_append hprefix tailTrace_787489
  have hstable : (prefixWord ++ tailWord_787489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787489).length < 2 ^ (prefixWord ++ tailWord_787489).sum := by decide
  have hdescent : baseEnd_787489 < baseStart_787489 := by decide
  rcases family_descends (prefixWord ++ tailWord_787489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787492 : List Nat := [2, 3, 1, 4, 1, 2, 1, 3, 4]
def baseStart_787492 : Nat := 118140960795 + 787492 * 2 ^ 59
def prefixEnd_787492 : Nat := 4983230072969 + 3 ^ 40 * 787492 * 2
def baseEnd_787492 : Nat := 179716403364683630057065

theorem tailTrace_787492 : CollatzResearch.WordTrace tailWord_787492 prefixEnd_787492 179716403364683630057065 := by
  unfold tailWord_787492
  simp only [CollatzResearch.WordTrace]
  refine ⟨14361096431529225885590365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19148128575372301180787153 14361096431529225885590365)
  ·
    refine ⟨5385411161823459707096387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14361096431529225885590365 5385411161823459707096387)
    ·
      refine ⟨8078116742735189560644581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5385411161823459707096387 8078116742735189560644581)
      ·
        refine ⟨1514646889262848042620859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8078116742735189560644581 1514646889262848042620859)
        ·
          refine ⟨2271970333894272063931289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1514646889262848042620859 2271970333894272063931289)
          ·
            refine ⟨1703977750420704047948467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2271970333894272063931289 1703977750420704047948467)
            ·
              refine ⟨2555966625631056071922701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1703977750420704047948467 2555966625631056071922701)
              ·
                refine ⟨958487484611646026971013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2555966625631056071922701 958487484611646026971013)
                ·
                  refine ⟨179716403364683630057065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 958487484611646026971013 179716403364683630057065)
                  ·
                    rfl

theorem cell21_787492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_787492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_787492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_787492 prefixEnd_787492 := by exact prefixLift 787492
  have htrace : WordTrace (prefixWord ++ tailWord_787492) baseStart_787492 baseEnd_787492 := by
    simpa [prefixWord, tailWord_787492, baseEnd_787492] using wordTrace_append hprefix tailTrace_787492
  have hstable : (prefixWord ++ tailWord_787492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787492).length < 2 ^ (prefixWord ++ tailWord_787492).sum := by decide
  have hdescent : baseEnd_787492 < baseStart_787492 := by decide
  rcases family_descends (prefixWord ++ tailWord_787492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787641 : List Nat := [1, 2, 1, 4, 1, 5, 7]
def baseStart_787641 : Nat := 118140960795 + 787641 * 2 ^ 59
def prefixEnd_787641 : Nat := 4983230072969 + 3 ^ 40 * 787641 * 2
def baseEnd_787641 : Nat := 19972267466076942452603

theorem tailTrace_787641 : CollatzResearch.WordTrace tailWord_787641 prefixEnd_787641 19972267466076942452603 := by
  unfold tailWord_787641
  simp only [CollatzResearch.WordTrace]
  refine ⟨28727627339518650218354777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19151751559679100145569851 28727627339518650218354777)
  ·
    refine ⟨21545720504638987663766083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28727627339518650218354777 21545720504638987663766083)
    ·
      refine ⟨32318580756958481495649125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21545720504638987663766083 32318580756958481495649125)
      ·
        refine ⟨6059733891929715280434211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32318580756958481495649125 6059733891929715280434211)
        ·
          refine ⟨9089600837894572920651317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6059733891929715280434211 9089600837894572920651317)
          ·
            refine ⟨852150078552616211311061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9089600837894572920651317 852150078552616211311061)
            ·
              refine ⟨19972267466076942452603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 852150078552616211311061 19972267466076942452603)
              ·
                rfl

theorem cell21_787641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 7].length) (baseStart_787641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_787641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_787641 prefixEnd_787641 := by exact prefixLift 787641
  have htrace : WordTrace (prefixWord ++ tailWord_787641) baseStart_787641 baseEnd_787641 := by
    simpa [prefixWord, tailWord_787641, baseEnd_787641] using wordTrace_append hprefix tailTrace_787641
  have hstable : (prefixWord ++ tailWord_787641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787641).length < 2 ^ (prefixWord ++ tailWord_787641).sum := by decide
  have hdescent : baseEnd_787641 < baseStart_787641 := by decide
  rcases family_descends (prefixWord ++ tailWord_787641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787765 : List Nat := [1, 3, 3, 1, 2, 2, 2, 4, 3]
def baseStart_787765 : Nat := 118140960795 + 787765 * 2 ^ 59
def prefixEnd_787765 : Nat := 4983230072969 + 3 ^ 40 * 787765 * 2
def baseEnd_787765 : Nat := 179778705684095822006507

theorem tailTrace_787765 : CollatzResearch.WordTrace tailWord_787765 prefixEnd_787765 179778705684095822006507 := by
  unfold tailWord_787765
  simp only [CollatzResearch.WordTrace]
  refine ⟨28732149991069419395868749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19154766660712946263912499 28732149991069419395868749)
  ·
    refine ⟨10774556246651032273450781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28732149991069419395868749 10774556246651032273450781)
    ·
      refine ⟨4040458592494137102544043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10774556246651032273450781 4040458592494137102544043)
      ·
        refine ⟨6060687888741205653816065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4040458592494137102544043 6060687888741205653816065)
        ·
          refine ⟨4545515916555904240362049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6060687888741205653816065 4545515916555904240362049)
          ·
            refine ⟨3409136937416928180271537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4545515916555904240362049 3409136937416928180271537)
            ·
              refine ⟨2556852703062696135203653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3409136937416928180271537 2556852703062696135203653)
              ·
                refine ⟨479409881824255525350685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2556852703062696135203653 479409881824255525350685)
                ·
                  refine ⟨179778705684095822006507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479409881824255525350685 179778705684095822006507)
                  ·
                    rfl

theorem cell21_787765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_787765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_787765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_787765 prefixEnd_787765 := by exact prefixLift 787765
  have htrace : WordTrace (prefixWord ++ tailWord_787765) baseStart_787765 baseEnd_787765 := by
    simpa [prefixWord, tailWord_787765, baseEnd_787765] using wordTrace_append hprefix tailTrace_787765
  have hstable : (prefixWord ++ tailWord_787765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787765).length < 2 ^ (prefixWord ++ tailWord_787765).sum := by decide
  have hdescent : baseEnd_787765 < baseStart_787765 := by decide
  rcases family_descends (prefixWord ++ tailWord_787765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787776 : List Nat := [2, 1, 1, 2, 2, 1, 4, 8]
def baseStart_787776 : Nat := 118140960795 + 787776 * 2 ^ 59
def prefixEnd_787776 : Nat := 4983230072969 + 3 ^ 40 * 787776 * 2
def baseEnd_787776 : Nat := 59927072011320749107717

theorem tailTrace_787776 : CollatzResearch.WordTrace tailWord_787776 prefixEnd_787776 59927072011320749107717 := by
  unfold tailWord_787776
  simp only [CollatzResearch.WordTrace]
  refine ⟨14366275597014784137259591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19155034129353045516346121 14366275597014784137259591)
  ·
    refine ⟨21549413395522176205889387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14366275597014784137259591 21549413395522176205889387)
    ·
      refine ⟨32324120093283264308834081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21549413395522176205889387 32324120093283264308834081)
      ·
        refine ⟨24243090069962448231625561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32324120093283264308834081 24243090069962448231625561)
        ·
          refine ⟨18182317552471836173719171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24243090069962448231625561 18182317552471836173719171)
          ·
            refine ⟨27273476328707754260578757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18182317552471836173719171 27273476328707754260578757)
            ·
              refine ⟨5113776811632703923858517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27273476328707754260578757 5113776811632703923858517)
              ·
                refine ⟨59927072011320749107717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5113776811632703923858517 59927072011320749107717)
                ·
                  rfl

theorem cell21_787776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 8].length) (baseStart_787776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_787776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_787776 prefixEnd_787776 := by exact prefixLift 787776
  have htrace : WordTrace (prefixWord ++ tailWord_787776) baseStart_787776 baseEnd_787776 := by
    simpa [prefixWord, tailWord_787776, baseEnd_787776] using wordTrace_append hprefix tailTrace_787776
  have hstable : (prefixWord ++ tailWord_787776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787776).length < 2 ^ (prefixWord ++ tailWord_787776).sum := by decide
  have hdescent : baseEnd_787776 < baseStart_787776 := by decide
  rcases family_descends (prefixWord ++ tailWord_787776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_787852 : List Nat := [2, 2, 1, 2, 1, 3, 1, 9]
def baseStart_787852 : Nat := 118140960795 + 787852 * 2 ^ 59
def prefixEnd_787852 : Nat := 4983230072969 + 3 ^ 40 * 787852 * 2
def baseEnd_787852 : Nat := 59932853423134334685443

theorem tailTrace_787852 : CollatzResearch.WordTrace tailWord_787852 prefixEnd_787852 59932853423134334685443 := by
  unfold tailWord_787852
  simp only [CollatzResearch.WordTrace]
  refine ⟨14367661570877116627142905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19156882094502822169523873 14367661570877116627142905)
  ·
    refine ⟨10775746178157837470357179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14367661570877116627142905 10775746178157837470357179)
    ·
      refine ⟨16163619267236756205535769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10775746178157837470357179 16163619267236756205535769)
      ·
        refine ⟨12122714450427567154151827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16163619267236756205535769 12122714450427567154151827)
        ·
          refine ⟨18184071675641350731227741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12122714450427567154151827 18184071675641350731227741)
          ·
            refine ⟨6819026878365506524210403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18184071675641350731227741 6819026878365506524210403)
            ·
              refine ⟨10228540317548259786315605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6819026878365506524210403 10228540317548259786315605)
              ·
                refine ⟨59932853423134334685443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10228540317548259786315605 59932853423134334685443)
                ·
                  rfl

theorem cell21_787852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 9].length) (baseStart_787852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_787852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_787852 prefixEnd_787852 := by exact prefixLift 787852
  have htrace : WordTrace (prefixWord ++ tailWord_787852) baseStart_787852 baseEnd_787852 := by
    simpa [prefixWord, tailWord_787852, baseEnd_787852] using wordTrace_append hprefix tailTrace_787852
  have hstable : (prefixWord ++ tailWord_787852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_787852).length < 2 ^ (prefixWord ++ tailWord_787852).sum := by decide
  have hdescent : baseEnd_787852 < baseStart_787852 := by decide
  rcases family_descends (prefixWord ++ tailWord_787852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788038 : List Nat := [6, 1, 1, 1, 3, 9]
def baseStart_788038 : Nat := 118140960795 + 788038 * 2 ^ 59
def prefixEnd_788038 : Nat := 4983230072969 + 3 ^ 40 * 788038 * 2
def baseEnd_788038 : Nat := 6660778074204000516887

theorem tailTrace_788038 : CollatzResearch.WordTrace tailWord_788038 prefixEnd_788038 6660778074204000516887 := by
  unfold tailWord_788038
  simp only [CollatzResearch.WordTrace]
  refine ⟨898190847471262094392399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19161404746053591347037845 898190847471262094392399)
  ·
    refine ⟨1347286271206893141588599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 898190847471262094392399 1347286271206893141588599)
    ·
      refine ⟨2020929406810339712382899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1347286271206893141588599 2020929406810339712382899)
      ·
        refine ⟨3031394110215509568574349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2020929406810339712382899 3031394110215509568574349)
        ·
          refine ⟨1136772791330816088215381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3031394110215509568574349 1136772791330816088215381)
          ·
            refine ⟨6660778074204000516887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1136772791330816088215381 6660778074204000516887)
            ·
              rfl

theorem cell21_788038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 9].length) (baseStart_788038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_788038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_788038 prefixEnd_788038 := by exact prefixLift 788038
  have htrace : WordTrace (prefixWord ++ tailWord_788038) baseStart_788038 baseEnd_788038 := by
    simpa [prefixWord, tailWord_788038, baseEnd_788038] using wordTrace_append hprefix tailTrace_788038
  have hstable : (prefixWord ++ tailWord_788038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788038).length < 2 ^ (prefixWord ++ tailWord_788038).sum := by decide
  have hdescent : baseEnd_788038 < baseStart_788038 := by decide
  rcases family_descends (prefixWord ++ tailWord_788038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788086 : List Nat := [5, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_788086 : Nat := 118140960795 + 788086 * 2 ^ 59
def prefixEnd_788086 : Nat := 4983230072969 + 3 ^ 40 * 788086 * 2
def baseEnd_788086 : Nat := 179851962257470597155851

theorem tailTrace_788086 : CollatzResearch.WordTrace tailWord_788086 prefixEnd_788086 179851962257470597155851 := by
  unfold tailWord_788086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1796491113931655701144007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19162571881937660812202741 1796491113931655701144007)
  ·
    refine ⟨2694736670897483551716011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1796491113931655701144007 2694736670897483551716011)
    ·
      refine ⟨4042105006346225327574017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2694736670897483551716011 4042105006346225327574017)
      ·
        refine ⟨3031578754759668995680513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4042105006346225327574017 3031578754759668995680513)
        ·
          refine ⟨2273684066069751746760385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3031578754759668995680513 2273684066069751746760385)
          ·
            refine ⟨1705263049552313810070289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2273684066069751746760385 1705263049552313810070289)
            ·
              refine ⟨1278947287164235357552717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1705263049552313810070289 1278947287164235357552717)
              ·
                refine ⟨479605232686588259082269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1278947287164235357552717 479605232686588259082269)
                ·
                  refine ⟨179851962257470597155851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479605232686588259082269 179851962257470597155851)
                  ·
                    rfl

theorem cell21_788086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_788086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_788086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_788086 prefixEnd_788086 := by exact prefixLift 788086
  have htrace : WordTrace (prefixWord ++ tailWord_788086) baseStart_788086 baseEnd_788086 := by
    simpa [prefixWord, tailWord_788086, baseEnd_788086] using wordTrace_append hprefix tailTrace_788086
  have hstable : (prefixWord ++ tailWord_788086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788086).length < 2 ^ (prefixWord ++ tailWord_788086).sum := by decide
  have hdescent : baseEnd_788086 < baseStart_788086 := by decide
  rcases family_descends (prefixWord ++ tailWord_788086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788100 : List Nat := [2, 3, 2, 1, 4, 2, 1, 2, 4]
def baseStart_788100 : Nat := 118140960795 + 788100 * 2 ^ 59
def prefixEnd_788100 : Nat := 4983230072969 + 3 ^ 40 * 788100 * 2
def baseEnd_788100 : Nat := 179855157248209683922489

theorem tailTrace_788100 : CollatzResearch.WordTrace tailWord_788100 prefixEnd_788100 179855157248209683922489 := by
  unfold tailWord_788100
  simp only [CollatzResearch.WordTrace]
  refine ⟨14372184222427885804656877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19162912296570514406209169 14372184222427885804656877)
  ·
    refine ⟨5389569083410457176746329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14372184222427885804656877 5389569083410457176746329)
    ·
      refine ⟨4042176812557842882559747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5389569083410457176746329 4042176812557842882559747)
      ·
        refine ⟨6063265218836764323839621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4042176812557842882559747 6063265218836764323839621)
        ·
          refine ⟨1136862228531893310719929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6063265218836764323839621 1136862228531893310719929)
          ·
            refine ⟨852646671398919983039947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1136862228531893310719929 852646671398919983039947)
            ·
              refine ⟨1278970007098379974559921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 852646671398919983039947 1278970007098379974559921)
              ·
                refine ⟨959227505323784980919941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1278970007098379974559921 959227505323784980919941)
                ·
                  refine ⟨179855157248209683922489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 959227505323784980919941 179855157248209683922489)
                  ·
                    rfl

theorem cell21_788100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_788100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_788100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_788100 prefixEnd_788100 := by exact prefixLift 788100
  have htrace : WordTrace (prefixWord ++ tailWord_788100) baseStart_788100 baseEnd_788100 := by
    simpa [prefixWord, tailWord_788100, baseEnd_788100] using wordTrace_append hprefix tailTrace_788100
  have hstable : (prefixWord ++ tailWord_788100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788100).length < 2 ^ (prefixWord ++ tailWord_788100).sum := by decide
  have hdescent : baseEnd_788100 < baseStart_788100 := by decide
  rcases family_descends (prefixWord ++ tailWord_788100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788156 : List Nat := [2, 2, 2, 3, 1, 2, 9]
def baseStart_788156 : Nat := 118140960795 + 788156 * 2 ^ 59
def prefixEnd_788156 : Nat := 4983230072969 + 3 ^ 40 * 788156 * 2
def baseEnd_788156 : Nat := 19985326356796225665449

theorem tailTrace_788156 : CollatzResearch.WordTrace tailWord_788156 prefixEnd_788156 19985326356796225665449 := by
  unfold tailWord_788156
  simp only [CollatzResearch.WordTrace]
  refine ⟨14373205466326446586676161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19164273955101928782234881 14373205466326446586676161)
  ·
    refine ⟨10779904099744834940007121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14373205466326446586676161 10779904099744834940007121)
    ·
      refine ⟨8084928074808626205005341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10779904099744834940007121 8084928074808626205005341)
      ·
        refine ⟨3031848028053234826877003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8084928074808626205005341 3031848028053234826877003)
        ·
          refine ⟨4547772042079852240315505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3031848028053234826877003 4547772042079852240315505)
          ·
            refine ⟨3410829031559889180236629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4547772042079852240315505 3410829031559889180236629)
            ·
              refine ⟨19985326356796225665449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3410829031559889180236629 19985326356796225665449)
              ·
                rfl

theorem cell21_788156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 9].length) (baseStart_788156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_788156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_788156 prefixEnd_788156 := by exact prefixLift 788156
  have htrace : WordTrace (prefixWord ++ tailWord_788156) baseStart_788156 baseEnd_788156 := by
    simpa [prefixWord, tailWord_788156, baseEnd_788156] using wordTrace_append hprefix tailTrace_788156
  have hstable : (prefixWord ++ tailWord_788156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788156).length < 2 ^ (prefixWord ++ tailWord_788156).sum := by decide
  have hdescent : baseEnd_788156 < baseStart_788156 := by decide
  rcases family_descends (prefixWord ++ tailWord_788156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788280 : List Nat := [2, 1, 2, 1, 3, 3, 2, 4, 3]
def baseStart_788280 : Nat := 118140960795 + 788280 * 2 ^ 59
def prefixEnd_788280 : Nat := 4983230072969 + 3 ^ 40 * 788280 * 2
def baseEnd_788280 : Nat := 179896235700569370922121

theorem tailTrace_788280 : CollatzResearch.WordTrace tailWord_788280 prefixEnd_788280 179896235700569370922121 := by
  unfold tailWord_788280
  simp only [CollatzResearch.WordTrace]
  refine ⟨14375466792101831175433147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19167289056135774900577529 14375466792101831175433147)
  ·
    refine ⟨21563200188152746763149721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14375466792101831175433147 21563200188152746763149721)
    ·
      refine ⟨16172400141114560072362291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21563200188152746763149721 16172400141114560072362291)
      ·
        refine ⟨24258600211671840108543437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16172400141114560072362291 24258600211671840108543437)
        ·
          refine ⟨9096975079376940040703789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24258600211671840108543437 9096975079376940040703789)
          ·
            refine ⟨3411365654766352515263921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9096975079376940040703789 3411365654766352515263921)
            ·
              refine ⟨2558524241074764386447941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3411365654766352515263921 2558524241074764386447941)
              ·
                refine ⟨479723295201518322458989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2558524241074764386447941 479723295201518322458989)
                ·
                  refine ⟨179896235700569370922121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479723295201518322458989 179896235700569370922121)
                  ·
                    rfl

theorem cell21_788280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 3].length) (baseStart_788280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_788280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_788280 prefixEnd_788280 := by exact prefixLift 788280
  have htrace : WordTrace (prefixWord ++ tailWord_788280) baseStart_788280 baseEnd_788280 := by
    simpa [prefixWord, tailWord_788280, baseEnd_788280] using wordTrace_append hprefix tailTrace_788280
  have hstable : (prefixWord ++ tailWord_788280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788280).length < 2 ^ (prefixWord ++ tailWord_788280).sum := by decide
  have hdescent : baseEnd_788280 < baseStart_788280 := by decide
  rcases family_descends (prefixWord ++ tailWord_788280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788342 : List Nat := [5, 1, 1, 3, 2, 1, 2, 6]
def baseStart_788342 : Nat := 118140960795 + 788342 * 2 ^ 59
def prefixEnd_788342 : Nat := 4983230072969 + 3 ^ 40 * 788342 * 2
def baseEnd_788342 : Nat := 59970128315090346962887

theorem tailTrace_788342 : CollatzResearch.WordTrace tailWord_788342 prefixEnd_788342 59970128315090346962887 := by
  unfold tailWord_788342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1797074681873690433726455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19168796606652697959748853 1797074681873690433726455)
  ·
    refine ⟨2695612022810535650589683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1797074681873690433726455 2695612022810535650589683)
    ·
      refine ⟨4043418034215803475884525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2695612022810535650589683 4043418034215803475884525)
      ·
        refine ⟨1516281762830926303456697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4043418034215803475884525 1516281762830926303456697)
        ·
          refine ⟨1137211322123194727592523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1516281762830926303456697 1137211322123194727592523)
          ·
            refine ⟨1705816983184792091388785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137211322123194727592523 1705816983184792091388785)
            ·
              refine ⟨1279362737388594068541589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1705816983184792091388785 1279362737388594068541589)
              ·
                refine ⟨59970128315090346962887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1279362737388594068541589 59970128315090346962887)
                ·
                  rfl

theorem cell21_788342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_788342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_788342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_788342 prefixEnd_788342 := by exact prefixLift 788342
  have htrace : WordTrace (prefixWord ++ tailWord_788342) baseStart_788342 baseEnd_788342 := by
    simpa [prefixWord, tailWord_788342, baseEnd_788342] using wordTrace_append hprefix tailTrace_788342
  have hstable : (prefixWord ++ tailWord_788342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788342).length < 2 ^ (prefixWord ++ tailWord_788342).sum := by decide
  have hdescent : baseEnd_788342 < baseStart_788342 := by decide
  rcases family_descends (prefixWord ++ tailWord_788342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788401 : List Nat := [1, 2, 2, 4, 2, 3, 1, 6]
def baseStart_788401 : Nat := 118140960795 + 788401 * 2 ^ 59
def prefixEnd_788401 : Nat := 4983230072969 + 3 ^ 40 * 788401 * 2
def baseEnd_788401 : Nat := 59974616516366683135069

theorem tailTrace_788401 : CollatzResearch.WordTrace tailWord_788401 prefixEnd_788401 59974616516366683135069 := by
  unfold tailWord_788401
  simp only [CollatzResearch.WordTrace]
  refine ⟨28755346816765300016021057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19170231211176866677347371 28755346816765300016021057)
  ·
    refine ⟨21566510112573975012015793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28755346816765300016021057 21566510112573975012015793)
    ·
      refine ⟨16174882584430481259011845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21566510112573975012015793 16174882584430481259011845)
      ·
        refine ⟨3032790484580715236064721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16174882584430481259011845 3032790484580715236064721)
        ·
          refine ⟨2274592863435536427048541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3032790484580715236064721 2274592863435536427048541)
          ·
            refine ⟨852972323788326160143203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2274592863435536427048541 852972323788326160143203)
            ·
              refine ⟨1279458485682489240214805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 852972323788326160143203 1279458485682489240214805)
              ·
                refine ⟨59974616516366683135069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1279458485682489240214805 59974616516366683135069)
                ·
                  rfl

theorem cell21_788401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 6].length) (baseStart_788401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_788401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_788401 prefixEnd_788401 := by exact prefixLift 788401
  have htrace : WordTrace (prefixWord ++ tailWord_788401) baseStart_788401 baseEnd_788401 := by
    simpa [prefixWord, tailWord_788401, baseEnd_788401] using wordTrace_append hprefix tailTrace_788401
  have hstable : (prefixWord ++ tailWord_788401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788401).length < 2 ^ (prefixWord ++ tailWord_788401).sum := by decide
  have hdescent : baseEnd_788401 < baseStart_788401 := by decide
  rcases family_descends (prefixWord ++ tailWord_788401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788505 : List Nat := [1, 2, 1, 2, 1, 1, 3, 6, 4]
def baseStart_788505 : Nat := 118140960795 + 788505 * 2 ^ 59
def prefixEnd_788505 : Nat := 4983230072969 + 3 ^ 40 * 788505 * 2
def baseEnd_788505 : Nat := 179947583766018979671661

theorem tailTrace_788505 : CollatzResearch.WordTrace tailWord_788505 prefixEnd_788505 179947583766018979671661 := by
  unfold tailWord_788505
  simp only [CollatzResearch.WordTrace]
  refine ⟨28759140008388525777806969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19172760005592350518537979 28759140008388525777806969)
  ·
    refine ⟨21569355006291394333355227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28759140008388525777806969 21569355006291394333355227)
    ·
      refine ⟨32354032509437091500032841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21569355006291394333355227 32354032509437091500032841)
      ·
        refine ⟨24265524382077818625024631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32354032509437091500032841 24265524382077818625024631)
        ·
          refine ⟨36398286573116727937536947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24265524382077818625024631 36398286573116727937536947)
          ·
            refine ⟨54597429859675091906305421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36398286573116727937536947 54597429859675091906305421)
            ·
              refine ⟨20474036197378159464864533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54597429859675091906305421 20474036197378159464864533)
              ·
                refine ⟨959720446752101224915525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20474036197378159464864533 959720446752101224915525)
                ·
                  refine ⟨179947583766018979671661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 959720446752101224915525 179947583766018979671661)
                  ·
                    rfl

theorem cell21_788505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_788505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_788505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_788505 prefixEnd_788505 := by exact prefixLift 788505
  have htrace : WordTrace (prefixWord ++ tailWord_788505) baseStart_788505 baseEnd_788505 := by
    simpa [prefixWord, tailWord_788505, baseEnd_788505] using wordTrace_append hprefix tailTrace_788505
  have hstable : (prefixWord ++ tailWord_788505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788505).length < 2 ^ (prefixWord ++ tailWord_788505).sum := by decide
  have hdescent : baseEnd_788505 < baseStart_788505 := by decide
  rcases family_descends (prefixWord ++ tailWord_788505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788508 : List Nat := [2, 2, 3, 1, 3, 3, 1, 1, 5]
def baseStart_788508 : Nat := 118140960795 + 788508 * 2 ^ 59
def prefixEnd_788508 : Nat := 4983230072969 + 3 ^ 40 * 788508 * 2
def baseEnd_788508 : Nat := 179948268406891641121655

theorem tailTrace_788508 : CollatzResearch.WordTrace tailWord_788508 prefixEnd_788508 179948268406891641121655 := by
  unfold tailWord_788508
  simp only [CollatzResearch.WordTrace]
  refine ⟨14379624713688828645083089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19172832951585104860110785 14379624713688828645083089)
  ·
    refine ⟨10784718535266621483812317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14379624713688828645083089 10784718535266621483812317)
    ·
      refine ⟨4044269450724983056429619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10784718535266621483812317 4044269450724983056429619)
      ·
        refine ⟨6066404176087474584644429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4044269450724983056429619 6066404176087474584644429)
        ·
          refine ⟨2274901566032802969241661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6066404176087474584644429 2274901566032802969241661)
          ·
            refine ⟨853088087262301113465623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2274901566032802969241661 853088087262301113465623)
            ·
              refine ⟨1279632130893451670198435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853088087262301113465623 1279632130893451670198435)
              ·
                refine ⟨1919448196340177505297653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1279632130893451670198435 1919448196340177505297653)
                ·
                  refine ⟨179948268406891641121655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1919448196340177505297653 179948268406891641121655)
                  ·
                    rfl

theorem cell21_788508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_788508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_788508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_788508 prefixEnd_788508 := by exact prefixLift 788508
  have htrace : WordTrace (prefixWord ++ tailWord_788508) baseStart_788508 baseEnd_788508 := by
    simpa [prefixWord, tailWord_788508, baseEnd_788508] using wordTrace_append hprefix tailTrace_788508
  have hstable : (prefixWord ++ tailWord_788508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788508).length < 2 ^ (prefixWord ++ tailWord_788508).sum := by decide
  have hdescent : baseEnd_788508 < baseStart_788508 := by decide
  rcases family_descends (prefixWord ++ tailWord_788508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788736 : List Nat := [2, 1, 1, 2, 1, 1, 8, 2, 3]
def baseStart_788736 : Nat := 118140960795 + 788736 * 2 ^ 59
def prefixEnd_788736 : Nat := 4983230072969 + 3 ^ 40 * 788736 * 2
def baseEnd_788736 : Nat := 180000301113213911321189

theorem tailTrace_788736 : CollatzResearch.WordTrace tailWord_788736 prefixEnd_788736 180000301113213911321189 := by
  unfold tailWord_788736
  simp only [CollatzResearch.WordTrace]
  refine ⟨14383782635275826114733031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19178376847034434819644041 14383782635275826114733031)
  ·
    refine ⟨21575673952913739172099547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14383782635275826114733031 21575673952913739172099547)
    ·
      refine ⟨32363510929370608758149321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21575673952913739172099547 32363510929370608758149321)
      ·
        refine ⟨24272633197027956568611991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32363510929370608758149321 24272633197027956568611991)
        ·
          refine ⟨36408949795541934852917987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24272633197027956568611991 36408949795541934852917987)
          ·
            refine ⟨54613424693312902279376981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36408949795541934852917987 54613424693312902279376981)
            ·
              refine ⟨640001070624760573586449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 54613424693312902279376981 640001070624760573586449)
              ·
                refine ⟨480000802968570430189837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640001070624760573586449 480000802968570430189837)
                ·
                  refine ⟨180000301113213911321189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 480000802968570430189837 180000301113213911321189)
                  ·
                    rfl

theorem cell21_788736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 3].length) (baseStart_788736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_788736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_788736 prefixEnd_788736 := by exact prefixLift 788736
  have htrace : WordTrace (prefixWord ++ tailWord_788736) baseStart_788736 baseEnd_788736 := by
    simpa [prefixWord, tailWord_788736, baseEnd_788736] using wordTrace_append hprefix tailTrace_788736
  have hstable : (prefixWord ++ tailWord_788736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788736).length < 2 ^ (prefixWord ++ tailWord_788736).sum := by decide
  have hdescent : baseEnd_788736 < baseStart_788736 := by decide
  rcases family_descends (prefixWord ++ tailWord_788736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788781 : List Nat := [1, 5, 3, 1, 2, 1, 8]
def baseStart_788781 : Nat := 118140960795 + 788781 * 2 ^ 59
def prefixEnd_788781 : Nat := 4983230072969 + 3 ^ 40 * 788781 * 2
def baseEnd_788781 : Nat := 20001174525144870341233

theorem tailTrace_788781 : CollatzResearch.WordTrace tailWord_788781 prefixEnd_788781 20001174525144870341233 := by
  unfold tailWord_788781
  simp only [CollatzResearch.WordTrace]
  refine ⟨28769206555388624914854197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19179471036925749943236131 28769206555388624914854197)
  ·
    refine ⟨2697113114567683585767581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28769206555388624914854197 2697113114567683585767581)
    ·
      refine ⟨1011417417962881344662843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2697113114567683585767581 1011417417962881344662843)
      ·
        refine ⟨1517126126944322016994265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1011417417962881344662843 1517126126944322016994265)
        ·
          refine ⟨1137844595208241512745699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1517126126944322016994265 1137844595208241512745699)
          ·
            refine ⟨1706766892812362269118549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137844595208241512745699 1706766892812362269118549)
            ·
              refine ⟨20001174525144870341233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1706766892812362269118549 20001174525144870341233)
              ·
                rfl

theorem cell21_788781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 8].length) (baseStart_788781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_788781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_788781 prefixEnd_788781 := by exact prefixLift 788781
  have htrace : WordTrace (prefixWord ++ tailWord_788781) baseStart_788781 baseEnd_788781 := by
    simpa [prefixWord, tailWord_788781, baseEnd_788781] using wordTrace_append hprefix tailTrace_788781
  have hstable : (prefixWord ++ tailWord_788781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788781).length < 2 ^ (prefixWord ++ tailWord_788781).sum := by decide
  have hdescent : baseEnd_788781 < baseStart_788781 := by decide
  rcases family_descends (prefixWord ++ tailWord_788781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788823 : List Nat := [1, 1, 3, 2, 3, 1, 3, 7]
def baseStart_788823 : Nat := 118140960795 + 788823 * 2 ^ 59
def prefixEnd_788823 : Nat := 4983230072969 + 3 ^ 40 * 788823 * 2
def baseEnd_788823 : Nat := 60006718566173697790337

theorem tailTrace_788823 : CollatzResearch.WordTrace tailWord_788823 prefixEnd_788823 60006718566173697790337 := by
  unfold tailWord_788823
  simp only [CollatzResearch.WordTrace]
  refine ⟨28770738421236466087883123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19180492280824310725255415 28770738421236466087883123)
  ·
    refine ⟨43156107631854699131824685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28770738421236466087883123 43156107631854699131824685)
    ·
      refine ⟨16183540361945512174434257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43156107631854699131824685 16183540361945512174434257)
      ·
        refine ⟨12137655271459134130825693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16183540361945512174434257 12137655271459134130825693)
        ·
          refine ⟨4551620726797175299059635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12137655271459134130825693 4551620726797175299059635)
          ·
            refine ⟨6827431090195762948589453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4551620726797175299059635 6827431090195762948589453)
            ·
              refine ⟨2560286658823411105721045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6827431090195762948589453 2560286658823411105721045)
              ·
                refine ⟨60006718566173697790337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2560286658823411105721045 60006718566173697790337)
                ·
                  rfl

theorem cell21_788823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 7].length) (baseStart_788823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_788823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_788823 prefixEnd_788823 := by exact prefixLift 788823
  have htrace : WordTrace (prefixWord ++ tailWord_788823) baseStart_788823 baseEnd_788823 := by
    simpa [prefixWord, tailWord_788823, baseEnd_788823] using wordTrace_append hprefix tailTrace_788823
  have hstable : (prefixWord ++ tailWord_788823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788823).length < 2 ^ (prefixWord ++ tailWord_788823).sum := by decide
  have hdescent : baseEnd_788823 < baseStart_788823 := by decide
  rcases family_descends (prefixWord ++ tailWord_788823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_788840 : List Nat := [2, 1, 4, 2, 2, 3, 7]
def baseStart_788840 : Nat := 118140960795 + 788840 * 2 ^ 59
def prefixEnd_788840 : Nat := 4983230072969 + 3 ^ 40 * 788840 * 2
def baseEnd_788840 : Nat := 20002670592236982398627

theorem tailTrace_788840 : CollatzResearch.WordTrace tailWord_788840 prefixEnd_788840 20002670592236982398627 := by
  unfold tailWord_788840
  simp only [CollatzResearch.WordTrace]
  refine ⟨14385679231087438995625987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19180905641449918660834649 14385679231087438995625987)
  ·
    refine ⟨21578518846631158493438981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14385679231087438995625987 21578518846631158493438981)
    ·
      refine ⟨4045972283743342217519809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21578518846631158493438981 4045972283743342217519809)
      ·
        refine ⟨3034479212807506663139857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4045972283743342217519809 3034479212807506663139857)
        ·
          refine ⟨2275859409605629997354893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3034479212807506663139857 2275859409605629997354893)
          ·
            refine ⟨853447278602111249008085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2275859409605629997354893 853447278602111249008085)
            ·
              refine ⟨20002670592236982398627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 853447278602111249008085 20002670592236982398627)
              ·
                rfl

theorem cell21_788840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 7].length) (baseStart_788840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_788840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_788840 prefixEnd_788840 := by exact prefixLift 788840
  have htrace : WordTrace (prefixWord ++ tailWord_788840) baseStart_788840 baseEnd_788840 := by
    simpa [prefixWord, tailWord_788840, baseEnd_788840] using wordTrace_append hprefix tailTrace_788840
  have hstable : (prefixWord ++ tailWord_788840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_788840).length < 2 ^ (prefixWord ++ tailWord_788840).sum := by decide
  have hdescent : baseEnd_788840 < baseStart_788840 := by decide
  rcases family_descends (prefixWord ++ tailWord_788840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789122 : List Nat := [3, 4, 3, 1, 2, 1, 1, 2, 4]
def baseStart_789122 : Nat := 118140960795 + 789122 * 2 ^ 59
def prefixEnd_789122 : Nat := 4983230072969 + 3 ^ 40 * 789122 * 2
def baseEnd_789122 : Nat := 180088391572163017887067

theorem tailTrace_789122 : CollatzResearch.WordTrace tailWord_789122 prefixEnd_789122 180088391572163017887067 := by
  unfold tailWord_789122
  simp only [CollatzResearch.WordTrace]
  refine ⟨7195410961788310038254405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19187762564768826768678413 7195410961788310038254405)
  ·
    refine ⟨1349139555335308132172701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7195410961788310038254405 1349139555335308132172701)
    ·
      refine ⟨505927333250740549564763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1349139555335308132172701 505927333250740549564763)
      ·
        refine ⟨758890999876110824347145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505927333250740549564763 758890999876110824347145)
        ·
          refine ⟨569168249907083118260359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 758890999876110824347145 569168249907083118260359)
          ·
            refine ⟨853752374860624677390539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569168249907083118260359 853752374860624677390539)
            ·
              refine ⟨1280628562290937016085809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853752374860624677390539 1280628562290937016085809)
              ·
                refine ⟨960471421718202762064357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1280628562290937016085809 960471421718202762064357)
                ·
                  refine ⟨180088391572163017887067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 960471421718202762064357 180088391572163017887067)
                  ·
                    rfl

theorem cell21_789122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_789122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_789122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_789122 prefixEnd_789122 := by exact prefixLift 789122
  have htrace : WordTrace (prefixWord ++ tailWord_789122) baseStart_789122 baseEnd_789122 := by
    simpa [prefixWord, tailWord_789122, baseEnd_789122] using wordTrace_append hprefix tailTrace_789122
  have hstable : (prefixWord ++ tailWord_789122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789122).length < 2 ^ (prefixWord ++ tailWord_789122).sum := by decide
  have hdescent : baseEnd_789122 < baseStart_789122 := by decide
  rcases family_descends (prefixWord ++ tailWord_789122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789192 : List Nat := [2, 1, 3, 1, 2, 4, 3, 2, 3]
def baseStart_789192 : Nat := 118140960795 + 789192 * 2 ^ 59
def prefixEnd_789192 : Nat := 4983230072969 + 3 ^ 40 * 789192 * 2
def baseEnd_789192 : Nat := 180104366525858451720257

theorem tailTrace_789192 : CollatzResearch.WordTrace tailWord_789192 prefixEnd_789192 180104366525858451720257 := by
  unfold tailWord_789192
  simp only [CollatzResearch.WordTrace]
  refine ⟨14392098478449821054032915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19189464637933094738710553 14392098478449821054032915)
  ·
    refine ⟨21588147717674731581049373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14392098478449821054032915 21588147717674731581049373)
    ·
      refine ⟨8095555394128024342893515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21588147717674731581049373 8095555394128024342893515)
      ·
        refine ⟨12143333091192036514340273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8095555394128024342893515 12143333091192036514340273)
        ·
          refine ⟨9107499818394027385755205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12143333091192036514340273 9107499818394027385755205)
          ·
            refine ⟨1707656215948880134829101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9107499818394027385755205 1707656215948880134829101)
            ·
              refine ⟨640371080980830050560913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1707656215948880134829101 640371080980830050560913)
              ·
                refine ⟨480278310735622537920685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640371080980830050560913 480278310735622537920685)
                ·
                  refine ⟨180104366525858451720257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 480278310735622537920685 180104366525858451720257)
                  ·
                    rfl

theorem cell21_789192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 3].length) (baseStart_789192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_789192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_789192 prefixEnd_789192 := by exact prefixLift 789192
  have htrace : WordTrace (prefixWord ++ tailWord_789192) baseStart_789192 baseEnd_789192 := by
    simpa [prefixWord, tailWord_789192, baseEnd_789192] using wordTrace_append hprefix tailTrace_789192
  have hstable : (prefixWord ++ tailWord_789192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789192).length < 2 ^ (prefixWord ++ tailWord_789192).sum := by decide
  have hdescent : baseEnd_789192 < baseStart_789192 := by decide
  rcases family_descends (prefixWord ++ tailWord_789192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789237 : List Nat := [1, 3, 6, 1, 1, 9]
def baseStart_789237 : Nat := 118140960795 + 789237 * 2 ^ 59
def prefixEnd_789237 : Nat := 4983230072969 + 3 ^ 40 * 789237 * 2
def baseEnd_789237 : Nat := 6670912449590680498895

theorem tailTrace_789237 : CollatzResearch.WordTrace tailWord_789237 prefixEnd_789237 6670912449590680498895 := by
  unfold tailWord_789237
  simp only [CollatzResearch.WordTrace]
  refine ⟨28785838241736614793453965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19190558827824409862302643 28785838241736614793453965)
  ·
    refine ⟨10794689340651230547545237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28785838241736614793453965 10794689340651230547545237)
    ·
      refine ⟨506001062843026431916183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10794689340651230547545237 506001062843026431916183)
      ·
        refine ⟨759001594264539647874275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506001062843026431916183 759001594264539647874275)
        ·
          refine ⟨1138502391396809471811413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759001594264539647874275 1138502391396809471811413)
          ·
            refine ⟨6670912449590680498895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1138502391396809471811413 6670912449590680498895)
            ·
              rfl

theorem cell21_789237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 9].length) (baseStart_789237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_789237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_789237 prefixEnd_789237 := by exact prefixLift 789237
  have htrace : WordTrace (prefixWord ++ tailWord_789237) baseStart_789237 baseEnd_789237 := by
    simpa [prefixWord, tailWord_789237, baseEnd_789237] using wordTrace_append hprefix tailTrace_789237
  have hstable : (prefixWord ++ tailWord_789237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789237).length < 2 ^ (prefixWord ++ tailWord_789237).sum := by decide
  have hdescent : baseEnd_789237 < baseStart_789237 := by decide
  rcases family_descends (prefixWord ++ tailWord_789237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789316 : List Nat := [2, 3, 4, 2, 1, 1, 3, 1, 4]
def baseStart_789316 : Nat := 118140960795 + 789316 * 2 ^ 59
def prefixEnd_789316 : Nat := 4983230072969 + 3 ^ 40 * 789316 * 2
def baseEnd_789316 : Nat := 180132665015261791653337

theorem tailTrace_789316 : CollatzResearch.WordTrace tailWord_789316 prefixEnd_789316 180132665015261791653337 := by
  unfold tailWord_789316
  simp only [CollatzResearch.WordTrace]
  refine ⟨14394359804225205642789901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19192479738966940857053201 14394359804225205642789901)
  ·
    refine ⟨5397884926584452116046213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14394359804225205642789901 5397884926584452116046213)
    ·
      refine ⟨1012103423734584771758665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5397884926584452116046213 1012103423734584771758665)
      ·
        refine ⟨759077567800938578818999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1012103423734584771758665 759077567800938578818999)
        ·
          refine ⟨1138616351701407868228499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759077567800938578818999 1138616351701407868228499)
          ·
            refine ⟨1707924527552111802342749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138616351701407868228499 1707924527552111802342749)
            ·
              refine ⟨640471697832041925878531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1707924527552111802342749 640471697832041925878531)
              ·
                refine ⟨960707546748062888817797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640471697832041925878531 960707546748062888817797)
                ·
                  refine ⟨180132665015261791653337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 960707546748062888817797 180132665015261791653337)
                  ·
                    rfl

theorem cell21_789316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_789316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_789316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_789316 prefixEnd_789316 := by exact prefixLift 789316
  have htrace : WordTrace (prefixWord ++ tailWord_789316) baseStart_789316 baseEnd_789316 := by
    simpa [prefixWord, tailWord_789316, baseEnd_789316] using wordTrace_append hprefix tailTrace_789316
  have hstable : (prefixWord ++ tailWord_789316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789316).length < 2 ^ (prefixWord ++ tailWord_789316).sum := by decide
  have hdescent : baseEnd_789316 < baseStart_789316 := by decide
  rcases family_descends (prefixWord ++ tailWord_789316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789448 : List Nat := [2, 1, 3, 1, 5, 1, 3, 5]
def baseStart_789448 : Nat := 118140960795 + 789448 * 2 ^ 59
def prefixEnd_789448 : Nat := 4983230072969 + 3 ^ 40 * 789448 * 2
def baseEnd_789448 : Nat := 60054263071219631817689

theorem tailTrace_789448 : CollatzResearch.WordTrace tailWord_789448 prefixEnd_789448 60054263071219631817689 := by
  unfold tailWord_789448
  simp only [CollatzResearch.WordTrace]
  refine ⟨14396767021986098914692499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19195689362648131886256665 14396767021986098914692499)
  ·
    refine ⟨21595150532979148372038749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14396767021986098914692499 21595150532979148372038749)
    ·
      refine ⟨8098181449867180639514531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21595150532979148372038749 8098181449867180639514531)
      ·
        refine ⟨12147272174800770959271797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8098181449867180639514531 12147272174800770959271797)
        ·
          refine ⟨1138806766387572277431731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12147272174800770959271797 1138806766387572277431731)
          ·
            refine ⟨1708210149581358416147597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138806766387572277431731 1708210149581358416147597)
            ·
              refine ⟨640578806093009406055349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1708210149581358416147597 640578806093009406055349)
              ·
                refine ⟨60054263071219631817689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 640578806093009406055349 60054263071219631817689)
                ·
                  rfl

theorem cell21_789448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 5].length) (baseStart_789448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_789448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_789448 prefixEnd_789448 := by exact prefixLift 789448
  have htrace : WordTrace (prefixWord ++ tailWord_789448) baseStart_789448 baseEnd_789448 := by
    simpa [prefixWord, tailWord_789448, baseEnd_789448] using wordTrace_append hprefix tailTrace_789448
  have hstable : (prefixWord ++ tailWord_789448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789448).length < 2 ^ (prefixWord ++ tailWord_789448).sum := by decide
  have hdescent : baseEnd_789448 < baseStart_789448 := by decide
  rcases family_descends (prefixWord ++ tailWord_789448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789476 : List Nat := [2, 3, 1, 1, 1, 1, 2, 6, 4]
def baseStart_789476 : Nat := 118140960795 + 789476 * 2 ^ 59
def prefixEnd_789476 : Nat := 4983230072969 + 3 ^ 40 * 789476 * 2
def baseEnd_789476 : Nat := 180169179195137068986343

theorem tailTrace_789476 : CollatzResearch.WordTrace tailWord_789476 prefixEnd_789476 180169179195137068986343 := by
  unfold tailWord_789476
  simp only [CollatzResearch.WordTrace]
  refine ⟨14397277643935379305702141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19196370191913839074269521 14397277643935379305702141)
  ·
    refine ⟨5398979116475767239638303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14397277643935379305702141 5398979116475767239638303)
    ·
      refine ⟨8098468674713650859457455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5398979116475767239638303 8098468674713650859457455)
      ·
        refine ⟨12147703012070476289186183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8098468674713650859457455 12147703012070476289186183)
        ·
          refine ⟨18221554518105714433779275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12147703012070476289186183 18221554518105714433779275)
          ·
            refine ⟨27332331777158571650668913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18221554518105714433779275 27332331777158571650668913)
            ·
              refine ⟨20499248832868928738001685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27332331777158571650668913 20499248832868928738001685)
              ·
                refine ⟨960902289040731034593829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20499248832868928738001685 960902289040731034593829)
                ·
                  refine ⟨180169179195137068986343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 960902289040731034593829 180169179195137068986343)
                  ·
                    rfl

theorem cell21_789476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_789476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_789476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_789476 prefixEnd_789476 := by exact prefixLift 789476
  have htrace : WordTrace (prefixWord ++ tailWord_789476) baseStart_789476 baseEnd_789476 := by
    simpa [prefixWord, tailWord_789476, baseEnd_789476] using wordTrace_append hprefix tailTrace_789476
  have hstable : (prefixWord ++ tailWord_789476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789476).length < 2 ^ (prefixWord ++ tailWord_789476).sum := by decide
  have hdescent : baseEnd_789476 < baseStart_789476 := by decide
  rcases family_descends (prefixWord ++ tailWord_789476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789479 : List Nat := [1, 1, 5, 2, 2, 1, 2, 4, 3]
def baseStart_789479 : Nat := 118140960795 + 789479 * 2 ^ 59
def prefixEnd_789479 : Nat := 4983230072969 + 3 ^ 40 * 789479 * 2
def baseEnd_789479 : Nat := 180169863836009730436337

theorem tailTrace_789479 : CollatzResearch.WordTrace tailWord_789479 prefixEnd_789479 180169863836009730436337 := by
  unfold tailWord_789479
  simp only [CollatzResearch.WordTrace]
  refine ⟨28794664706859890123763491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19196443137906593415842327 28794664706859890123763491)
  ·
    refine ⟨43191997060289835185645237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28794664706859890123763491 43191997060289835185645237)
    ·
      refine ⟨4049249724402172048654241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43191997060289835185645237 4049249724402172048654241)
      ·
        refine ⟨3036937293301629036490681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4049249724402172048654241 3036937293301629036490681)
        ·
          refine ⟨2277702969976221777368011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3036937293301629036490681 2277702969976221777368011)
          ·
            refine ⟨3416554454964332666052017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2277702969976221777368011 3416554454964332666052017)
            ·
              refine ⟨2562415841223249499539013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3416554454964332666052017 2562415841223249499539013)
              ·
                refine ⟨480452970229359281163565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2562415841223249499539013 480452970229359281163565)
                ·
                  refine ⟨180169863836009730436337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 480452970229359281163565 180169863836009730436337)
                  ·
                    rfl

theorem cell21_789479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 3].length) (baseStart_789479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_789479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_789479 prefixEnd_789479 := by exact prefixLift 789479
  have htrace : WordTrace (prefixWord ++ tailWord_789479) baseStart_789479 baseEnd_789479 := by
    simpa [prefixWord, tailWord_789479, baseEnd_789479] using wordTrace_append hprefix tailTrace_789479
  have hstable : (prefixWord ++ tailWord_789479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789479).length < 2 ^ (prefixWord ++ tailWord_789479).sum := by decide
  have hdescent : baseEnd_789479 < baseStart_789479 := by decide
  rcases family_descends (prefixWord ++ tailWord_789479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789538 : List Nat := [3, 3, 1, 1, 1, 3, 3, 1, 5]
def baseStart_789538 : Nat := 118140960795 + 789538 * 2 ^ 59
def prefixEnd_789538 : Nat := 4983230072969 + 3 ^ 40 * 789538 * 2
def baseEnd_789538 : Nat := 180183328439838738952883

theorem tailTrace_789538 : CollatzResearch.WordTrace tailWord_789538 prefixEnd_789538 180183328439838738952883 := by
  unfold tailWord_789538
  simp only [CollatzResearch.WordTrace]
  refine ⟨7199204153411535800040317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19197877742430762133440845 7199204153411535800040317)
  ·
    refine ⟨2699701557529325925015119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7199204153411535800040317 2699701557529325925015119)
    ·
      refine ⟨4049552336293988887522679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2699701557529325925015119 4049552336293988887522679)
      ·
        refine ⟨6074328504440983331284019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4049552336293988887522679 6074328504440983331284019)
        ·
          refine ⟨9111492756661474996926029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6074328504440983331284019 9111492756661474996926029)
          ·
            refine ⟨3416809783748053123847261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9111492756661474996926029 3416809783748053123847261)
            ·
              refine ⟨1281303668905519921442723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3416809783748053123847261 1281303668905519921442723)
              ·
                refine ⟨1921955503358279882164085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1281303668905519921442723 1921955503358279882164085)
                ·
                  refine ⟨180183328439838738952883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1921955503358279882164085 180183328439838738952883)
                  ·
                    rfl

theorem cell21_789538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_789538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_789538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_789538 prefixEnd_789538 := by exact prefixLift 789538
  have htrace : WordTrace (prefixWord ++ tailWord_789538) baseStart_789538 baseEnd_789538 := by
    simpa [prefixWord, tailWord_789538, baseEnd_789538] using wordTrace_append hprefix tailTrace_789538
  have hstable : (prefixWord ++ tailWord_789538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789538).length < 2 ^ (prefixWord ++ tailWord_789538).sum := by decide
  have hdescent : baseEnd_789538 < baseStart_789538 := by decide
  rcases family_descends (prefixWord ++ tailWord_789538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789552 : List Nat := [2, 1, 1, 1, 2, 4, 3, 3, 4]
def baseStart_789552 : Nat := 118140960795 + 789552 * 2 ^ 59
def prefixEnd_789552 : Nat := 4983230072969 + 3 ^ 40 * 789552 * 2
def baseEnd_789552 : Nat := 180186523430577825719521

theorem tailTrace_789552 : CollatzResearch.WordTrace tailWord_789552 prefixEnd_789552 180186523430577825719521 := by
  unfold tailWord_789552
  simp only [CollatzResearch.WordTrace]
  refine ⟨14398663617797711795585455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19198218157063615727447273 14398663617797711795585455)
  ·
    refine ⟨21597995426696567693378183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14398663617797711795585455 21597995426696567693378183)
    ·
      refine ⟨32396993140044851540067275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21597995426696567693378183 32396993140044851540067275)
      ·
        refine ⟨48595489710067277310100913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32396993140044851540067275 48595489710067277310100913)
        ·
          refine ⟨36446617282550457982575685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48595489710067277310100913 36446617282550457982575685)
          ·
            refine ⟨6833740740478210871732941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36446617282550457982575685 6833740740478210871732941)
            ·
              refine ⟨2562652777679329076899853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6833740740478210871732941 2562652777679329076899853)
              ·
                refine ⟨960994791629748403837445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2562652777679329076899853 960994791629748403837445)
                ·
                  refine ⟨180186523430577825719521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 960994791629748403837445 180186523430577825719521)
                  ·
                    rfl

theorem cell21_789552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_789552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_789552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_789552 prefixEnd_789552 := by exact prefixLift 789552
  have htrace : WordTrace (prefixWord ++ tailWord_789552) baseStart_789552 baseEnd_789552 := by
    simpa [prefixWord, tailWord_789552, baseEnd_789552] using wordTrace_append hprefix tailTrace_789552
  have hstable : (prefixWord ++ tailWord_789552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789552).length < 2 ^ (prefixWord ++ tailWord_789552).sum := by decide
  have hdescent : baseEnd_789552 < baseStart_789552 := by decide
  rcases family_descends (prefixWord ++ tailWord_789552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789614 : List Nat := [4, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_789614 : Nat := 118140960795 + 789614 * 2 ^ 59
def prefixEnd_789614 : Nat := 4983230072969 + 3 ^ 40 * 789614 * 2
def baseEnd_789614 : Nat := 180200672675279495686061

theorem tailTrace_789614 : CollatzResearch.WordTrace tailWord_789614 prefixEnd_789614 180200672675279495686061 := by
  unfold tailWord_789614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3599948570171351022490987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19199725707580538786618597 3599948570171351022490987)
  ·
    refine ⟨5399922855257026533736481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3599948570171351022490987 5399922855257026533736481)
    ·
      refine ⟨4049942141442769900302361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5399922855257026533736481 4049942141442769900302361)
      ·
        refine ⟨3037456606082077425226771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4049942141442769900302361 3037456606082077425226771)
        ·
          refine ⟨4556184909123116137840157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3037456606082077425226771 4556184909123116137840157)
          ·
            refine ⟨1708569340921168551690059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4556184909123116137840157 1708569340921168551690059)
            ·
              refine ⟨2562854011381752827535089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708569340921168551690059 2562854011381752827535089)
              ·
                refine ⟨1922140508536314620651317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2562854011381752827535089 1922140508536314620651317)
                ·
                  refine ⟨180200672675279495686061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1922140508536314620651317 180200672675279495686061)
                  ·
                    rfl

theorem cell21_789614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_789614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_789614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_789614 prefixEnd_789614 := by exact prefixLift 789614
  have htrace : WordTrace (prefixWord ++ tailWord_789614) baseStart_789614 baseEnd_789614 := by
    simpa [prefixWord, tailWord_789614, baseEnd_789614] using wordTrace_append hprefix tailTrace_789614
  have hstable : (prefixWord ++ tailWord_789614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789614).length < 2 ^ (prefixWord ++ tailWord_789614).sum := by decide
  have hdescent : baseEnd_789614 < baseStart_789614 := by decide
  rcases family_descends (prefixWord ++ tailWord_789614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789642 : List Nat := [3, 1, 2, 3, 1, 1, 10]
def baseStart_789642 : Nat := 118140960795 + 789642 * 2 ^ 59
def prefixEnd_789642 : Nat := 4983230072969 + 3 ^ 40 * 789642 * 2
def baseEnd_789642 : Nat := 20023006961861963246593

theorem tailTrace_789642 : CollatzResearch.WordTrace tailWord_789642 prefixEnd_789642 20023006961861963246593 := by
  unfold tailWord_789642
  simp only [CollatzResearch.WordTrace]
  refine ⟨7200152451317342240486795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19200406536846245974631453 7200152451317342240486795)
  ·
    refine ⟨10800228676976013360730193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7200152451317342240486795 10800228676976013360730193)
    ·
      refine ⟨8100171507732010020547645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10800228676976013360730193 8100171507732010020547645)
      ·
        refine ⟨3037564315399503757705367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8100171507732010020547645 3037564315399503757705367)
        ·
          refine ⟨4556346473099255636558051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3037564315399503757705367 4556346473099255636558051)
          ·
            refine ⟨6834519709648883454837077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4556346473099255636558051 6834519709648883454837077)
            ·
              refine ⟨20023006961861963246593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6834519709648883454837077 20023006961861963246593)
              ·
                rfl

theorem cell21_789642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 10].length) (baseStart_789642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_789642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_789642 prefixEnd_789642 := by exact prefixLift 789642
  have htrace : WordTrace (prefixWord ++ tailWord_789642) baseStart_789642 baseEnd_789642 := by
    simpa [prefixWord, tailWord_789642, baseEnd_789642] using wordTrace_append hprefix tailTrace_789642
  have hstable : (prefixWord ++ tailWord_789642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789642).length < 2 ^ (prefixWord ++ tailWord_789642).sum := by decide
  have hdescent : baseEnd_789642 < baseStart_789642 := by decide
  rcases family_descends (prefixWord ++ tailWord_789642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789687 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 8]
def baseStart_789687 : Nat := 118140960795 + 789687 * 2 ^ 59
def prefixEnd_789687 : Nat := 4983230072969 + 3 ^ 40 * 789687 * 2
def baseEnd_789687 : Nat := 180217332269847590969245

theorem tailTrace_789687 : CollatzResearch.WordTrace tailWord_789687 prefixEnd_789687 180217332269847590969245 := by
  unfold tailWord_789687
  simp only [CollatzResearch.WordTrace]
  refine ⟨28802251090106341647335315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19201500726737561098223543 28802251090106341647335315)
  ·
    refine ⟨43203376635159512471002973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28802251090106341647335315 43203376635159512471002973)
    ·
      refine ⟨16201266238184817176626115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43203376635159512471002973 16201266238184817176626115)
      ·
        refine ⟨24301899357277225764939173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16201266238184817176626115 24301899357277225764939173)
        ·
          refine ⟨4556606129489479830926095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24301899357277225764939173 4556606129489479830926095)
          ·
            refine ⟨6834909194234219746389143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4556606129489479830926095 6834909194234219746389143)
            ·
              refine ⟨10252363791351329619583715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6834909194234219746389143 10252363791351329619583715)
              ·
                refine ⟨15378545687026994429375573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10252363791351329619583715 15378545687026994429375573)
                ·
                  refine ⟨180217332269847590969245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15378545687026994429375573 180217332269847590969245)
                  ·
                    rfl

theorem cell21_789687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 8].length) (baseStart_789687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_789687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_789687 prefixEnd_789687 := by exact prefixLift 789687
  have htrace : WordTrace (prefixWord ++ tailWord_789687) baseStart_789687 baseEnd_789687 := by
    simpa [prefixWord, tailWord_789687, baseEnd_789687] using wordTrace_append hprefix tailTrace_789687
  have hstable : (prefixWord ++ tailWord_789687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789687).length < 2 ^ (prefixWord ++ tailWord_789687).sum := by decide
  have hdescent : baseEnd_789687 < baseStart_789687 := by decide
  rcases family_descends (prefixWord ++ tailWord_789687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789808 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 7]
def baseStart_789808 : Nat := 118140960795 + 789808 * 2 ^ 59
def prefixEnd_789808 : Nat := 4983230072969 + 3 ^ 40 * 789808 * 2
def baseEnd_789808 : Nat := 180244946118378269452331

theorem tailTrace_789808 : CollatzResearch.WordTrace tailWord_789808 prefixEnd_789808 180244946118378269452331 := by
  unfold tailWord_789808
  simp only [CollatzResearch.WordTrace]
  refine ⟨14403332161333989656245039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19204442881778652874993385 14403332161333989656245039)
  ·
    refine ⟨21604998242000984484367559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14403332161333989656245039 21604998242000984484367559)
    ·
      refine ⟨32407497363001476726551339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21604998242000984484367559 32407497363001476726551339)
      ·
        refine ⟨48611246044502215089827009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32407497363001476726551339 48611246044502215089827009)
        ·
          refine ⟨36458434533376661317370257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48611246044502215089827009 36458434533376661317370257)
          ·
            refine ⟨27343825900032495988027693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36458434533376661317370257 27343825900032495988027693)
            ·
              refine ⟨10253934712512185995510385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27343825900032495988027693 10253934712512185995510385)
              ·
                refine ⟨7690451034384139496632789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10253934712512185995510385 7690451034384139496632789)
                ·
                  refine ⟨180244946118378269452331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7690451034384139496632789 180244946118378269452331)
                  ·
                    rfl

theorem cell21_789808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_789808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_789808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_789808 prefixEnd_789808 := by exact prefixLift 789808
  have htrace : WordTrace (prefixWord ++ tailWord_789808) baseStart_789808 baseEnd_789808 := by
    simpa [prefixWord, tailWord_789808, baseEnd_789808] using wordTrace_append hprefix tailTrace_789808
  have hstable : (prefixWord ++ tailWord_789808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789808).length < 2 ^ (prefixWord ++ tailWord_789808).sum := by decide
  have hdescent : baseEnd_789808 < baseStart_789808 := by decide
  rcases family_descends (prefixWord ++ tailWord_789808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789814 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_789814 : Nat := 118140960795 + 789814 * 2 ^ 59
def prefixEnd_789814 : Nat := 4983230072969 + 3 ^ 40 * 789814 * 2
def baseEnd_789814 : Nat := 180246315400123592352319

theorem tailTrace_789814 : CollatzResearch.WordTrace tailWord_789814 prefixEnd_789814 180246315400123592352319 := by
  unfold tailWord_789814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1800430197540390146075531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19204588773764161558138997 1800430197540390146075531)
  ·
    refine ⟨2700645296310585219113297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1800430197540390146075531 2700645296310585219113297)
    ·
      refine ⟨2025483972232938914334973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2700645296310585219113297 2025483972232938914334973)
      ·
        refine ⟨759556489587352092875615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2025483972232938914334973 759556489587352092875615)
        ·
          refine ⟨1139334734381028139313423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759556489587352092875615 1139334734381028139313423)
          ·
            refine ⟨1709002101571542208970135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139334734381028139313423 1709002101571542208970135)
            ·
              refine ⟨2563503152357313313455203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709002101571542208970135 2563503152357313313455203)
              ·
                refine ⟨3845254728535969970182805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563503152357313313455203 3845254728535969970182805)
                ·
                  refine ⟨180246315400123592352319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3845254728535969970182805 180246315400123592352319)
                  ·
                    rfl

theorem cell21_789814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_789814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_789814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_789814 prefixEnd_789814 := by exact prefixLift 789814
  have htrace : WordTrace (prefixWord ++ tailWord_789814) baseStart_789814 baseEnd_789814 := by
    simpa [prefixWord, tailWord_789814, baseEnd_789814] using wordTrace_append hprefix tailTrace_789814
  have hstable : (prefixWord ++ tailWord_789814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789814).length < 2 ^ (prefixWord ++ tailWord_789814).sum := by decide
  have hdescent : baseEnd_789814 < baseStart_789814 := by decide
  rcases family_descends (prefixWord ++ tailWord_789814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789859 : List Nat := [1, 1, 1, 5, 2, 4, 1, 3, 3]
def baseStart_789859 : Nat := 118140960795 + 789859 * 2 ^ 59
def prefixEnd_789859 : Nat := 4983230072969 + 3 ^ 40 * 789859 * 2
def baseEnd_789859 : Nat := 180256585013213514102227

theorem tailTrace_789859 : CollatzResearch.WordTrace tailWord_789859 prefixEnd_789859 180256585013213514102227 := by
  unfold tailWord_789859
  simp only [CollatzResearch.WordTrace]
  refine ⟨28808524445483215022596631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19205682963655476681731087 28808524445483215022596631)
  ·
    refine ⟨43212786668224822533894947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28808524445483215022596631 43212786668224822533894947)
    ·
      refine ⟨64819180002337233800842421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43212786668224822533894947 64819180002337233800842421)
      ·
        refine ⟨6076798125219115668828977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64819180002337233800842421 6076798125219115668828977)
        ·
          refine ⟨4557598593914336751621733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6076798125219115668828977 4557598593914336751621733)
          ·
            refine ⟨854549736358938140929075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4557598593914336751621733 854549736358938140929075)
            ·
              refine ⟨1281824604538407211393613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854549736358938140929075 1281824604538407211393613)
              ·
                refine ⟨480684226701902704272605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1281824604538407211393613 480684226701902704272605)
                ·
                  refine ⟨180256585013213514102227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 480684226701902704272605 180256585013213514102227)
                  ·
                    rfl

theorem cell21_789859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 3].length) (baseStart_789859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_789859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_789859 prefixEnd_789859 := by exact prefixLift 789859
  have htrace : WordTrace (prefixWord ++ tailWord_789859) baseStart_789859 baseEnd_789859 := by
    simpa [prefixWord, tailWord_789859, baseEnd_789859] using wordTrace_append hprefix tailTrace_789859
  have hstable : (prefixWord ++ tailWord_789859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789859).length < 2 ^ (prefixWord ++ tailWord_789859).sum := by decide
  have hdescent : baseEnd_789859 < baseStart_789859 := by decide
  rcases family_descends (prefixWord ++ tailWord_789859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789890 : List Nat := [3, 4, 2, 1, 1, 2, 1, 3, 4]
def baseStart_789890 : Nat := 118140960795 + 789890 * 2 ^ 59
def prefixEnd_789890 : Nat := 4983230072969 + 3 ^ 40 * 789890 * 2
def baseEnd_789890 : Nat := 180263659635564349085497

theorem tailTrace_789890 : CollatzResearch.WordTrace tailWord_789890 prefixEnd_789890 180263659635564349085497 := by
  unfold tailWord_789890
  simp only [CollatzResearch.WordTrace]
  refine ⟨7202413777092726829243781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19206436738913938211316749 7202413777092726829243781)
  ·
    refine ⟨1350452583204886280483209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7202413777092726829243781 1350452583204886280483209)
    ·
      refine ⟨1012839437403664710362407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1350452583204886280483209 1012839437403664710362407)
      ·
        refine ⟨1519259156105497065543611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012839437403664710362407 1519259156105497065543611)
        ·
          refine ⟨2278888734158245598315417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1519259156105497065543611 2278888734158245598315417)
          ·
            refine ⟨1709166550618684198736563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2278888734158245598315417 1709166550618684198736563)
            ·
              refine ⟨2563749825928026298104845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709166550618684198736563 2563749825928026298104845)
              ·
                refine ⟨961406184723009861789317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2563749825928026298104845 961406184723009861789317)
                ·
                  refine ⟨180263659635564349085497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 961406184723009861789317 180263659635564349085497)
                  ·
                    rfl

theorem cell21_789890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_789890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_789890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_789890 prefixEnd_789890 := by exact prefixLift 789890
  have htrace : WordTrace (prefixWord ++ tailWord_789890) baseStart_789890 baseEnd_789890 := by
    simpa [prefixWord, tailWord_789890, baseEnd_789890] using wordTrace_append hprefix tailTrace_789890
  have hstable : (prefixWord ++ tailWord_789890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789890).length < 2 ^ (prefixWord ++ tailWord_789890).sum := by decide
  have hdescent : baseEnd_789890 < baseStart_789890 := by decide
  rcases family_descends (prefixWord ++ tailWord_789890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_789994 : List Nat := [3, 1, 3, 1, 4, 1, 2, 1, 5]
def baseStart_789994 : Nat := 118140960795 + 789994 * 2 ^ 59
def prefixEnd_789994 : Nat := 4983230072969 + 3 ^ 40 * 789994 * 2
def baseEnd_789994 : Nat := 180287393852483279351951

theorem tailTrace_789994 : CollatzResearch.WordTrace tailWord_789994 prefixEnd_789994 180287393852483279351951 := by
  unfold tailWord_789994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7203362074998533269690259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19208965533329422052507357 7203362074998533269690259)
  ·
    refine ⟨10805043112497799904535389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7203362074998533269690259 10805043112497799904535389)
    ·
      refine ⟨4051891167186674964200771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10805043112497799904535389 4051891167186674964200771)
      ·
        refine ⟨6077836750780012446301157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4051891167186674964200771 6077836750780012446301157)
        ·
          refine ⟨1139594390771252333681467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6077836750780012446301157 1139594390771252333681467)
          ·
            refine ⟨1709391586156878500522201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139594390771252333681467 1709391586156878500522201)
            ·
              refine ⟨1282043689617658875391651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1709391586156878500522201 1282043689617658875391651)
              ·
                refine ⟨1923065534426488313087477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1282043689617658875391651 1923065534426488313087477)
                ·
                  refine ⟨180287393852483279351951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1923065534426488313087477 180287393852483279351951)
                  ·
                    rfl

theorem cell21_789994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_789994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_789994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_789994 prefixEnd_789994 := by exact prefixLift 789994
  have htrace : WordTrace (prefixWord ++ tailWord_789994) baseStart_789994 baseEnd_789994 := by
    simpa [prefixWord, tailWord_789994, baseEnd_789994] using wordTrace_append hprefix tailTrace_789994
  have hstable : (prefixWord ++ tailWord_789994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_789994).length < 2 ^ (prefixWord ++ tailWord_789994).sum := by decide
  have hdescent : baseEnd_789994 < baseStart_789994 := by decide
  rcases family_descends (prefixWord ++ tailWord_789994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790014 : List Nat := [4, 2, 2, 3, 2, 1, 2, 5]
def baseStart_790014 : Nat := 118140960795 + 790014 * 2 ^ 59
def prefixEnd_790014 : Nat := 4983230072969 + 3 ^ 40 * 790014 * 2
def baseEnd_790014 : Nat := 60097319374989229672859

theorem tailTrace_790014 : CollatzResearch.WordTrace tailWord_790014 prefixEnd_790014 60097319374989229672859 := by
  unfold tailWord_790014
  simp only [CollatzResearch.WordTrace]
  refine ⟨3601772219990209561811137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19209451839947784329659397 3601772219990209561811137)
  ·
    refine ⟨2701329164992657171358353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3601772219990209561811137 2701329164992657171358353)
    ·
      refine ⟨2025996873744492878518765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2701329164992657171358353 2025996873744492878518765)
      ·
        refine ⟨759748827654184829444537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2025996873744492878518765 759748827654184829444537)
        ·
          refine ⟨569811620740638622083403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 759748827654184829444537 569811620740638622083403)
          ·
            refine ⟨854717431110957933125105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569811620740638622083403 854717431110957933125105)
            ·
              refine ⟨641038073333218449843829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854717431110957933125105 641038073333218449843829)
              ·
                refine ⟨60097319374989229672859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 641038073333218449843829 60097319374989229672859)
                ·
                  rfl

theorem cell21_790014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_790014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_790014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_790014 prefixEnd_790014 := by exact prefixLift 790014
  have htrace : WordTrace (prefixWord ++ tailWord_790014) baseStart_790014 baseEnd_790014 := by
    simpa [prefixWord, tailWord_790014, baseEnd_790014] using wordTrace_append hprefix tailTrace_790014
  have hstable : (prefixWord ++ tailWord_790014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790014).length < 2 ^ (prefixWord ++ tailWord_790014).sum := by decide
  have hdescent : baseEnd_790014 < baseStart_790014 := by decide
  rcases family_descends (prefixWord ++ tailWord_790014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790028 : List Nat := [2, 2, 1, 2, 6, 1, 1, 3, 3]
def baseStart_790028 : Nat := 118140960795 + 790028 * 2 ^ 59
def prefixEnd_790028 : Nat := 4983230072969 + 3 ^ 40 * 790028 * 2
def baseEnd_790028 : Nat := 180295153115706775785215

theorem tailTrace_790028 : CollatzResearch.WordTrace tailWord_790028 prefixEnd_790028 180295153115706775785215 := by
  unfold tailWord_790028
  simp only [CollatzResearch.WordTrace]
  refine ⟨14407344190935478442749369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19209792254580637923665825 14407344190935478442749369)
  ·
    refine ⟨10805508143201608832062027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14407344190935478442749369 10805508143201608832062027)
    ·
      refine ⟨16208262214802413248093041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10805508143201608832062027 16208262214802413248093041)
      ·
        refine ⟨12156196661101809936069781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16208262214802413248093041 12156196661101809936069781)
        ·
          refine ⟨569821718489147340753271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12156196661101809936069781 569821718489147340753271)
          ·
            refine ⟨854732577733721011129907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569821718489147340753271 854732577733721011129907)
            ·
              refine ⟨1282098866600581516694861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854732577733721011129907 1282098866600581516694861)
              ·
                refine ⟨480787074975218068760573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1282098866600581516694861 480787074975218068760573)
                ·
                  refine ⟨180295153115706775785215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 480787074975218068760573 180295153115706775785215)
                  ·
                    rfl

theorem cell21_790028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_790028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_790028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_790028 prefixEnd_790028 := by exact prefixLift 790028
  have htrace : WordTrace (prefixWord ++ tailWord_790028) baseStart_790028 baseEnd_790028 := by
    simpa [prefixWord, tailWord_790028, baseEnd_790028] using wordTrace_append hprefix tailTrace_790028
  have hstable : (prefixWord ++ tailWord_790028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790028).length < 2 ^ (prefixWord ++ tailWord_790028).sum := by decide
  have hdescent : baseEnd_790028 < baseStart_790028 := by decide
  rcases family_descends (prefixWord ++ tailWord_790028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790112 : List Nat := [2, 1, 1, 3, 2, 1, 1, 5, 5]
def baseStart_790112 : Nat := 118140960795 + 790112 * 2 ^ 59
def prefixEnd_790112 : Nat := 4983230072969 + 3 ^ 40 * 790112 * 2
def baseEnd_790112 : Nat := 180314323060141296385043

theorem tailTrace_790112 : CollatzResearch.WordTrace tailWord_790112 prefixEnd_790112 180314323060141296385043 := by
  unfold tailWord_790112
  simp only [CollatzResearch.WordTrace]
  refine ⟨14408876056783319615778295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19211834742377759487704393 14408876056783319615778295)
  ·
    refine ⟨21613314085174979423667443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14408876056783319615778295 21613314085174979423667443)
    ·
      refine ⟨32419971127762469135501165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21613314085174979423667443 32419971127762469135501165)
      ·
        refine ⟨12157489172910925925812937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32419971127762469135501165 12157489172910925925812937)
        ·
          refine ⟨9118116879683194444359703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12157489172910925925812937 9118116879683194444359703)
          ·
            refine ⟨13677175319524791666539555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9118116879683194444359703 13677175319524791666539555)
            ·
              refine ⟨20515762979287187499809333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13677175319524791666539555 20515762979287187499809333)
              ·
                refine ⟨1923352779308173828107125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20515762979287187499809333 1923352779308173828107125)
                ·
                  refine ⟨180314323060141296385043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1923352779308173828107125 180314323060141296385043)
                  ·
                    rfl

theorem cell21_790112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_790112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_790112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_790112 prefixEnd_790112 := by exact prefixLift 790112
  have htrace : WordTrace (prefixWord ++ tailWord_790112) baseStart_790112 baseEnd_790112 := by
    simpa [prefixWord, tailWord_790112, baseEnd_790112] using wordTrace_append hprefix tailTrace_790112
  have hstable : (prefixWord ++ tailWord_790112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790112).length < 2 ^ (prefixWord ++ tailWord_790112).sum := by decide
  have hdescent : baseEnd_790112 < baseStart_790112 := by decide
  rcases family_descends (prefixWord ++ tailWord_790112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790177 : List Nat := [1, 2, 3, 3, 2, 2, 3, 1, 4]
def baseStart_790177 : Nat := 118140960795 + 790177 * 2 ^ 59
def prefixEnd_790177 : Nat := 4983230072969 + 3 ^ 40 * 790177 * 2
def baseEnd_790177 : Nat := 180329156945715627801577

theorem tailTrace_790177 : CollatzResearch.WordTrace tailWord_790177 prefixEnd_790177 180329156945715627801577 := by
  unfold tailWord_790177
  simp only [CollatzResearch.WordTrace]
  refine ⟨28820122858331155332672785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19213415238887436888448523 28820122858331155332672785)
  ·
    refine ⟨21615092143748366499504589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28820122858331155332672785 21615092143748366499504589)
    ·
      refine ⟨8105659553905637437314221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21615092143748366499504589 8105659553905637437314221)
      ·
        refine ⟨3039622332714614038992833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8105659553905637437314221 3039622332714614038992833)
        ·
          refine ⟨2279716749535960529244625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3039622332714614038992833 2279716749535960529244625)
          ·
            refine ⟨1709787562151970396933469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2279716749535960529244625 1709787562151970396933469)
            ·
              refine ⟨641170335806988898850051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1709787562151970396933469 641170335806988898850051)
              ·
                refine ⟨961755503710483348275077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641170335806988898850051 961755503710483348275077)
                ·
                  refine ⟨180329156945715627801577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 961755503710483348275077 180329156945715627801577)
                  ·
                    rfl

theorem cell21_790177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 4].length) (baseStart_790177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_790177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_790177 prefixEnd_790177 := by exact prefixLift 790177
  have htrace : WordTrace (prefixWord ++ tailWord_790177) baseStart_790177 baseEnd_790177 := by
    simpa [prefixWord, tailWord_790177, baseEnd_790177] using wordTrace_append hprefix tailTrace_790177
  have hstable : (prefixWord ++ tailWord_790177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790177).length < 2 ^ (prefixWord ++ tailWord_790177).sum := by decide
  have hdescent : baseEnd_790177 < baseStart_790177 := by decide
  rcases family_descends (prefixWord ++ tailWord_790177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790233 : List Nat := [1, 2, 1, 2, 3, 3, 1, 8]
def baseStart_790233 : Nat := 118140960795 + 790233 * 2 ^ 59
def prefixEnd_790233 : Nat := 4983230072969 + 3 ^ 40 * 790233 * 2
def baseEnd_790233 : Nat := 60113978969557324956043

theorem tailTrace_790233 : CollatzResearch.WordTrace tailWord_790233 prefixEnd_790233 60113978969557324956043 := by
  unfold tailWord_790233
  simp only [CollatzResearch.WordTrace]
  refine ⟨28822165346128276896711353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19214776897418851264474235 28822165346128276896711353)
  ·
    refine ⟨21616624009596207672533515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28822165346128276896711353 21616624009596207672533515)
    ·
      refine ⟨32424936014394311508800273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21616624009596207672533515 32424936014394311508800273)
      ·
        refine ⟨24318702010795733631600205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32424936014394311508800273 24318702010795733631600205)
        ·
          refine ⟨9119513254048400111850077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24318702010795733631600205 9119513254048400111850077)
          ·
            refine ⟨3419817470268150041943779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9119513254048400111850077 3419817470268150041943779)
            ·
              refine ⟨5129726205402225062915669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3419817470268150041943779 5129726205402225062915669)
              ·
                refine ⟨60113978969557324956043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5129726205402225062915669 60113978969557324956043)
                ·
                  rfl

theorem cell21_790233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 8].length) (baseStart_790233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_790233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_790233 prefixEnd_790233 := by exact prefixLift 790233
  have htrace : WordTrace (prefixWord ++ tailWord_790233) baseStart_790233 baseEnd_790233 := by
    simpa [prefixWord, tailWord_790233, baseEnd_790233] using wordTrace_append hprefix tailTrace_790233
  have hstable : (prefixWord ++ tailWord_790233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790233).length < 2 ^ (prefixWord ++ tailWord_790233).sum := by decide
  have hdescent : baseEnd_790233 < baseStart_790233 := by decide
  rcases family_descends (prefixWord ++ tailWord_790233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790447 : List Nat := [1, 1, 2, 1, 2, 2, 6, 2, 4]
def baseStart_790447 : Nat := 118140960795 + 790447 * 2 ^ 59
def prefixEnd_790447 : Nat := 4983230072969 + 3 ^ 40 * 790447 * 2
def baseEnd_790447 : Nat := 180390774624255158301025

theorem tailTrace_790447 : CollatzResearch.WordTrace tailWord_790447 prefixEnd_790447 180390774624255158301025 := by
  unfold tailWord_790447
  simp only [CollatzResearch.WordTrace]
  refine ⟨28829970567352991445001595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19219980378235327630001063 28829970567352991445001595)
  ·
    refine ⟨43244955851029487167502393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28829970567352991445001595 43244955851029487167502393)
    ·
      refine ⟨32433716888272115375626795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43244955851029487167502393 32433716888272115375626795)
      ·
        refine ⟨48650575332408173063440193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32433716888272115375626795 48650575332408173063440193)
        ·
          refine ⟨36487931499306129797580145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48650575332408173063440193 36487931499306129797580145)
          ·
            refine ⟨27365948624479597348185109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36487931499306129797580145 27365948624479597348185109)
            ·
              refine ⟨1282778841772481125696177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27365948624479597348185109 1282778841772481125696177)
              ·
                refine ⟨962084131329360844272133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1282778841772481125696177 962084131329360844272133)
                ·
                  refine ⟨180390774624255158301025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 962084131329360844272133 180390774624255158301025)
                  ·
                    rfl

theorem cell21_790447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 4].length) (baseStart_790447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_790447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_790447 prefixEnd_790447 := by exact prefixLift 790447
  have htrace : WordTrace (prefixWord ++ tailWord_790447) baseStart_790447 baseEnd_790447 := by
    simpa [prefixWord, tailWord_790447, baseEnd_790447] using wordTrace_append hprefix tailTrace_790447
  have hstable : (prefixWord ++ tailWord_790447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790447).length < 2 ^ (prefixWord ++ tailWord_790447).sum := by decide
  have hdescent : baseEnd_790447 < baseStart_790447 := by decide
  rcases family_descends (prefixWord ++ tailWord_790447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790478 : List Nat := [4, 1, 1, 1, 2, 2, 5, 5]
def baseStart_790478 : Nat := 118140960795 + 790478 * 2 ^ 59
def prefixEnd_790478 : Nat := 4983230072969 + 3 ^ 40 * 790478 * 2
def baseEnd_790478 : Nat := 60132616415535331094765

theorem tailTrace_790478 : CollatzResearch.WordTrace tailWord_790478 prefixEnd_790478 60132616415535331094765 := by
  unfold tailWord_790478
  simp only [CollatzResearch.WordTrace]
  refine ⟨3603887653780085467422511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19220734153493789159586725 3603887653780085467422511)
  ·
    refine ⟨5405831480670128201133767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3603887653780085467422511 5405831480670128201133767)
    ·
      refine ⟨8108747221005192301700651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5405831480670128201133767 8108747221005192301700651)
      ·
        refine ⟨12163120831507788452550977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8108747221005192301700651 12163120831507788452550977)
        ·
          refine ⟨9122340623630841339413233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12163120831507788452550977 9122340623630841339413233)
          ·
            refine ⟨6841755467723131004559925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9122340623630841339413233 6841755467723131004559925)
            ·
              refine ⟨641414575099043531677493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6841755467723131004559925 641414575099043531677493)
              ·
                refine ⟨60132616415535331094765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 641414575099043531677493 60132616415535331094765)
                ·
                  rfl

theorem cell21_790478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_790478 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_790478 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_790478 prefixEnd_790478 := by exact prefixLift 790478
  have htrace : WordTrace (prefixWord ++ tailWord_790478) baseStart_790478 baseEnd_790478 := by
    simpa [prefixWord, tailWord_790478, baseEnd_790478] using wordTrace_append hprefix tailTrace_790478
  have hstable : (prefixWord ++ tailWord_790478).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790478).length < 2 ^ (prefixWord ++ tailWord_790478).sum := by decide
  have hdescent : baseEnd_790478 < baseStart_790478 := by decide
  rcases family_descends (prefixWord ++ tailWord_790478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790498 : List Nat := [3, 3, 3, 1, 2, 2, 1, 2, 4]
def baseStart_790498 : Nat := 118140960795 + 790498 * 2 ^ 59
def prefixEnd_790498 : Nat := 4983230072969 + 3 ^ 40 * 790498 * 2
def baseEnd_790498 : Nat := 180402413519090402950921

theorem tailTrace_790498 : CollatzResearch.WordTrace tailWord_790498 prefixEnd_790498 180402413519090402950921 := by
  unfold tailWord_790498
  simp only [CollatzResearch.WordTrace]
  refine ⟨7207957672542056788777037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19221220460112151436738765 7207957672542056788777037)
  ·
    refine ⟨2702984127203271295791389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7207957672542056788777037 2702984127203271295791389)
    ·
      refine ⟨1013619047701226735921771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2702984127203271295791389 1013619047701226735921771)
      ·
        refine ⟨1520428571551840103882657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1013619047701226735921771 1520428571551840103882657)
        ·
          refine ⟨1140321428663880077911993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1520428571551840103882657 1140321428663880077911993)
          ·
            refine ⟨855241071497910058433995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1140321428663880077911993 855241071497910058433995)
            ·
              refine ⟨1282861607246865087650993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855241071497910058433995 1282861607246865087650993)
              ·
                refine ⟨962146205435148815738245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1282861607246865087650993 962146205435148815738245)
                ·
                  refine ⟨180402413519090402950921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 962146205435148815738245 180402413519090402950921)
                  ·
                    rfl

theorem cell21_790498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_790498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_790498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_790498 prefixEnd_790498 := by exact prefixLift 790498
  have htrace : WordTrace (prefixWord ++ tailWord_790498) baseStart_790498 baseEnd_790498 := by
    simpa [prefixWord, tailWord_790498, baseEnd_790498] using wordTrace_append hprefix tailTrace_790498
  have hstable : (prefixWord ++ tailWord_790498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790498).length < 2 ^ (prefixWord ++ tailWord_790498).sum := by decide
  have hdescent : baseEnd_790498 < baseStart_790498 := by decide
  rcases family_descends (prefixWord ++ tailWord_790498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790661 : List Nat := [1, 3, 1, 1, 5, 1, 1, 5, 3]
def baseStart_790661 : Nat := 118140960795 + 790661 * 2 ^ 59
def prefixEnd_790661 : Nat := 4983230072969 + 3 ^ 40 * 790661 * 2
def baseEnd_790661 : Nat := 180439612339838341733921

theorem tailTrace_790661 : CollatzResearch.WordTrace tailWord_790661 prefixEnd_790661 180439612339838341733921 := by
  unfold tailWord_790661
  simp only [CollatzResearch.WordTrace]
  refine ⟨28837775788577705993291837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19225183859051803995527891 28837775788577705993291837)
  ·
    refine ⟨10814165920716639747484439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28837775788577705993291837 10814165920716639747484439)
    ·
      refine ⟨16221248881074959621226659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10814165920716639747484439 16221248881074959621226659)
      ·
        refine ⟨24331873321612439431839989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16221248881074959621226659 24331873321612439431839989)
        ·
          refine ⟨2281113123901166196734999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24331873321612439431839989 2281113123901166196734999)
          ·
            refine ⟨3421669685851749295102499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2281113123901166196734999 3421669685851749295102499)
            ·
              refine ⟨5132504528777623942653749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3421669685851749295102499 5132504528777623942653749)
              ·
                refine ⟨481172299572902244623789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5132504528777623942653749 481172299572902244623789)
                ·
                  refine ⟨180439612339838341733921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 481172299572902244623789 180439612339838341733921)
                  ·
                    rfl

theorem cell21_790661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 3].length) (baseStart_790661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_790661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_790661 prefixEnd_790661 := by exact prefixLift 790661
  have htrace : WordTrace (prefixWord ++ tailWord_790661) baseStart_790661 baseEnd_790661 := by
    simpa [prefixWord, tailWord_790661, baseEnd_790661] using wordTrace_append hprefix tailTrace_790661
  have hstable : (prefixWord ++ tailWord_790661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790661).length < 2 ^ (prefixWord ++ tailWord_790661).sum := by decide
  have hdescent : baseEnd_790661 < baseStart_790661 := by decide
  rcases family_descends (prefixWord ++ tailWord_790661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790672 : List Nat := [2, 1, 1, 1, 1, 1, 14]
def baseStart_790672 : Nat := 118140960795 + 790672 * 2 ^ 59
def prefixEnd_790672 : Nat := 4983230072969 + 3 ^ 40 * 790672 * 2
def baseEnd_790672 : Nat := 20049124743300529672285

theorem tailTrace_790672 : CollatzResearch.WordTrace tailWord_790672 prefixEnd_790672 20049124743300529672285 := by
  unfold tailWord_790672
  simp only [CollatzResearch.WordTrace]
  refine ⟨14419088495768927435971135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19225451327691903247961513 14419088495768927435971135)
  ·
    refine ⟨21628632743653391153956703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14419088495768927435971135 21628632743653391153956703)
    ·
      refine ⟨32442949115480086730935055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21628632743653391153956703 32442949115480086730935055)
      ·
        refine ⟨48664423673220130096402583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32442949115480086730935055 48664423673220130096402583)
        ·
          refine ⟨72996635509830195144603875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48664423673220130096402583 72996635509830195144603875)
          ·
            refine ⟨109494953264745292716905813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72996635509830195144603875 109494953264745292716905813)
            ·
              refine ⟨20049124743300529672285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 109494953264745292716905813 20049124743300529672285)
              ·
                rfl

theorem cell21_790672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 14].length) (baseStart_790672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_790672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_790672 prefixEnd_790672 := by exact prefixLift 790672
  have htrace : WordTrace (prefixWord ++ tailWord_790672) baseStart_790672 baseEnd_790672 := by
    simpa [prefixWord, tailWord_790672, baseEnd_790672] using wordTrace_append hprefix tailTrace_790672
  have hstable : (prefixWord ++ tailWord_790672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790672).length < 2 ^ (prefixWord ++ tailWord_790672).sum := by decide
  have hdescent : baseEnd_790672 < baseStart_790672 := by decide
  rcases family_descends (prefixWord ++ tailWord_790672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790788 : List Nat := [2, 3, 2, 2, 4, 1, 2, 2, 3]
def baseStart_790788 : Nat := 118140960795 + 790788 * 2 ^ 59
def prefixEnd_790788 : Nat := 4983230072969 + 3 ^ 40 * 790788 * 2
def baseEnd_790788 : Nat := 180468595470114343116995

theorem tailTrace_790788 : CollatzResearch.WordTrace tailWord_790788 prefixEnd_790788 180468595470114343116995 := by
  unfold tailWord_790788
  simp only [CollatzResearch.WordTrace]
  refine ⟨14421203929558803341582509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19228271906078404455443345 14421203929558803341582509)
  ·
    refine ⟨5407951473584551253093441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14421203929558803341582509 5407951473584551253093441)
    ·
      refine ⟨4055963605188413439820081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5407951473584551253093441 4055963605188413439820081)
      ·
        refine ⟨3041972703891310079865061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4055963605188413439820081 3041972703891310079865061)
        ·
          refine ⟨570369881979620639974699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3041972703891310079865061 570369881979620639974699)
          ·
            refine ⟨855554822969430959962049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570369881979620639974699 855554822969430959962049)
            ·
              refine ⟨641666117227073219971537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 855554822969430959962049 641666117227073219971537)
              ·
                refine ⟨481249587920304914978653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 641666117227073219971537 481249587920304914978653)
                ·
                  refine ⟨180468595470114343116995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 481249587920304914978653 180468595470114343116995)
                  ·
                    rfl

theorem cell21_790788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_790788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_790788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_790788 prefixEnd_790788 := by exact prefixLift 790788
  have htrace : WordTrace (prefixWord ++ tailWord_790788) baseStart_790788 baseEnd_790788 := by
    simpa [prefixWord, tailWord_790788, baseEnd_790788] using wordTrace_append hprefix tailTrace_790788
  have hstable : (prefixWord ++ tailWord_790788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790788).length < 2 ^ (prefixWord ++ tailWord_790788).sum := by decide
  have hdescent : baseEnd_790788 < baseStart_790788 := by decide
  rcases family_descends (prefixWord ++ tailWord_790788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790813 : List Nat := [1, 4, 2, 3, 2, 1, 1, 2, 5]
def baseStart_790813 : Nat := 118140960795 + 790813 * 2 ^ 59
def prefixEnd_790813 : Nat := 4983230072969 + 3 ^ 40 * 790813 * 2
def baseEnd_790813 : Nat := 180474300810719855200277

theorem tailTrace_790813 : CollatzResearch.WordTrace tailWord_790813 prefixEnd_790813 180474300810719855200277 := by
  unfold tailWord_790813
  simp only [CollatzResearch.WordTrace]
  refine ⟨28843319684027035952825093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19228879789351357301883395 28843319684027035952825093)
  ·
    refine ⟨5408122440755069241154705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28843319684027035952825093 5408122440755069241154705)
    ·
      refine ⟨4056091830566301930866029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5408122440755069241154705 4056091830566301930866029)
      ·
        refine ⟨1521034436462363224074761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4056091830566301930866029 1521034436462363224074761)
        ·
          refine ⟨1140775827346772418056071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1521034436462363224074761 1140775827346772418056071)
          ·
            refine ⟨1711163741020158627084107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140775827346772418056071 1711163741020158627084107)
            ·
              refine ⟨2566745611530237940626161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711163741020158627084107 2566745611530237940626161)
              ·
                refine ⟨1925059208647678455469621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2566745611530237940626161 1925059208647678455469621)
                ·
                  refine ⟨180474300810719855200277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1925059208647678455469621 180474300810719855200277)
                  ·
                    rfl

theorem cell21_790813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_790813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_790813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_790813 prefixEnd_790813 := by exact prefixLift 790813
  have htrace : WordTrace (prefixWord ++ tailWord_790813) baseStart_790813 baseEnd_790813 := by
    simpa [prefixWord, tailWord_790813, baseEnd_790813] using wordTrace_append hprefix tailTrace_790813
  have hstable : (prefixWord ++ tailWord_790813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790813).length < 2 ^ (prefixWord ++ tailWord_790813).sum := by decide
  have hdescent : baseEnd_790813 < baseStart_790813 := by decide
  rcases family_descends (prefixWord ++ tailWord_790813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790841 : List Nat := [1, 2, 1, 6, 1, 2, 8]
def baseStart_790841 : Nat := 118140960795 + 790841 * 2 ^ 59
def prefixEnd_790841 : Nat := 4983230072969 + 3 ^ 40 * 790841 * 2
def baseEnd_790841 : Nat := 20053410088022003192617

theorem tailTrace_790841 : CollatzResearch.WordTrace tailWord_790841 prefixEnd_790841 20053410088022003192617 := by
  unfold tailWord_790841
  simp only [CollatzResearch.WordTrace]
  refine ⟨28844340927925596734844377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19229560618617064489896251 28844340927925596734844377)
  ·
    refine ⟨21633255695944197551133283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28844340927925596734844377 21633255695944197551133283)
    ·
      refine ⟨32449883543916296326699925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21633255695944197551133283 32449883543916296326699925)
      ·
        refine ⟨1521088291121076390314059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32449883543916296326699925 1521088291121076390314059)
        ·
          refine ⟨2281632436681614585471089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521088291121076390314059 2281632436681614585471089)
          ·
            refine ⟨1711224327511210939103317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2281632436681614585471089 1711224327511210939103317)
            ·
              refine ⟨20053410088022003192617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1711224327511210939103317 20053410088022003192617)
              ·
                rfl

theorem cell21_790841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 8].length) (baseStart_790841 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_790841 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_790841 prefixEnd_790841 := by exact prefixLift 790841
  have htrace : WordTrace (prefixWord ++ tailWord_790841) baseStart_790841 baseEnd_790841 := by
    simpa [prefixWord, tailWord_790841, baseEnd_790841] using wordTrace_append hprefix tailTrace_790841
  have hstable : (prefixWord ++ tailWord_790841).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790841).length < 2 ^ (prefixWord ++ tailWord_790841).sum := by decide
  have hdescent : baseEnd_790841 < baseStart_790841 := by decide
  rcases family_descends (prefixWord ++ tailWord_790841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_790954 : List Nat := [3, 1, 6, 1, 1, 1, 2, 2, 4]
def baseStart_790954 : Nat := 118140960795 + 790954 * 2 ^ 59
def prefixEnd_790954 : Nat := 4983230072969 + 3 ^ 40 * 790954 * 2
def baseEnd_790954 : Nat := 180506478931734943349989

theorem tailTrace_790954 : CollatzResearch.WordTrace tailWord_790954 prefixEnd_790954 180506478931734943349989 := by
  unfold tailWord_790954
  simp only [CollatzResearch.WordTrace]
  refine ⟨7212115594129054258426979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19232308251010811355805277 7212115594129054258426979)
  ·
    refine ⟨10818173391193581387640469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7212115594129054258426979 10818173391193581387640469)
    ·
      refine ⟨507101877712199127545647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10818173391193581387640469 507101877712199127545647)
      ·
        refine ⟨760652816568298691318471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507101877712199127545647 760652816568298691318471)
        ·
          refine ⟨1140979224852448036977707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760652816568298691318471 1140979224852448036977707)
          ·
            refine ⟨1711468837278672055466561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140979224852448036977707 1711468837278672055466561)
            ·
              refine ⟨1283601627959004041599921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1711468837278672055466561 1283601627959004041599921)
              ·
                refine ⟨962701220969253031199941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1283601627959004041599921 962701220969253031199941)
                ·
                  refine ⟨180506478931734943349989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 962701220969253031199941 180506478931734943349989)
                  ·
                    rfl

theorem cell21_790954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_790954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_790954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_790954 prefixEnd_790954 := by exact prefixLift 790954
  have htrace : WordTrace (prefixWord ++ tailWord_790954) baseStart_790954 baseEnd_790954 := by
    simpa [prefixWord, tailWord_790954, baseEnd_790954] using wordTrace_append hprefix tailTrace_790954
  have hstable : (prefixWord ++ tailWord_790954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_790954).length < 2 ^ (prefixWord ++ tailWord_790954).sum := by decide
  have hdescent : baseEnd_790954 < baseStart_790954 := by decide
  rcases family_descends (prefixWord ++ tailWord_790954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791013 : List Nat := [1, 3, 1, 5, 3, 1, 1, 2, 4]
def baseStart_791013 : Nat := 118140960795 + 791013 * 2 ^ 59
def prefixEnd_791013 : Nat := 4983230072969 + 3 ^ 40 * 791013 * 2
def baseEnd_791013 : Nat := 180519943535563951866535

theorem tailTrace_791013 : CollatzResearch.WordTrace tailWord_791013 prefixEnd_791013 180519943535563951866535 := by
  unfold tailWord_791013
  simp only [CollatzResearch.WordTrace]
  refine ⟨28850614283302470110105693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19233742855534980073403795 28850614283302470110105693)
  ·
    refine ⟨10818980356238426291289635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28850614283302470110105693 10818980356238426291289635)
    ·
      refine ⟨16228470534357639436934453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10818980356238426291289635 16228470534357639436934453)
      ·
        refine ⟨1521419112596028697212605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16228470534357639436934453 1521419112596028697212605)
        ·
          refine ⟨570532167223510761454727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1521419112596028697212605 570532167223510761454727)
          ·
            refine ⟨855798250835266142182091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570532167223510761454727 855798250835266142182091)
            ·
              refine ⟨1283697376252899213273137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855798250835266142182091 1283697376252899213273137)
              ·
                refine ⟨962773032189674409954853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1283697376252899213273137 962773032189674409954853)
                ·
                  refine ⟨180519943535563951866535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 962773032189674409954853 180519943535563951866535)
                  ·
                    rfl

theorem cell21_791013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_791013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791013 prefixEnd_791013 := by exact prefixLift 791013
  have htrace : WordTrace (prefixWord ++ tailWord_791013) baseStart_791013 baseEnd_791013 := by
    simpa [prefixWord, tailWord_791013, baseEnd_791013] using wordTrace_append hprefix tailTrace_791013
  have hstable : (prefixWord ++ tailWord_791013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791013).length < 2 ^ (prefixWord ++ tailWord_791013).sum := by decide
  have hdescent : baseEnd_791013 < baseStart_791013 := by decide
  rcases family_descends (prefixWord ++ tailWord_791013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791024 : List Nat := [2, 1, 1, 1, 3, 3, 1, 6, 3]
def baseStart_791024 : Nat := 118140960795 + 791024 * 2 ^ 59
def prefixEnd_791024 : Nat := 4983230072969 + 3 ^ 40 * 791024 * 2
def baseEnd_791024 : Nat := 180522453885430377183179

theorem tailTrace_791024 : CollatzResearch.WordTrace tailWord_791024 prefixEnd_791024 180522453885430377183179 := by
  unfold tailWord_791024
  simp only [CollatzResearch.WordTrace]
  refine ⟨14425507743131309494378063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19234010324175079325837417 14425507743131309494378063)
  ·
    refine ⟨21638261614696964241567095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14425507743131309494378063 21638261614696964241567095)
    ·
      refine ⟨32457392422045446362350643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21638261614696964241567095 32457392422045446362350643)
      ·
        refine ⟨48686088633068169543525965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32457392422045446362350643 48686088633068169543525965)
        ·
          refine ⟨18257283237400563578822237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48686088633068169543525965 18257283237400563578822237)
          ·
            refine ⟨6846481214025211342058339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18257283237400563578822237 6846481214025211342058339)
            ·
              refine ⟨10269721821037817013087509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6846481214025211342058339 10269721821037817013087509)
              ·
                refine ⟨481393210361147672488477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10269721821037817013087509 481393210361147672488477)
                ·
                  refine ⟨180522453885430377183179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 481393210361147672488477 180522453885430377183179)
                  ·
                    rfl

theorem cell21_791024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 3].length) (baseStart_791024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791024 prefixEnd_791024 := by exact prefixLift 791024
  have htrace : WordTrace (prefixWord ++ tailWord_791024) baseStart_791024 baseEnd_791024 := by
    simpa [prefixWord, tailWord_791024, baseEnd_791024] using wordTrace_append hprefix tailTrace_791024
  have hstable : (prefixWord ++ tailWord_791024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791024).length < 2 ^ (prefixWord ++ tailWord_791024).sum := by decide
  have hdescent : baseEnd_791024 < baseStart_791024 := by decide
  rcases family_descends (prefixWord ++ tailWord_791024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791069 : List Nat := [1, 4, 2, 2, 1, 4, 7]
def baseStart_791069 : Nat := 118140960795 + 791069 * 2 ^ 59
def prefixEnd_791069 : Nat := 4983230072969 + 3 ^ 40 * 791069 * 2
def baseEnd_791069 : Nat := 20059191499835588770343

theorem tailTrace_791069 : CollatzResearch.WordTrace tailWord_791069 prefixEnd_791069 20059191499835588770343 := by
  unfold tailWord_791069
  simp only [CollatzResearch.WordTrace]
  refine ⟨28852656771099591674144261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19235104514066394449429507 28852656771099591674144261)
  ·
    refine ⟨5409873144581173438902049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28852656771099591674144261 5409873144581173438902049)
    ·
      refine ⟨4057404858435880079176537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5409873144581173438902049 4057404858435880079176537)
      ·
        refine ⟨3043053643826910059382403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4057404858435880079176537 3043053643826910059382403)
        ·
          refine ⟨4564580465740365089073605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3043053643826910059382403 4564580465740365089073605)
          ·
            refine ⟨855858837326318454201301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4564580465740365089073605 855858837326318454201301)
            ·
              refine ⟨20059191499835588770343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 855858837326318454201301 20059191499835588770343)
              ·
                rfl

theorem cell21_791069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 7].length) (baseStart_791069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791069 prefixEnd_791069 := by exact prefixLift 791069
  have htrace : WordTrace (prefixWord ++ tailWord_791069) baseStart_791069 baseEnd_791069 := by
    simpa [prefixWord, tailWord_791069, baseEnd_791069] using wordTrace_append hprefix tailTrace_791069
  have hstable : (prefixWord ++ tailWord_791069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791069).length < 2 ^ (prefixWord ++ tailWord_791069).sum := by decide
  have hdescent : baseEnd_791069 < baseStart_791069 := by decide
  rcases family_descends (prefixWord ++ tailWord_791069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791086 : List Nat := [4, 1, 3, 1, 3, 1, 2, 6]
def baseStart_791086 : Nat := 118140960795 + 791086 * 2 ^ 59
def prefixEnd_791086 : Nat := 4983230072969 + 3 ^ 40 * 791086 * 2
def baseEnd_791086 : Nat := 60178867710044015716573

theorem tailTrace_791086 : CollatzResearch.WordTrace tailWord_791086 prefixEnd_791086 60178867710044015716573 := by
  unfold tailWord_791086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3606659601504750447189139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19235517874692002385008741 3606659601504750447189139)
  ·
    refine ⟨5409989402257125670783709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3606659601504750447189139 5409989402257125670783709)
    ·
      refine ⟨2028746025846422126543891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5409989402257125670783709 2028746025846422126543891)
      ·
        refine ⟨3043119038769633189815837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2028746025846422126543891 3043119038769633189815837)
        ·
          refine ⟨1141169639538612446180939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3043119038769633189815837 1141169639538612446180939)
          ·
            refine ⟨1711754459307918669271409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1141169639538612446180939 1711754459307918669271409)
            ·
              refine ⟨1283815844480939001953557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1711754459307918669271409 1283815844480939001953557)
              ·
                refine ⟨60178867710044015716573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1283815844480939001953557 60178867710044015716573)
                ·
                  rfl

theorem cell21_791086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_791086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791086 prefixEnd_791086 := by exact prefixLift 791086
  have htrace : WordTrace (prefixWord ++ tailWord_791086) baseStart_791086 baseEnd_791086 := by
    simpa [prefixWord, tailWord_791086, baseEnd_791086] using wordTrace_append hprefix tailTrace_791086
  have hstable : (prefixWord ++ tailWord_791086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791086).length < 2 ^ (prefixWord ++ tailWord_791086).sum := by decide
  have hdescent : baseEnd_791086 < baseStart_791086 := by decide
  rcases family_descends (prefixWord ++ tailWord_791086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791204 : List Nat := [2, 3, 1, 2, 2, 1, 2, 8]
def baseStart_791204 : Nat := 118140960795 + 791204 * 2 ^ 59
def prefixEnd_791204 : Nat := 4983230072969 + 3 ^ 40 * 791204 * 2
def baseEnd_791204 : Nat := 60187844112596688060937

theorem tailTrace_791204 : CollatzResearch.WordTrace tailWord_791204 prefixEnd_791204 60187844112596688060937 := by
  unfold tailWord_791204
  simp only [CollatzResearch.WordTrace]
  refine ⟨14428790312805254865154333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19238387083740339820205777 14428790312805254865154333)
  ·
    refine ⟨5410796367301970574432875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14428790312805254865154333 5410796367301970574432875)
    ·
      refine ⟨8116194550952955861649313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5410796367301970574432875 8116194550952955861649313)
      ·
        refine ⟨6087145913214716896236985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8116194550952955861649313 6087145913214716896236985)
        ·
          refine ⟨4565359434911037672177739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6087145913214716896236985 4565359434911037672177739)
          ·
            refine ⟨6848039152366556508266609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4565359434911037672177739 6848039152366556508266609)
            ·
              refine ⟨5136029364274917381199957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6848039152366556508266609 5136029364274917381199957)
              ·
                refine ⟨60187844112596688060937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5136029364274917381199957 60187844112596688060937)
                ·
                  rfl

theorem cell21_791204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 8].length) (baseStart_791204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791204 prefixEnd_791204 := by exact prefixLift 791204
  have htrace : WordTrace (prefixWord ++ tailWord_791204) baseStart_791204 baseEnd_791204 := by
    simpa [prefixWord, tailWord_791204, baseEnd_791204] using wordTrace_append hprefix tailTrace_791204
  have hstable : (prefixWord ++ tailWord_791204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791204).length < 2 ^ (prefixWord ++ tailWord_791204).sum := by decide
  have hdescent : baseEnd_791204 < baseStart_791204 := by decide
  rcases family_descends (prefixWord ++ tailWord_791204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791221 : List Nat := [1, 3, 3, 3, 1, 2, 1, 7]
def baseStart_791221 : Nat := 118140960795 + 791221 * 2 ^ 59
def prefixEnd_791221 : Nat := 4983230072969 + 3 ^ 40 * 791221 * 2
def baseEnd_791221 : Nat := 60189137323133937466481

theorem tailTrace_791221 : CollatzResearch.WordTrace tailWord_791221 prefixEnd_791221 60189137323133937466481 := by
  unfold tailWord_791221
  simp only [CollatzResearch.WordTrace]
  refine ⟨28858200666548921633677517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19238800444365947755785011 28858200666548921633677517)
  ·
    refine ⟨10821825249955845612629069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28858200666548921633677517 10821825249955845612629069)
    ·
      refine ⟨4058184468733442104735901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10821825249955845612629069 4058184468733442104735901)
      ·
        refine ⟨1521819175775040789275963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4058184468733442104735901 1521819175775040789275963)
        ·
          refine ⟨2282728763662561183913945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1521819175775040789275963 2282728763662561183913945)
          ·
            refine ⟨1712046572746920887935459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2282728763662561183913945 1712046572746920887935459)
            ·
              refine ⟨2568069859120381331903189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1712046572746920887935459 2568069859120381331903189)
              ·
                refine ⟨60189137323133937466481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2568069859120381331903189 60189137323133937466481)
                ·
                  rfl

theorem cell21_791221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 7].length) (baseStart_791221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791221 prefixEnd_791221 := by exact prefixLift 791221
  have htrace : WordTrace (prefixWord ++ tailWord_791221) baseStart_791221 baseEnd_791221 := by
    simpa [prefixWord, tailWord_791221, baseEnd_791221] using wordTrace_append hprefix tailTrace_791221
  have hstable : (prefixWord ++ tailWord_791221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791221).length < 2 ^ (prefixWord ++ tailWord_791221).sum := by decide
  have hdescent : baseEnd_791221 < baseStart_791221 := by decide
  rcases family_descends (prefixWord ++ tailWord_791221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791249 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 6]
def baseStart_791249 : Nat := 118140960795 + 791249 * 2 ^ 59
def prefixEnd_791249 : Nat := 4983230072969 + 3 ^ 40 * 791249 * 2
def baseEnd_791249 : Nat := 180573801950879985932719

theorem tailTrace_791249 : CollatzResearch.WordTrace tailWord_791249 prefixEnd_791249 180573801950879985932719 := by
  unfold tailWord_791249
  simp only [CollatzResearch.WordTrace]
  refine ⟨28859221910447482415696801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19239481273631654943797867 28859221910447482415696801)
  ·
    refine ⟨21644416432835611811772601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28859221910447482415696801 21644416432835611811772601)
    ·
      refine ⟨16233312324626708858829451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21644416432835611811772601 16233312324626708858829451)
      ·
        refine ⟨24349968486940063288244177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16233312324626708858829451 24349968486940063288244177)
        ·
          refine ⟨18262476365205047466183133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24349968486940063288244177 18262476365205047466183133)
          ·
            refine ⟨6848428636951892799818675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18262476365205047466183133 6848428636951892799818675)
            ·
              refine ⟨10272642955427839199728013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6848428636951892799818675 10272642955427839199728013)
              ·
                refine ⟨3852241108285439699898005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10272642955427839199728013 3852241108285439699898005)
                ·
                  refine ⟨180573801950879985932719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3852241108285439699898005 180573801950879985932719)
                  ·
                    rfl

theorem cell21_791249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_791249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791249 prefixEnd_791249 := by exact prefixLift 791249
  have htrace : WordTrace (prefixWord ++ tailWord_791249) baseStart_791249 baseEnd_791249 := by
    simpa [prefixWord, tailWord_791249, baseEnd_791249] using wordTrace_append hprefix tailTrace_791249
  have hstable : (prefixWord ++ tailWord_791249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791249).length < 2 ^ (prefixWord ++ tailWord_791249).sum := by decide
  have hdescent : baseEnd_791249 < baseStart_791249 := by decide
  rcases family_descends (prefixWord ++ tailWord_791249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791359 : List Nat := [1, 1, 2, 2, 5, 3, 1, 2, 4]
def baseStart_791359 : Nat := 118140960795 + 791359 * 2 ^ 59
def prefixEnd_791359 : Nat := 4983230072969 + 3 ^ 40 * 791359 * 2
def baseEnd_791359 : Nat := 180598905449544239099161

theorem tailTrace_791359 : CollatzResearch.WordTrace tailWord_791359 prefixEnd_791359 180598905449544239099161 := by
  unfold tailWord_791359
  simp only [CollatzResearch.WordTrace]
  refine ⟨28863233940048971202201131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19242155960032647468134087 28863233940048971202201131)
  ·
    refine ⟨43294850910073456803301697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28863233940048971202201131 43294850910073456803301697)
    ·
      refine ⟨32471138182555092602476273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43294850910073456803301697 32471138182555092602476273)
      ·
        refine ⟨24353353636916319451857205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32471138182555092602476273 24353353636916319451857205)
        ·
          refine ⟨2283126903460904948611613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24353353636916319451857205 2283126903460904948611613)
          ·
            refine ⟨856172588797839355729355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2283126903460904948611613 856172588797839355729355)
            ·
              refine ⟨1284258883196759033594033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856172588797839355729355 1284258883196759033594033)
              ·
                refine ⟨963194162397569275195525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1284258883196759033594033 963194162397569275195525)
                ·
                  refine ⟨180598905449544239099161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 963194162397569275195525 180598905449544239099161)
                  ·
                    rfl

theorem cell21_791359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 4].length) (baseStart_791359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791359 prefixEnd_791359 := by exact prefixLift 791359
  have htrace : WordTrace (prefixWord ++ tailWord_791359) baseStart_791359 baseEnd_791359 := by
    simpa [prefixWord, tailWord_791359, baseEnd_791359] using wordTrace_append hprefix tailTrace_791359
  have hstable : (prefixWord ++ tailWord_791359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791359).length < 2 ^ (prefixWord ++ tailWord_791359).sum := by decide
  have hdescent : baseEnd_791359 < baseStart_791359 := by decide
  rcases family_descends (prefixWord ++ tailWord_791359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791432 : List Nat := [2, 1, 3, 3, 2, 1, 1, 8]
def baseStart_791432 : Nat := 118140960795 + 791432 * 2 ^ 59
def prefixEnd_791432 : Nat := 4983230072969 + 3 ^ 40 * 791432 * 2
def baseEnd_791432 : Nat := 60205188348037444794115

theorem tailTrace_791432 : CollatzResearch.WordTrace tailWord_791432 prefixEnd_791432 60205188348037444794115 := by
  unfold tailWord_791432
  simp only [CollatzResearch.WordTrace]
  refine ⟨14432948234392252334804275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19243930979189669779739033 14432948234392252334804275)
  ·
    refine ⟨21649422351588378502206413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14432948234392252334804275 21649422351588378502206413)
    ·
      refine ⟨8118533381845641938327405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21649422351588378502206413 8118533381845641938327405)
      ·
        refine ⟨3044450018192115726872777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8118533381845641938327405 3044450018192115726872777)
        ·
          refine ⟨2283337513644086795154583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3044450018192115726872777 2283337513644086795154583)
          ·
            refine ⟨3425006270466130192731875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2283337513644086795154583 3425006270466130192731875)
            ·
              refine ⟨5137509405699195289097813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3425006270466130192731875 5137509405699195289097813)
              ·
                refine ⟨60205188348037444794115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5137509405699195289097813 60205188348037444794115)
                ·
                  rfl

theorem cell21_791432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 8].length) (baseStart_791432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791432 prefixEnd_791432 := by exact prefixLift 791432
  have htrace : WordTrace (prefixWord ++ tailWord_791432) baseStart_791432 baseEnd_791432 := by
    simpa [prefixWord, tailWord_791432, baseEnd_791432] using wordTrace_append hprefix tailTrace_791432
  have hstable : (prefixWord ++ tailWord_791432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791432).length < 2 ^ (prefixWord ++ tailWord_791432).sum := by decide
  have hdescent : baseEnd_791432 < baseStart_791432 := by decide
  rcases family_descends (prefixWord ++ tailWord_791432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791480 : List Nat := [2, 1, 2, 1, 2, 5, 1, 4, 3]
def baseStart_791480 : Nat := 118140960795 + 791480 * 2 ^ 59
def prefixEnd_791480 : Nat := 4983230072969 + 3 ^ 40 * 791480 * 2
def baseEnd_791480 : Nat := 180626519298074917582247

theorem tailTrace_791480 : CollatzResearch.WordTrace tailWord_791480 prefixEnd_791480 180626519298074917582247 := by
  unfold tailWord_791480
  simp only [CollatzResearch.WordTrace]
  refine ⟨14433823586305304433677947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19245098115073739244903929 14433823586305304433677947)
  ·
    refine ⟨21650735379457956650516921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14433823586305304433677947 21650735379457956650516921)
    ·
      refine ⟨16238051534593467487887691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21650735379457956650516921 16238051534593467487887691)
      ·
        refine ⟨24357077301890201231831537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16238051534593467487887691 24357077301890201231831537)
        ·
          refine ⟨18267807976417650923873653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24357077301890201231831537 18267807976417650923873653)
          ·
            refine ⟨1712606997789154774113155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18267807976417650923873653 1712606997789154774113155)
            ·
              refine ⟨2568910496683732161169733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1712606997789154774113155 2568910496683732161169733)
              ·
                refine ⟨481670718128199780219325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2568910496683732161169733 481670718128199780219325)
                ·
                  refine ⟨180626519298074917582247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 481670718128199780219325 180626519298074917582247)
                  ·
                    rfl

theorem cell21_791480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 3].length) (baseStart_791480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791480 prefixEnd_791480 := by exact prefixLift 791480
  have htrace : WordTrace (prefixWord ++ tailWord_791480) baseStart_791480 baseEnd_791480 := by
    simpa [prefixWord, tailWord_791480, baseEnd_791480] using wordTrace_append hprefix tailTrace_791480
  have hstable : (prefixWord ++ tailWord_791480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791480).length < 2 ^ (prefixWord ++ tailWord_791480).sum := by decide
  have hdescent : baseEnd_791480 < baseStart_791480 := by decide
  rcases family_descends (prefixWord ++ tailWord_791480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791525 : List Nat := [1, 3, 1, 6, 1, 1, 8]
def baseStart_791525 : Nat := 118140960795 + 791525 * 2 ^ 59
def prefixEnd_791525 : Nat := 4983230072969 + 3 ^ 40 * 791525 * 2
def baseEnd_791525 : Nat := 20070754323462759925795

theorem tailTrace_791525 : CollatzResearch.WordTrace tailWord_791525 prefixEnd_791525 20070754323462759925795 := by
  unfold tailWord_791525
  simp only [CollatzResearch.WordTrace]
  refine ⟨28869288457447581552744029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19246192304965054368496019 28869288457447581552744029)
  ·
    refine ⟨10825983171542843082279011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28869288457447581552744029 10825983171542843082279011)
    ·
      refine ⟨16238974757314264623418517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10825983171542843082279011 16238974757314264623418517)
      ·
        refine ⟨761201941749106154222743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16238974757314264623418517 761201941749106154222743)
        ·
          refine ⟨1141802912623659231334115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 761201941749106154222743 1141802912623659231334115)
          ·
            refine ⟨1712704368935488847001173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1141802912623659231334115 1712704368935488847001173)
            ·
              refine ⟨20070754323462759925795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1712704368935488847001173 20070754323462759925795)
              ·
                rfl

theorem cell21_791525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 8].length) (baseStart_791525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791525 prefixEnd_791525 := by exact prefixLift 791525
  have htrace : WordTrace (prefixWord ++ tailWord_791525) baseStart_791525 baseEnd_791525 := by
    simpa [prefixWord, tailWord_791525, baseEnd_791525] using wordTrace_append hprefix tailTrace_791525
  have hstable : (prefixWord ++ tailWord_791525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791525).length < 2 ^ (prefixWord ++ tailWord_791525).sum := by decide
  have hdescent : baseEnd_791525 < baseStart_791525 := by decide
  rcases family_descends (prefixWord ++ tailWord_791525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791573 : List Nat := [1, 3, 2, 1, 4, 3, 1, 3, 3]
def baseStart_791573 : Nat := 118140960795 + 791573 * 2 ^ 59
def prefixEnd_791573 : Nat := 4983230072969 + 3 ^ 40 * 791573 * 2
def baseEnd_791573 : Nat := 180647743165127422532057

theorem tailTrace_791573 : CollatzResearch.WordTrace tailWord_791573 prefixEnd_791573 180647743165127422532057 := by
  unfold tailWord_791573
  simp only [CollatzResearch.WordTrace]
  refine ⟨28871039161273685750491373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19247359440849123833660915 28871039161273685750491373)
  ·
    refine ⟨10826639685477632156434265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28871039161273685750491373 10826639685477632156434265)
    ·
      refine ⟨8119979764108224117325699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10826639685477632156434265 8119979764108224117325699)
      ·
        refine ⟨12179969646162336175988549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8119979764108224117325699 12179969646162336175988549)
        ·
          refine ⟨2283744308655438032997853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12179969646162336175988549 2283744308655438032997853)
          ·
            refine ⟨856404115745789262374195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2283744308655438032997853 856404115745789262374195)
            ·
              refine ⟨1284606173618683893561293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856404115745789262374195 1284606173618683893561293)
              ·
                refine ⟨481727315107006460085485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1284606173618683893561293 481727315107006460085485)
                ·
                  refine ⟨180647743165127422532057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 481727315107006460085485 180647743165127422532057)
                  ·
                    rfl

theorem cell21_791573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 3].length) (baseStart_791573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791573 prefixEnd_791573 := by exact prefixLift 791573
  have htrace : WordTrace (prefixWord ++ tailWord_791573) baseStart_791573 baseEnd_791573 := by
    simpa [prefixWord, tailWord_791573, baseEnd_791573] using wordTrace_append hprefix tailTrace_791573
  have hstable : (prefixWord ++ tailWord_791573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791573).length < 2 ^ (prefixWord ++ tailWord_791573).sum := by decide
  have hdescent : baseEnd_791573 < baseStart_791573 := by decide
  rcases family_descends (prefixWord ++ tailWord_791573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791604 : List Nat := [2, 5, 1, 2, 1, 1, 4, 1, 4]
def baseStart_791604 : Nat := 118140960795 + 791604 * 2 ^ 59
def prefixEnd_791604 : Nat := 4983230072969 + 3 ^ 40 * 791604 * 2
def baseEnd_791604 : Nat := 180654817787478257515327

theorem tailTrace_791604 : CollatzResearch.WordTrace tailWord_791604 prefixEnd_791604 180654817787478257515327 := by
  unfold tailWord_791604
  simp only [CollatzResearch.WordTrace]
  refine ⟨14436084912080689022434933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19248113216107585363246577 14436084912080689022434933)
  ·
    refine ⟨1353382960507564595853275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14436084912080689022434933 1353382960507564595853275)
    ·
      refine ⟨2030074440761346893779913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1353382960507564595853275 2030074440761346893779913)
      ·
        refine ⟨1522555830571010170334935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2030074440761346893779913 1522555830571010170334935)
        ·
          refine ⟨2283833745856515255502403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1522555830571010170334935 2283833745856515255502403)
          ·
            refine ⟨3425750618784772883253605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2283833745856515255502403 3425750618784772883253605)
            ·
              refine ⟨642328241022144915610051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3425750618784772883253605 642328241022144915610051)
              ·
                refine ⟨963492361533217373415077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642328241022144915610051 963492361533217373415077)
                ·
                  refine ⟨180654817787478257515327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 963492361533217373415077 180654817787478257515327)
                  ·
                    rfl

theorem cell21_791604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_791604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791604 prefixEnd_791604 := by exact prefixLift 791604
  have htrace : WordTrace (prefixWord ++ tailWord_791604) baseStart_791604 baseEnd_791604 := by
    simpa [prefixWord, tailWord_791604, baseEnd_791604] using wordTrace_append hprefix tailTrace_791604
  have hstable : (prefixWord ++ tailWord_791604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791604).length < 2 ^ (prefixWord ++ tailWord_791604).sum := by decide
  have hdescent : baseEnd_791604 < baseStart_791604 := by decide
  rcases family_descends (prefixWord ++ tailWord_791604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791708 : List Nat := [2, 2, 3, 2, 1, 2, 2, 4, 3]
def baseStart_791708 : Nat := 118140960795 + 791708 * 2 ^ 59
def prefixEnd_791708 : Nat := 4983230072969 + 3 ^ 40 * 791708 * 2
def baseEnd_791708 : Nat := 180678552004397187781781

theorem tailTrace_791708 : CollatzResearch.WordTrace tailWord_791708 prefixEnd_791708 180678552004397187781781 := by
  unfold tailWord_791708
  simp only [CollatzResearch.WordTrace]
  refine ⟨14437981507892301903327889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19250642010523069204437185 14437981507892301903327889)
  ·
    refine ⟨10828486130919226427495917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14437981507892301903327889 10828486130919226427495917)
    ·
      refine ⟨4060682299094709910310969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10828486130919226427495917 4060682299094709910310969)
      ·
        refine ⟨3045511724321032432733227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4060682299094709910310969 3045511724321032432733227)
        ·
          refine ⟨4568267586481548649099841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3045511724321032432733227 4568267586481548649099841)
          ·
            refine ⟨3426200689861161486824881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4568267586481548649099841 3426200689861161486824881)
            ·
              refine ⟨2569650517395871115118661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3426200689861161486824881 2569650517395871115118661)
              ·
                refine ⟨481809472011725834084749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2569650517395871115118661 481809472011725834084749)
                ·
                  refine ⟨180678552004397187781781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 481809472011725834084749 180678552004397187781781)
                  ·
                    rfl

theorem cell21_791708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 3].length) (baseStart_791708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791708 prefixEnd_791708 := by exact prefixLift 791708
  have htrace : WordTrace (prefixWord ++ tailWord_791708) baseStart_791708 baseEnd_791708 := by
    simpa [prefixWord, tailWord_791708, baseEnd_791708] using wordTrace_append hprefix tailTrace_791708
  have hstable : (prefixWord ++ tailWord_791708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791708).length < 2 ^ (prefixWord ++ tailWord_791708).sum := by decide
  have hdescent : baseEnd_791708 < baseStart_791708 := by decide
  rcases family_descends (prefixWord ++ tailWord_791708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791767 : List Nat := [1, 1, 3, 2, 1, 2, 2, 6, 3]
def baseStart_791767 : Nat := 118140960795 + 791767 * 2 ^ 59
def prefixEnd_791767 : Nat := 4983230072969 + 3 ^ 40 * 791767 * 2
def baseEnd_791767 : Nat := 180692016608226196298327

theorem tailTrace_791767 : CollatzResearch.WordTrace tailWord_791767 prefixEnd_791767 180692016608226196298327 := by
  unfold tailWord_791767
  simp only [CollatzResearch.WordTrace]
  refine ⟨28878114922570856883053555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19252076615047237922035703 28878114922570856883053555)
  ·
    refine ⟨43317172383856285324580333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28878114922570856883053555 43317172383856285324580333)
    ·
      refine ⟨16243939643946106996717625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43317172383856285324580333 16243939643946106996717625)
      ·
        refine ⟨12182954732959580247538219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16243939643946106996717625 12182954732959580247538219)
        ·
          refine ⟨18274432099439370371307329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12182954732959580247538219 18274432099439370371307329)
          ·
            refine ⟨13705824074579527778480497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18274432099439370371307329 13705824074579527778480497)
            ·
              refine ⟨10279368055934645833860373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13705824074579527778480497 10279368055934645833860373)
              ·
                refine ⟨481845377621936523462205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10279368055934645833860373 481845377621936523462205)
                ·
                  refine ⟨180692016608226196298327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 481845377621936523462205 180692016608226196298327)
                  ·
                    rfl

theorem cell21_791767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 3].length) (baseStart_791767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791767 prefixEnd_791767 := by exact prefixLift 791767
  have htrace : WordTrace (prefixWord ++ tailWord_791767) baseStart_791767 baseEnd_791767 := by
    simpa [prefixWord, tailWord_791767, baseEnd_791767] using wordTrace_append hprefix tailTrace_791767
  have hstable : (prefixWord ++ tailWord_791767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791767).length < 2 ^ (prefixWord ++ tailWord_791767).sum := by decide
  have hdescent : baseEnd_791767 < baseStart_791767 := by decide
  rcases family_descends (prefixWord ++ tailWord_791767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791773 : List Nat := [1, 4, 3, 2, 3, 1, 2, 1, 4]
def baseStart_791773 : Nat := 118140960795 + 791773 * 2 ^ 59
def prefixEnd_791773 : Nat := 4983230072969 + 3 ^ 40 * 791773 * 2
def baseEnd_791773 : Nat := 180693385889971519198315

theorem tailTrace_791773 : CollatzResearch.WordTrace tailWord_791773 prefixEnd_791773 180693385889971519198315 := by
  unfold tailWord_791773
  simp only [CollatzResearch.WordTrace]
  refine ⟨28878333760549119907771973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19252222507032746605181315 28878333760549119907771973)
  ·
    refine ⟨5414687580102959982707245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28878333760549119907771973 5414687580102959982707245)
    ·
      refine ⟨2030507842538609993515217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5414687580102959982707245 2030507842538609993515217)
      ·
        refine ⟨1522880881903957495136413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2030507842538609993515217 1522880881903957495136413)
        ·
          refine ⟨571080330713984060676155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1522880881903957495136413 571080330713984060676155)
          ·
            refine ⟨856620496070976091014233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571080330713984060676155 856620496070976091014233)
            ·
              refine ⟨642465372053232068260675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 856620496070976091014233 642465372053232068260675)
              ·
                refine ⟨963698058079848102391013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642465372053232068260675 963698058079848102391013)
                ·
                  refine ⟨180693385889971519198315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 963698058079848102391013 180693385889971519198315)
                  ·
                    rfl

theorem cell21_791773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_791773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791773 prefixEnd_791773 := by exact prefixLift 791773
  have htrace : WordTrace (prefixWord ++ tailWord_791773) baseStart_791773 baseEnd_791773 := by
    simpa [prefixWord, tailWord_791773, baseEnd_791773] using wordTrace_append hprefix tailTrace_791773
  have hstable : (prefixWord ++ tailWord_791773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791773).length < 2 ^ (prefixWord ++ tailWord_791773).sum := by decide
  have hdescent : baseEnd_791773 < baseStart_791773 := by decide
  rcases family_descends (prefixWord ++ tailWord_791773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791795 : List Nat := [1, 1, 1, 2, 2, 5, 2, 7]
def baseStart_791795 : Nat := 118140960795 + 791795 * 2 ^ 59
def prefixEnd_791795 : Nat := 4983230072969 + 3 ^ 40 * 791795 * 2
def baseEnd_791795 : Nat := 60232802196568123277201

theorem tailTrace_791795 : CollatzResearch.WordTrace tailWord_791795 prefixEnd_791795 60232802196568123277201 := by
  unfold tailWord_791795
  simp only [CollatzResearch.WordTrace]
  refine ⟨28879136166469417665072839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19252757444312945110048559 28879136166469417665072839)
  ·
    refine ⟨43318704249704126497609259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28879136166469417665072839 43318704249704126497609259)
    ·
      refine ⟨64978056374556189746413889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43318704249704126497609259 64978056374556189746413889)
      ·
        refine ⟨48733542280917142309810417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64978056374556189746413889 48733542280917142309810417)
        ·
          refine ⟨36550156710687856732357813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48733542280917142309810417 36550156710687856732357813)
          ·
            refine ⟨3426577191626986568658545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36550156710687856732357813 3426577191626986568658545)
            ·
              refine ⟨2569932893720239926493909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3426577191626986568658545 2569932893720239926493909)
              ·
                refine ⟨60232802196568123277201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2569932893720239926493909 60232802196568123277201)
                ·
                  rfl

theorem cell21_791795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 7].length) (baseStart_791795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791795 prefixEnd_791795 := by exact prefixLift 791795
  have htrace : WordTrace (prefixWord ++ tailWord_791795) baseStart_791795 baseEnd_791795 := by
    simpa [prefixWord, tailWord_791795, baseEnd_791795] using wordTrace_append hprefix tailTrace_791795
  have hstable : (prefixWord ++ tailWord_791795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791795).length < 2 ^ (prefixWord ++ tailWord_791795).sum := by decide
  have hdescent : baseEnd_791795 < baseStart_791795 := by decide
  rcases family_descends (prefixWord ++ tailWord_791795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791871 : List Nat := [1, 1, 2, 2, 4, 3, 8]
def baseStart_791871 : Nat := 118140960795 + 791871 * 2 ^ 59
def prefixEnd_791871 : Nat := 4983230072969 + 3 ^ 40 * 791871 * 2
def baseEnd_791871 : Nat := 20079527869460569618309

theorem tailTrace_791871 : CollatzResearch.WordTrace tailWord_791871 prefixEnd_791871 20079527869460569618309 := by
  unfold tailWord_791871
  simp only [CollatzResearch.WordTrace]
  refine ⟨28881908114194082644839467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19254605409462721763226311 28881908114194082644839467)
  ·
    refine ⟨43322862171291123967259201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28881908114194082644839467 43322862171291123967259201)
    ·
      refine ⟨32492146628468342975444401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43322862171291123967259201 32492146628468342975444401)
      ·
        refine ⟨24369109971351257231583301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32492146628468342975444401 24369109971351257231583301)
        ·
          refine ⟨4569208119628360730921869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24369109971351257231583301 4569208119628360730921869)
          ·
            refine ⟨1713453044860635274095701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4569208119628360730921869 1713453044860635274095701)
            ·
              refine ⟨20079527869460569618309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1713453044860635274095701 20079527869460569618309)
              ·
                rfl

theorem cell21_791871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 8].length) (baseStart_791871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791871 prefixEnd_791871 := by exact prefixLift 791871
  have htrace : WordTrace (prefixWord ++ tailWord_791871) baseStart_791871 baseEnd_791871 := by
    simpa [prefixWord, tailWord_791871, baseEnd_791871] using wordTrace_append hprefix tailTrace_791871
  have hstable : (prefixWord ++ tailWord_791871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791871).length < 2 ^ (prefixWord ++ tailWord_791871).sum := by decide
  have hdescent : baseEnd_791871 < baseStart_791871 := by decide
  rcases family_descends (prefixWord ++ tailWord_791871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791933 : List Nat := [1, 4, 1, 1, 2, 2, 2, 4, 4]
def baseStart_791933 : Nat := 118140960795 + 791933 * 2 ^ 59
def prefixEnd_791933 : Nat := 4983230072969 + 3 ^ 40 * 791933 * 2
def baseEnd_791933 : Nat := 180729900069846796531321

theorem tailTrace_791933 : CollatzResearch.WordTrace tailWord_791933 prefixEnd_791933 180729900069846796531321 := by
  unfold tailWord_791933
  simp only [CollatzResearch.WordTrace]
  refine ⟨28884169439969467233596453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19256112959979644822397635 28884169439969467233596453)
  ·
    refine ⟨5415781769994275106299335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28884169439969467233596453 5415781769994275106299335)
    ·
      refine ⟨8123672654991412659449003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5415781769994275106299335 8123672654991412659449003)
      ·
        refine ⟨12185508982487118989173505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8123672654991412659449003 12185508982487118989173505)
        ·
          refine ⟨9139131736865339241880129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12185508982487118989173505 9139131736865339241880129)
          ·
            refine ⟨6854348802649004431410097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9139131736865339241880129 6854348802649004431410097)
            ·
              refine ⟨5140761601986753323557573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6854348802649004431410097 5140761601986753323557573)
              ·
                refine ⟨963892800372516248167045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5140761601986753323557573 963892800372516248167045)
                ·
                  refine ⟨180729900069846796531321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 963892800372516248167045 180729900069846796531321)
                  ·
                    rfl

theorem cell21_791933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_791933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791933 prefixEnd_791933 := by exact prefixLift 791933
  have htrace : WordTrace (prefixWord ++ tailWord_791933) baseStart_791933 baseEnd_791933 := by
    simpa [prefixWord, tailWord_791933, baseEnd_791933] using wordTrace_append hprefix tailTrace_791933
  have hstable : (prefixWord ++ tailWord_791933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791933).length < 2 ^ (prefixWord ++ tailWord_791933).sum := by decide
  have hdescent : baseEnd_791933 < baseStart_791933 := by decide
  rcases family_descends (prefixWord ++ tailWord_791933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791947 : List Nat := [1, 1, 1, 1, 4, 3, 4, 6]
def baseStart_791947 : Nat := 118140960795 + 791947 * 2 ^ 59
def prefixEnd_791947 : Nat := 4983230072969 + 3 ^ 40 * 791947 * 2
def baseEnd_791947 : Nat := 60244365020195294432653

theorem tailTrace_791947 : CollatzResearch.WordTrace tailWord_791947 prefixEnd_791947 60244365020195294432653 := by
  unfold tailWord_791947
  simp only [CollatzResearch.WordTrace]
  refine ⟨28884680061918747624606095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19256453374612498416404063 28884680061918747624606095)
  ·
    refine ⟨43327020092878121436909143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28884680061918747624606095 43327020092878121436909143)
    ·
      refine ⟨64990530139317182155363715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43327020092878121436909143 64990530139317182155363715)
      ·
        refine ⟨97485795208975773233045573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64990530139317182155363715 97485795208975773233045573)
        ·
          refine ⟨18278586601682957481196045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97485795208975773233045573 18278586601682957481196045)
          ·
            refine ⟨6854469975631109055448517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18278586601682957481196045 6854469975631109055448517)
            ·
              refine ⟨1285213120430832947896597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6854469975631109055448517 1285213120430832947896597)
              ·
                refine ⟨60244365020195294432653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1285213120430832947896597 60244365020195294432653)
                ·
                  rfl

theorem cell21_791947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 6].length) (baseStart_791947 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791947 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791947 prefixEnd_791947 := by exact prefixLift 791947
  have htrace : WordTrace (prefixWord ++ tailWord_791947) baseStart_791947 baseEnd_791947 := by
    simpa [prefixWord, tailWord_791947, baseEnd_791947] using wordTrace_append hprefix tailTrace_791947
  have hstable : (prefixWord ++ tailWord_791947).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791947).length < 2 ^ (prefixWord ++ tailWord_791947).sum := by decide
  have hdescent : baseEnd_791947 < baseStart_791947 := by decide
  rcases family_descends (prefixWord ++ tailWord_791947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_791992 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 6]
def baseStart_791992 : Nat := 118140960795 + 791992 * 2 ^ 59
def prefixEnd_791992 : Nat := 4983230072969 + 3 ^ 40 * 791992 * 2
def baseEnd_791992 : Nat := 180743364673675805047867

theorem tailTrace_791992 : CollatzResearch.WordTrace tailWord_791992 prefixEnd_791992 180743364673675805047867 := by
  unfold tailWord_791992
  simp only [CollatzResearch.WordTrace]
  refine ⟨14443160673377860154997115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19257547564503813539996153 14443160673377860154997115)
  ·
    refine ⟨21664741010066790232495673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14443160673377860154997115 21664741010066790232495673)
    ·
      refine ⟨16248555757550092674371755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21664741010066790232495673 16248555757550092674371755)
      ·
        refine ⟨24372833636325139011557633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16248555757550092674371755 24372833636325139011557633)
        ·
          refine ⟨18279625227243854258668225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24372833636325139011557633 18279625227243854258668225)
          ·
            refine ⟨13709718920432890694001169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18279625227243854258668225 13709718920432890694001169)
            ·
              refine ⟨10282289190324668020500877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13709718920432890694001169 10282289190324668020500877)
              ·
                refine ⟨3855858446371750507687829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10282289190324668020500877 3855858446371750507687829)
                ·
                  refine ⟨180743364673675805047867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3855858446371750507687829 180743364673675805047867)
                  ·
                    rfl

theorem cell21_791992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_791992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_791992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_791992 prefixEnd_791992 := by exact prefixLift 791992
  have htrace : WordTrace (prefixWord ++ tailWord_791992) baseStart_791992 baseEnd_791992 := by
    simpa [prefixWord, tailWord_791992, baseEnd_791992] using wordTrace_append hprefix tailTrace_791992
  have hstable : (prefixWord ++ tailWord_791992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_791992).length < 2 ^ (prefixWord ++ tailWord_791992).sum := by decide
  have hdescent : baseEnd_791992 < baseStart_791992 := by decide
  rcases family_descends (prefixWord ++ tailWord_791992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792150 : List Nat := [5, 2, 2, 2, 2, 8]
def baseStart_792150 : Nat := 118140960795 + 792150 * 2 ^ 59
def prefixEnd_792150 : Nat := 4983230072969 + 3 ^ 40 * 792150 * 2
def baseEnd_792150 : Nat := 6695534163937134867193

theorem tailTrace_792150 : CollatzResearch.WordTrace tailWord_792150 prefixEnd_792150 6695534163937134867193 := by
  unfold tailWord_792150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1805755255011457080890369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19261389386788875529497269 1805755255011457080890369)
  ·
    refine ⟨1354316441258592810667777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1805755255011457080890369 1354316441258592810667777)
    ·
      refine ⟨1015737330943944608000833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1354316441258592810667777 1015737330943944608000833)
      ·
        refine ⟨761802998207958456000625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1015737330943944608000833 761802998207958456000625)
        ·
          refine ⟨571352248655968842000469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 761802998207958456000625 571352248655968842000469)
          ·
            refine ⟨6695534163937134867193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 571352248655968842000469 6695534163937134867193)
            ·
              rfl

theorem cell21_792150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 8].length) (baseStart_792150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792150 prefixEnd_792150 := by exact prefixLift 792150
  have htrace : WordTrace (prefixWord ++ tailWord_792150) baseStart_792150 baseEnd_792150 := by
    simpa [prefixWord, tailWord_792150, baseEnd_792150] using wordTrace_append hprefix tailTrace_792150
  have hstable : (prefixWord ++ tailWord_792150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792150).length < 2 ^ (prefixWord ++ tailWord_792150).sum := by decide
  have hdescent : baseEnd_792150 < baseStart_792150 := by decide
  rcases family_descends (prefixWord ++ tailWord_792150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792161 : List Nat := [1, 2, 3, 1, 1, 3, 4, 2, 4]
def baseStart_792161 : Nat := 118140960795 + 792161 * 2 ^ 59
def prefixEnd_792161 : Nat := 4983230072969 + 3 ^ 40 * 792161 * 2
def baseEnd_792161 : Nat := 180781932776169066730855

theorem tailTrace_792161 : CollatzResearch.WordTrace tailWord_792161 prefixEnd_792161 180781932776169066730855 := by
  unfold tailWord_792161
  simp only [CollatzResearch.WordTrace]
  refine ⟨28892485283143462172896337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19261656855428974781930891 28892485283143462172896337)
  ·
    refine ⟨21669363962357596629672253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28892485283143462172896337 21669363962357596629672253)
    ·
      refine ⟨8126011485884098736127095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21669363962357596629672253 8126011485884098736127095)
      ·
        refine ⟨12189017228826148104190643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8126011485884098736127095 12189017228826148104190643)
        ·
          refine ⟨18283525843239222156285965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12189017228826148104190643 18283525843239222156285965)
          ·
            refine ⟨6856322191214708308607237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18283525843239222156285965 6856322191214708308607237)
            ·
              refine ⟨1285560410852757807863857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6856322191214708308607237 1285560410852757807863857)
              ·
                refine ⟨964170308139568355897893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1285560410852757807863857 964170308139568355897893)
                ·
                  refine ⟨180781932776169066730855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 964170308139568355897893 180781932776169066730855)
                  ·
                    rfl

theorem cell21_792161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_792161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792161 prefixEnd_792161 := by exact prefixLift 792161
  have htrace : WordTrace (prefixWord ++ tailWord_792161) baseStart_792161 baseEnd_792161 := by
    simpa [prefixWord, tailWord_792161, baseEnd_792161] using wordTrace_append hprefix tailTrace_792161
  have hstable : (prefixWord ++ tailWord_792161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792161).length < 2 ^ (prefixWord ++ tailWord_792161).sum := by decide
  have hdescent : baseEnd_792161 < baseStart_792161 := by decide
  rcases family_descends (prefixWord ++ tailWord_792161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792164 : List Nat := [2, 3, 1, 1, 2, 3, 4, 2, 3]
def baseStart_792164 : Nat := 118140960795 + 792164 * 2 ^ 59
def prefixEnd_792164 : Nat := 4983230072969 + 3 ^ 40 * 792164 * 2
def baseEnd_792164 : Nat := 180782617417041728180849

theorem tailTrace_792164 : CollatzResearch.WordTrace tailWord_792164 prefixEnd_792164 180782617417041728180849 := by
  unfold tailWord_792164
  simp only [CollatzResearch.WordTrace]
  refine ⟨14446297351066296842627773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19261729801421729123503697 14446297351066296842627773)
  ·
    refine ⟨5417361506649861315985415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14446297351066296842627773 5417361506649861315985415)
    ·
      refine ⟨8126042259974791973978123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5417361506649861315985415 8126042259974791973978123)
      ·
        refine ⟨12189063389962187960967185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8126042259974791973978123 12189063389962187960967185)
        ·
          refine ⟨9141797542471640970725389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12189063389962187960967185 9141797542471640970725389)
          ·
            refine ⟨3428174078426865364022021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9141797542471640970725389 3428174078426865364022021)
            ·
              refine ⟨642782639705037255754129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3428174078426865364022021 642782639705037255754129)
              ·
                refine ⟨482086979778777941815597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 642782639705037255754129 482086979778777941815597)
                ·
                  refine ⟨180782617417041728180849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 482086979778777941815597 180782617417041728180849)
                  ·
                    rfl

theorem cell21_792164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_792164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792164 prefixEnd_792164 := by exact prefixLift 792164
  have htrace : WordTrace (prefixWord ++ tailWord_792164) baseStart_792164 baseEnd_792164 := by
    simpa [prefixWord, tailWord_792164, baseEnd_792164] using wordTrace_append hprefix tailTrace_792164
  have hstable : (prefixWord ++ tailWord_792164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792164).length < 2 ^ (prefixWord ++ tailWord_792164).sum := by decide
  have hdescent : baseEnd_792164 < baseStart_792164 := by decide
  rcases family_descends (prefixWord ++ tailWord_792164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792212 : List Nat := [2, 4, 2, 2, 3, 1, 1, 2, 4]
def baseStart_792212 : Nat := 118140960795 + 792212 * 2 ^ 59
def prefixEnd_792212 : Nat := 4983230072969 + 3 ^ 40 * 792212 * 2
def baseEnd_792212 : Nat := 180793571671004311380751

theorem tailTrace_792212 : CollatzResearch.WordTrace tailWord_792212 prefixEnd_792212 180793571671004311380751 := by
  unfold tailWord_792212
  simp only [CollatzResearch.WordTrace]
  refine ⟨14447172702979348941501445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19262896937305798588668593 14447172702979348941501445)
  ·
    refine ⟨2708844881808627926531521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14447172702979348941501445 2708844881808627926531521)
    ·
      refine ⟨2031633661356470944898641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2708844881808627926531521 2031633661356470944898641)
      ·
        refine ⟨1523725246017353208673981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2031633661356470944898641 1523725246017353208673981)
        ·
          refine ⟨571396967256507453252743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1523725246017353208673981 571396967256507453252743)
          ·
            refine ⟨857095450884761179879115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571396967256507453252743 857095450884761179879115)
            ·
              refine ⟨1285643176327141769818673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857095450884761179879115 1285643176327141769818673)
              ·
                refine ⟨964232382245356327364005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1285643176327141769818673 964232382245356327364005)
                ·
                  refine ⟨180793571671004311380751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 964232382245356327364005 180793571671004311380751)
                  ·
                    rfl

theorem cell21_792212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_792212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792212 prefixEnd_792212 := by exact prefixLift 792212
  have htrace : WordTrace (prefixWord ++ tailWord_792212) baseStart_792212 baseEnd_792212 := by
    simpa [prefixWord, tailWord_792212, baseEnd_792212] using wordTrace_append hprefix tailTrace_792212
  have hstable : (prefixWord ++ tailWord_792212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792212).length < 2 ^ (prefixWord ++ tailWord_792212).sum := by decide
  have hdescent : baseEnd_792212 < baseStart_792212 := by decide
  rcases family_descends (prefixWord ++ tailWord_792212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792268 : List Nat := [2, 2, 1, 5, 2, 2, 7]
def baseStart_792268 : Nat := 118140960795 + 792268 * 2 ^ 59
def prefixEnd_792268 : Nat := 4983230072969 + 3 ^ 40 * 792268 * 2
def baseEnd_792268 : Nat := 20089594625995628716367

theorem tailTrace_792268 : CollatzResearch.WordTrace tailWord_792268 prefixEnd_792268 20089594625995628716367 := by
  unfold tailWord_792268
  simp only [CollatzResearch.WordTrace]
  refine ⟨14448193946877909723520729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19264258595837212964694305 14448193946877909723520729)
  ·
    refine ⟨10836145460158432292640547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14448193946877909723520729 10836145460158432292640547)
    ·
      refine ⟨16254218190237648438960821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10836145460158432292640547 16254218190237648438960821)
      ·
        refine ⟨1523832955334779541152577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16254218190237648438960821 1523832955334779541152577)
        ·
          refine ⟨1142874716501084655864433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1523832955334779541152577 1142874716501084655864433)
          ·
            refine ⟨857156037375813491898325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1142874716501084655864433 857156037375813491898325)
            ·
              refine ⟨20089594625995628716367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 857156037375813491898325 20089594625995628716367)
              ·
                rfl

theorem cell21_792268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 7].length) (baseStart_792268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792268 prefixEnd_792268 := by exact prefixLift 792268
  have htrace : WordTrace (prefixWord ++ tailWord_792268) baseStart_792268 baseEnd_792268 := by
    simpa [prefixWord, tailWord_792268, baseEnd_792268] using wordTrace_append hprefix tailTrace_792268
  have hstable : (prefixWord ++ tailWord_792268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792268).length < 2 ^ (prefixWord ++ tailWord_792268).sum := by decide
  have hdescent : baseEnd_792268 < baseStart_792268 := by decide
  rcases family_descends (prefixWord ++ tailWord_792268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792282 : List Nat := [3, 1, 1, 2, 2, 3, 3, 1, 5]
def baseStart_792282 : Nat := 118140960795 + 792282 * 2 ^ 59
def prefixEnd_792282 : Nat := 4983230072969 + 3 ^ 40 * 792282 * 2
def baseEnd_792282 : Nat := 180809546624699745213941

theorem tailTrace_792282 : CollatzResearch.WordTrace tailWord_792282 prefixEnd_792282 180809546624699745213941 := by
  unfold tailWord_792282
  simp only [CollatzResearch.WordTrace]
  refine ⟨7224224628926274959512775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19264599010470066558700733 7224224628926274959512775)
  ·
    refine ⟨10836336943389412439269163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7224224628926274959512775 10836336943389412439269163)
    ·
      refine ⟨16254505415084118658903745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10836336943389412439269163 16254505415084118658903745)
      ·
        refine ⟨12190879061313088994177809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16254505415084118658903745 12190879061313088994177809)
        ·
          refine ⟨9143159295984816745633357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12190879061313088994177809 9143159295984816745633357)
          ·
            refine ⟨3428684735994306279612509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9143159295984816745633357 3428684735994306279612509)
            ·
              refine ⟨1285756775997864854854691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3428684735994306279612509 1285756775997864854854691)
              ·
                refine ⟨1928635163996797282282037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1285756775997864854854691 1928635163996797282282037)
                ·
                  refine ⟨180809546624699745213941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1928635163996797282282037 180809546624699745213941)
                  ·
                    rfl

theorem cell21_792282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_792282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792282 prefixEnd_792282 := by exact prefixLift 792282
  have htrace : WordTrace (prefixWord ++ tailWord_792282) baseStart_792282 baseEnd_792282 := by
    simpa [prefixWord, tailWord_792282, baseEnd_792282] using wordTrace_append hprefix tailTrace_792282
  have hstable : (prefixWord ++ tailWord_792282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792282).length < 2 ^ (prefixWord ++ tailWord_792282).sum := by decide
  have hdescent : baseEnd_792282 < baseStart_792282 := by decide
  rcases family_descends (prefixWord ++ tailWord_792282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792285 : List Nat := [1, 4, 3, 3, 1, 1, 2, 6]
def baseStart_792285 : Nat := 118140960795 + 792285 * 2 ^ 59
def prefixEnd_792285 : Nat := 4983230072969 + 3 ^ 40 * 792285 * 2
def baseEnd_792285 : Nat := 60270077088524135554645

theorem tailTrace_792285 : CollatzResearch.WordTrace tailWord_792285 prefixEnd_792285 60270077088524135554645 := by
  unfold tailWord_792285
  simp only [CollatzResearch.WordTrace]
  refine ⟨28897007934694231350410309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19264671956462820900273539 28897007934694231350410309)
  ·
    refine ⟨5418188987755168378201933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28897007934694231350410309 5418188987755168378201933)
    ·
      refine ⟨2031820870408188141825725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5418188987755168378201933 2031820870408188141825725)
      ·
        refine ⟨761932826403070553184647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2031820870408188141825725 761932826403070553184647)
        ·
          refine ⟨1142899239604605829776971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 761932826403070553184647 1142899239604605829776971)
          ·
            refine ⟨1714348859406908744665457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142899239604605829776971 1714348859406908744665457)
            ·
              refine ⟨1285761644555181558499093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1714348859406908744665457 1285761644555181558499093)
              ·
                refine ⟨60270077088524135554645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1285761644555181558499093 60270077088524135554645)
                ·
                  rfl

theorem cell21_792285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 6].length) (baseStart_792285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792285 prefixEnd_792285 := by exact prefixLift 792285
  have htrace : WordTrace (prefixWord ++ tailWord_792285) baseStart_792285 baseEnd_792285 := by
    simpa [prefixWord, tailWord_792285, baseEnd_792285] using wordTrace_append hprefix tailTrace_792285
  have hstable : (prefixWord ++ tailWord_792285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792285).length < 2 ^ (prefixWord ++ tailWord_792285).sum := by decide
  have hdescent : baseEnd_792285 < baseStart_792285 := by decide
  rcases family_descends (prefixWord ++ tailWord_792285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792327 : List Nat := [1, 1, 4, 4, 2, 9]
def baseStart_792327 : Nat := 118140960795 + 792327 * 2 ^ 59
def prefixEnd_792327 : Nat := 4983230072969 + 3 ^ 40 * 792327 * 2
def baseEnd_792327 : Nat := 6697030231029246924587

theorem tailTrace_792327 : CollatzResearch.WordTrace tailWord_792327 prefixEnd_792327 6697030231029246924587 := by
  unfold tailWord_792327
  simp only [CollatzResearch.WordTrace]
  refine ⟨28898539800542072523439235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19265693200361381682292823 28898539800542072523439235)
  ·
    refine ⟨43347809700813108785158853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28898539800542072523439235 43347809700813108785158853)
    ·
      refine ⟨8127714318902457897217285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43347809700813108785158853 8127714318902457897217285)
      ·
        refine ⟨1523946434794210855728241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8127714318902457897217285 1523946434794210855728241)
        ·
          refine ⟨1142959826095658141796181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1523946434794210855728241 1142959826095658141796181)
          ·
            refine ⟨6697030231029246924587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1142959826095658141796181 6697030231029246924587)
            ·
              rfl

theorem cell21_792327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 9].length) (baseStart_792327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792327 prefixEnd_792327 := by exact prefixLift 792327
  have htrace : WordTrace (prefixWord ++ tailWord_792327) baseStart_792327 baseEnd_792327 := by
    simpa [prefixWord, tailWord_792327, baseEnd_792327] using wordTrace_append hprefix tailTrace_792327
  have hstable : (prefixWord ++ tailWord_792327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792327).length < 2 ^ (prefixWord ++ tailWord_792327).sum := by decide
  have hdescent : baseEnd_792327 < baseStart_792327 := by decide
  rcases family_descends (prefixWord ++ tailWord_792327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792417 : List Nat := [1, 2, 3, 1, 1, 1, 3, 4, 5]
def baseStart_792417 : Nat := 118140960795 + 792417 * 2 ^ 59
def prefixEnd_792417 : Nat := 4983230072969 + 3 ^ 40 * 792417 * 2
def baseEnd_792417 : Nat := 180840355463969510463665

theorem tailTrace_792417 : CollatzResearch.WordTrace tailWord_792417 prefixEnd_792417 180840355463969510463665 := by
  unfold tailWord_792417
  simp only [CollatzResearch.WordTrace]
  refine ⟨28901822370216017894215505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19267881580144011929477003 28901822370216017894215505)
  ·
    refine ⟨21676366777662013420661629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28901822370216017894215505 21676366777662013420661629)
    ·
      refine ⟨8128637541623255032748111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21676366777662013420661629 8128637541623255032748111)
      ·
        refine ⟨12192956312434882549122167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8128637541623255032748111 12192956312434882549122167)
        ·
          refine ⟨18289434468652323823683251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12192956312434882549122167 18289434468652323823683251)
          ·
            refine ⟨27434151702978485735524877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18289434468652323823683251 27434151702978485735524877)
            ·
              refine ⟨10287806888616932150821829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27434151702978485735524877 10287806888616932150821829)
              ·
                refine ⟨1928963791615674778279093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10287806888616932150821829 1928963791615674778279093)
                ·
                  refine ⟨180840355463969510463665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1928963791615674778279093 180840355463969510463665)
                  ·
                    rfl

theorem cell21_792417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_792417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792417 prefixEnd_792417 := by exact prefixLift 792417
  have htrace : WordTrace (prefixWord ++ tailWord_792417) baseStart_792417 baseEnd_792417 := by
    simpa [prefixWord, tailWord_792417, baseEnd_792417] using wordTrace_append hprefix tailTrace_792417
  have hstable : (prefixWord ++ tailWord_792417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792417).length < 2 ^ (prefixWord ++ tailWord_792417).sum := by decide
  have hdescent : baseEnd_792417 < baseStart_792417 := by decide
  rcases family_descends (prefixWord ++ tailWord_792417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792426 : List Nat := [3, 1, 3, 4, 2, 1, 1, 3, 3]
def baseStart_792426 : Nat := 118140960795 + 792426 * 2 ^ 59
def prefixEnd_792426 : Nat := 4983230072969 + 3 ^ 40 * 792426 * 2
def baseEnd_792426 : Nat := 180842409386587494813647

theorem tailTrace_792426 : CollatzResearch.WordTrace tailWord_792426 prefixEnd_792426 180842409386587494813647 := by
  unfold tailWord_792426
  simp only [CollatzResearch.WordTrace]
  refine ⟨7225537656795853107823283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19268100418122274954195421 7225537656795853107823283)
  ·
    refine ⟨10838306485193779661734925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7225537656795853107823283 10838306485193779661734925)
    ·
      refine ⟨4064364931947667373150597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10838306485193779661734925 4064364931947667373150597)
      ·
        refine ⟨762068424740187632465737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4064364931947667373150597 762068424740187632465737)
        ·
          refine ⟨571551318555140724349303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 762068424740187632465737 571551318555140724349303)
          ·
            refine ⟨857326977832711086523955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571551318555140724349303 857326977832711086523955)
            ·
              refine ⟨1285990466749066629785933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857326977832711086523955 1285990466749066629785933)
              ·
                refine ⟨482246425030899986169725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1285990466749066629785933 482246425030899986169725)
                ·
                  refine ⟨180842409386587494813647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 482246425030899986169725 180842409386587494813647)
                  ·
                    rfl

theorem cell21_792426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_792426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792426 prefixEnd_792426 := by exact prefixLift 792426
  have htrace : WordTrace (prefixWord ++ tailWord_792426) baseStart_792426 baseEnd_792426 := by
    simpa [prefixWord, tailWord_792426, baseEnd_792426] using wordTrace_append hprefix tailTrace_792426
  have hstable : (prefixWord ++ tailWord_792426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792426).length < 2 ^ (prefixWord ++ tailWord_792426).sum := by decide
  have hdescent : baseEnd_792426 < baseStart_792426 := by decide
  rcases family_descends (prefixWord ++ tailWord_792426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792448 : List Nat := [2, 1, 1, 2, 1, 2, 4, 4, 4]
def baseStart_792448 : Nat := 118140960795 + 792448 * 2 ^ 59
def prefixEnd_792448 : Nat := 4983230072969 + 3 ^ 40 * 792448 * 2
def baseEnd_792448 : Nat := 180847430086320345446935

theorem tailTrace_792448 : CollatzResearch.WordTrace tailWord_792448 prefixEnd_792448 180847430086320345446935 := by
  unfold tailWord_792448
  simp only [CollatzResearch.WordTrace]
  refine ⟨14451476516551855094296999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19268635355402473459062665 14451476516551855094296999)
  ·
    refine ⟨21677214774827782641445499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14451476516551855094296999 21677214774827782641445499)
    ·
      refine ⟨32515822162241673962168249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21677214774827782641445499 32515822162241673962168249)
      ·
        refine ⟨24386866621681255471626187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32515822162241673962168249 24386866621681255471626187)
        ·
          refine ⟨36580299932521883207439281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24386866621681255471626187 36580299932521883207439281)
          ·
            refine ⟨27435224949391412405579461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36580299932521883207439281 27435224949391412405579461)
            ·
              refine ⟨5144104678010889826046149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27435224949391412405579461 5144104678010889826046149)
              ·
                refine ⟨964519627127041842383653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5144104678010889826046149 964519627127041842383653)
                ·
                  refine ⟨180847430086320345446935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 964519627127041842383653 180847430086320345446935)
                  ·
                    rfl

theorem cell21_792448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_792448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792448 prefixEnd_792448 := by exact prefixLift 792448
  have htrace : WordTrace (prefixWord ++ tailWord_792448) baseStart_792448 baseEnd_792448 := by
    simpa [prefixWord, tailWord_792448, baseEnd_792448] using wordTrace_append hprefix tailTrace_792448
  have hstable : (prefixWord ++ tailWord_792448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792448).length < 2 ^ (prefixWord ++ tailWord_792448).sum := by decide
  have hdescent : baseEnd_792448 < baseStart_792448 := by decide
  rcases family_descends (prefixWord ++ tailWord_792448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792465 : List Nat := [1, 2, 2, 1, 1, 1, 8, 1, 4]
def baseStart_792465 : Nat := 118140960795 + 792465 * 2 ^ 59
def prefixEnd_792465 : Nat := 4983230072969 + 3 ^ 40 * 792465 * 2
def baseEnd_792465 : Nat := 180851309717932093663567

theorem tailTrace_792465 : CollatzResearch.WordTrace tailWord_792465 prefixEnd_792465 180851309717932093663567 := by
  unfold tailWord_792465
  simp only [CollatzResearch.WordTrace]
  refine ⟨28903573074042122091962849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19269048716028081394641899 28903573074042122091962849)
  ·
    refine ⟨21677679805531591568972137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28903573074042122091962849 21677679805531591568972137)
    ·
      refine ⟨16258259854148693676729103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21677679805531591568972137 16258259854148693676729103)
      ·
        refine ⟨24387389781223040515093655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16258259854148693676729103 24387389781223040515093655)
        ·
          refine ⟨36581084671834560772640483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24387389781223040515093655 36581084671834560772640483)
          ·
            refine ⟨54871627007751841158960725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36581084671834560772640483 54871627007751841158960725)
            ·
              refine ⟨643026878997091888581571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 54871627007751841158960725 643026878997091888581571)
              ·
                refine ⟨964540318495637832872357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643026878997091888581571 964540318495637832872357)
                ·
                  refine ⟨180851309717932093663567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 964540318495637832872357 180851309717932093663567)
                  ·
                    rfl

theorem cell21_792465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 4].length) (baseStart_792465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792465 prefixEnd_792465 := by exact prefixLift 792465
  have htrace : WordTrace (prefixWord ++ tailWord_792465) baseStart_792465 baseEnd_792465 := by
    simpa [prefixWord, tailWord_792465, baseEnd_792465] using wordTrace_append hprefix tailTrace_792465
  have hstable : (prefixWord ++ tailWord_792465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792465).length < 2 ^ (prefixWord ++ tailWord_792465).sum := by decide
  have hdescent : baseEnd_792465 < baseStart_792465 := by decide
  rcases family_descends (prefixWord ++ tailWord_792465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792558 : List Nat := [4, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_792558 : Nat := 118140960795 + 792558 * 2 ^ 59
def prefixEnd_792558 : Nat := 4983230072969 + 3 ^ 40 * 792558 * 2
def baseEnd_792558 : Nat := 180872533584984598613377

theorem tailTrace_792558 : CollatzResearch.WordTrace tailWord_792558 prefixEnd_792558 180872533584984598613377 := by
  unfold tailWord_792558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3613370632838149871887291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19271310041803465983398885 3613370632838149871887291)
  ·
    refine ⟨5420055949257224807830937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3613370632838149871887291 5420055949257224807830937)
    ·
      refine ⟨4065041961942918605873203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5420055949257224807830937 4065041961942918605873203)
      ·
        refine ⟨6097562942914377908809805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4065041961942918605873203 6097562942914377908809805)
        ·
          refine ⟨2286586103592891715803677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6097562942914377908809805 2286586103592891715803677)
          ·
            refine ⟨857469788847334393426379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2286586103592891715803677 857469788847334393426379)
            ·
              refine ⟨1286204683271001590139569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857469788847334393426379 1286204683271001590139569)
              ·
                refine ⟨964653512453251192604677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286204683271001590139569 964653512453251192604677)
                ·
                  refine ⟨180872533584984598613377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 964653512453251192604677 180872533584984598613377)
                  ·
                    rfl

theorem cell21_792558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_792558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792558 prefixEnd_792558 := by exact prefixLift 792558
  have htrace : WordTrace (prefixWord ++ tailWord_792558) baseStart_792558 baseEnd_792558 := by
    simpa [prefixWord, tailWord_792558, baseEnd_792558] using wordTrace_append hprefix tailTrace_792558
  have hstable : (prefixWord ++ tailWord_792558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792558).length < 2 ^ (prefixWord ++ tailWord_792558).sum := by decide
  have hdescent : baseEnd_792558 < baseStart_792558 := by decide
  rcases family_descends (prefixWord ++ tailWord_792558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792569 : List Nat := [1, 2, 1, 3, 1, 4, 1, 3, 5]
def baseStart_792569 : Nat := 118140960795 + 792569 * 2 ^ 59
def prefixEnd_792569 : Nat := 4983230072969 + 3 ^ 40 * 792569 * 2
def baseEnd_792569 : Nat := 180875043934851023930021

theorem tailTrace_792569 : CollatzResearch.WordTrace tailWord_792569 prefixEnd_792569 180875043934851023930021 := by
  unfold tailWord_792569
  simp only [CollatzResearch.WordTrace]
  refine ⟨28907366265665347853748761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19271577510443565235832507 28907366265665347853748761)
  ·
    refine ⟨21680524699249010890311571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28907366265665347853748761 21680524699249010890311571)
    ·
      refine ⟨32520787048873516335467357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21680524699249010890311571 32520787048873516335467357)
      ·
        refine ⟨12195295143327568625800259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32520787048873516335467357 12195295143327568625800259)
        ·
          refine ⟨18292942714991352938700389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12195295143327568625800259 18292942714991352938700389)
          ·
            refine ⟨3429926759060878676006323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18292942714991352938700389 3429926759060878676006323)
            ·
              refine ⟨5144890138591318014009485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3429926759060878676006323 5144890138591318014009485)
              ·
                refine ⟨1929333801971744255253557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5144890138591318014009485 1929333801971744255253557)
                ·
                  refine ⟨180875043934851023930021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1929333801971744255253557 180875043934851023930021)
                  ·
                    rfl

theorem cell21_792569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_792569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792569 prefixEnd_792569 := by exact prefixLift 792569
  have htrace : WordTrace (prefixWord ++ tailWord_792569) baseStart_792569 baseEnd_792569 := by
    simpa [prefixWord, tailWord_792569, baseEnd_792569] using wordTrace_append hprefix tailTrace_792569
  have hstable : (prefixWord ++ tailWord_792569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792569).length < 2 ^ (prefixWord ++ tailWord_792569).sum := by decide
  have hdescent : baseEnd_792569 < baseStart_792569 := by decide
  rcases family_descends (prefixWord ++ tailWord_792569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792676 : List Nat := [2, 3, 1, 1, 2, 1, 3, 4, 4]
def baseStart_792676 : Nat := 118140960795 + 792676 * 2 ^ 59
def prefixEnd_792676 : Nat := 4983230072969 + 3 ^ 40 * 792676 * 2
def baseEnd_792676 : Nat := 180899462792642615646469

theorem tailTrace_792676 : CollatzResearch.WordTrace tailWord_792676 prefixEnd_792676 180899462792642615646469 := by
  unfold tailWord_792676
  simp only [CollatzResearch.WordTrace]
  refine ⟨14455634438138852563946941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19274179250851803418595921 14455634438138852563946941)
  ·
    refine ⟨5420862914302069711480103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14455634438138852563946941 5420862914302069711480103)
    ·
      refine ⟨8131294371453104567220155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5420862914302069711480103 8131294371453104567220155)
      ·
        refine ⟨12196941557179656850830233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8131294371453104567220155 12196941557179656850830233)
        ·
          refine ⟨9147706167884742638122675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12196941557179656850830233 9147706167884742638122675)
          ·
            refine ⟨13721559251827113957184013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9147706167884742638122675 13721559251827113957184013)
            ·
              refine ⟨5145584719435167733944005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13721559251827113957184013 5145584719435167733944005)
              ·
                refine ⟨964797134894093950114501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5145584719435167733944005 964797134894093950114501)
                ·
                  refine ⟨180899462792642615646469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 964797134894093950114501 180899462792642615646469)
                  ·
                    rfl

theorem cell21_792676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_792676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792676 prefixEnd_792676 := by exact prefixLift 792676
  have htrace : WordTrace (prefixWord ++ tailWord_792676) baseStart_792676 baseEnd_792676 := by
    simpa [prefixWord, tailWord_792676, baseEnd_792676] using wordTrace_append hprefix tailTrace_792676
  have hstable : (prefixWord ++ tailWord_792676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792676).length < 2 ^ (prefixWord ++ tailWord_792676).sum := by decide
  have hdescent : baseEnd_792676 < baseStart_792676 := by decide
  rcases family_descends (prefixWord ++ tailWord_792676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792707 : List Nat := [1, 1, 1, 3, 3, 4, 3, 5]
def baseStart_792707 : Nat := 118140960795 + 792707 * 2 ^ 59
def prefixEnd_792707 : Nat := 4983230072969 + 3 ^ 40 * 792707 * 2
def baseEnd_792707 : Nat := 60302179138331150209913

theorem tailTrace_792707 : CollatzResearch.WordTrace tailWord_792707 prefixEnd_792707 60302179138331150209913 := by
  unfold tailWord_792707
  simp only [CollatzResearch.WordTrace]
  refine ⟨28912399539165397422272375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19274933026110264948181583 28912399539165397422272375)
  ·
    refine ⟨43368599308748096133408563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28912399539165397422272375 43368599308748096133408563)
    ·
      refine ⟨65052898963122144200112845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43368599308748096133408563 65052898963122144200112845)
      ·
        refine ⟨24394837111170804075042317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65052898963122144200112845 24394837111170804075042317)
        ·
          refine ⟨9148063916689051528140869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24394837111170804075042317 9148063916689051528140869)
          ·
            refine ⟨1715261984379197161526413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9148063916689051528140869 1715261984379197161526413)
            ·
              refine ⟨643223244142198935572405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1715261984379197161526413 643223244142198935572405)
              ·
                refine ⟨60302179138331150209913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 643223244142198935572405 60302179138331150209913)
                ·
                  rfl

theorem cell21_792707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 5].length) (baseStart_792707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792707 prefixEnd_792707 := by exact prefixLift 792707
  have htrace : WordTrace (prefixWord ++ tailWord_792707) baseStart_792707 baseEnd_792707 := by
    simpa [prefixWord, tailWord_792707, baseEnd_792707] using wordTrace_append hprefix tailTrace_792707
  have hstable : (prefixWord ++ tailWord_792707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792707).length < 2 ^ (prefixWord ++ tailWord_792707).sum := by decide
  have hdescent : baseEnd_792707 < baseStart_792707 := by decide
  rcases family_descends (prefixWord ++ tailWord_792707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792724 : List Nat := [2, 4, 2, 3, 1, 1, 8]
def baseStart_792724 : Nat := 118140960795 + 792724 * 2 ^ 59
def prefixEnd_792724 : Nat := 4983230072969 + 3 ^ 40 * 792724 * 2
def baseEnd_792724 : Nat := 20101157449622799871819

theorem tailTrace_792724 : CollatzResearch.WordTrace tailWord_792724 prefixEnd_792724 20101157449622799871819 := by
  unfold tailWord_792724
  simp only [CollatzResearch.WordTrace]
  refine ⟨14456509790051904662820613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19275346386735872883760817 14456509790051904662820613)
  ·
    refine ⟨2710595585634732124278865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14456509790051904662820613 2710595585634732124278865)
    ·
      refine ⟨2032946689226049093209149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2710595585634732124278865 2032946689226049093209149)
      ·
        refine ⟨762355008459768409953431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2032946689226049093209149 762355008459768409953431)
        ·
          refine ⟨1143532512689652614930147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762355008459768409953431 1143532512689652614930147)
          ·
            refine ⟨1715298769034478922395221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1143532512689652614930147 1715298769034478922395221)
            ·
              refine ⟨20101157449622799871819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1715298769034478922395221 20101157449622799871819)
              ·
                rfl

theorem cell21_792724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 8].length) (baseStart_792724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792724 prefixEnd_792724 := by exact prefixLift 792724
  have htrace : WordTrace (prefixWord ++ tailWord_792724) baseStart_792724 baseEnd_792724 := by
    simpa [prefixWord, tailWord_792724, baseEnd_792724] using wordTrace_append hprefix tailTrace_792724
  have hstable : (prefixWord ++ tailWord_792724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792724).length < 2 ^ (prefixWord ++ tailWord_792724).sum := by decide
  have hdescent : baseEnd_792724 < baseStart_792724 := by decide
  rcases family_descends (prefixWord ++ tailWord_792724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792738 : List Nat := [3, 3, 1, 3, 1, 1, 1, 3, 5]
def baseStart_792738 : Nat := 118140960795 + 792738 * 2 ^ 59
def prefixEnd_792738 : Nat := 4983230072969 + 3 ^ 40 * 792738 * 2
def baseEnd_792738 : Nat := 180913612037344285613009

theorem tailTrace_792738 : CollatzResearch.WordTrace tailWord_792738 prefixEnd_792738 180913612037344285613009 := by
  unfold tailWord_792738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7228382550513272429162717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19275686801368726477767245 7228382550513272429162717)
  ·
    refine ⟨2710643456442477160936019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7228382550513272429162717 2710643456442477160936019)
    ·
      refine ⟨4065965184663715741404029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2710643456442477160936019 4065965184663715741404029)
      ·
        refine ⟨1524736944248893403026511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4065965184663715741404029 1524736944248893403026511)
        ·
          refine ⟨2287105416373340104539767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524736944248893403026511 2287105416373340104539767)
          ·
            refine ⟨3430658124560010156809651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2287105416373340104539767 3430658124560010156809651)
            ·
              refine ⟨5145987186840015235214477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3430658124560010156809651 5145987186840015235214477)
              ·
                refine ⟨1929745195065005713205429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5145987186840015235214477 1929745195065005713205429)
                ·
                  refine ⟨180913612037344285613009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1929745195065005713205429 180913612037344285613009)
                  ·
                    rfl

theorem cell21_792738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_792738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792738 prefixEnd_792738 := by exact prefixLift 792738
  have htrace : WordTrace (prefixWord ++ tailWord_792738) baseStart_792738 baseEnd_792738 := by
    simpa [prefixWord, tailWord_792738, baseEnd_792738] using wordTrace_append hprefix tailTrace_792738
  have hstable : (prefixWord ++ tailWord_792738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792738).length < 2 ^ (prefixWord ++ tailWord_792738).sum := by decide
  have hdescent : baseEnd_792738 < baseStart_792738 := by decide
  rcases family_descends (prefixWord ++ tailWord_792738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792772 : List Nat := [2, 3, 3, 1, 2, 3, 1, 3, 3]
def baseStart_792772 : Nat := 118140960795 + 792772 * 2 ^ 59
def prefixEnd_792772 : Nat := 4983230072969 + 3 ^ 40 * 792772 * 2
def baseEnd_792772 : Nat := 180921371300567782046273

theorem tailTrace_792772 : CollatzResearch.WordTrace tailWord_792772 prefixEnd_792772 180921371300567782046273 := by
  unfold tailWord_792772
  simp only [CollatzResearch.WordTrace]
  refine ⟨14457385141964956761694285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19276513522619942348925713 14457385141964956761694285)
  ·
    refine ⟨5421519428236858785635357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14457385141964956761694285 5421519428236858785635357)
    ·
      refine ⟨2033069785588822044613259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5421519428236858785635357 2033069785588822044613259)
      ·
        refine ⟨3049604678383233066919889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2033069785588822044613259 3049604678383233066919889)
        ·
          refine ⟨2287203508787424800189917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3049604678383233066919889 2287203508787424800189917)
          ·
            refine ⟨857701315795284300071219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2287203508787424800189917 857701315795284300071219)
            ·
              refine ⟨1286551973692926450106829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857701315795284300071219 1286551973692926450106829)
              ·
                refine ⟨482456990134847418790061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1286551973692926450106829 482456990134847418790061)
                ·
                  refine ⟨180921371300567782046273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 482456990134847418790061 180921371300567782046273)
                  ·
                    rfl

theorem cell21_792772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_792772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792772 prefixEnd_792772 := by exact prefixLift 792772
  have htrace : WordTrace (prefixWord ++ tailWord_792772) baseStart_792772 baseEnd_792772 := by
    simpa [prefixWord, tailWord_792772, baseEnd_792772] using wordTrace_append hprefix tailTrace_792772
  have hstable : (prefixWord ++ tailWord_792772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792772).length < 2 ^ (prefixWord ++ tailWord_792772).sum := by decide
  have hdescent : baseEnd_792772 < baseStart_792772 := by decide
  rcases family_descends (prefixWord ++ tailWord_792772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792803 : List Nat := [1, 1, 1, 8, 1, 2, 2, 1, 4]
def baseStart_792803 : Nat := 118140960795 + 792803 * 2 ^ 59
def prefixEnd_792803 : Nat := 4983230072969 + 3 ^ 40 * 792803 * 2
def baseEnd_792803 : Nat := 180928445922918617029543

theorem tailTrace_792803 : CollatzResearch.WordTrace tailWord_792803 prefixEnd_792803 180928445922918617029543 := by
  unfold tailWord_792803
  simp only [CollatzResearch.WordTrace]
  refine ⟨28915900946817605817767063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19277267297878403878511375 28915900946817605817767063)
  ·
    refine ⟨43373851420226408726650595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28915900946817605817767063 43373851420226408726650595)
    ·
      refine ⟨65060777130339613089975893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43373851420226408726650595 65060777130339613089975893)
      ·
        refine ⟨762430981996167340898155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 65060777130339613089975893 762430981996167340898155)
        ·
          refine ⟨1143646472994251011347233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762430981996167340898155 1143646472994251011347233)
          ·
            refine ⟨857734854745688258510425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1143646472994251011347233 857734854745688258510425)
            ·
              refine ⟨643301141059266193882819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 857734854745688258510425 643301141059266193882819)
              ·
                refine ⟨964951711588899290824229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643301141059266193882819 964951711588899290824229)
                ·
                  refine ⟨180928445922918617029543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 964951711588899290824229 180928445922918617029543)
                  ·
                    rfl

theorem cell21_792803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 4].length) (baseStart_792803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792803 prefixEnd_792803 := by exact prefixLift 792803
  have htrace : WordTrace (prefixWord ++ tailWord_792803) baseStart_792803 baseEnd_792803 := by
    simpa [prefixWord, tailWord_792803, baseEnd_792803] using wordTrace_append hprefix tailTrace_792803
  have hstable : (prefixWord ++ tailWord_792803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792803).length < 2 ^ (prefixWord ++ tailWord_792803).sum := by decide
  have hdescent : baseEnd_792803 < baseStart_792803 := by decide
  rcases family_descends (prefixWord ++ tailWord_792803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792862 : List Nat := [4, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_792862 : Nat := 118140960795 + 792862 * 2 ^ 59
def prefixEnd_792862 : Nat := 4983230072969 + 3 ^ 40 * 792862 * 2
def baseEnd_792862 : Nat := 180941910526747625546089

theorem tailTrace_792862 : CollatzResearch.WordTrace tailWord_792862 prefixEnd_792862 180941910526747625546089 := by
  unfold tailWord_792862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3614756606700482361770605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19278701902402572596109893 3614756606700482361770605)
  ·
    refine ⟨1355533727512680885663977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3614756606700482361770605 1355533727512680885663977)
    ·
      refine ⟨1016650295634510664247983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1355533727512680885663977 1016650295634510664247983)
      ·
        refine ⟨1524975443451765996371975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1016650295634510664247983 1524975443451765996371975)
        ·
          refine ⟨2287463165177648994557963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524975443451765996371975 2287463165177648994557963)
          ·
            refine ⟨3431194747766473491836945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2287463165177648994557963 3431194747766473491836945)
            ·
              refine ⟨2573396060824855118877709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3431194747766473491836945 2573396060824855118877709)
              ·
                refine ⟨965023522809320669579141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2573396060824855118877709 965023522809320669579141)
                ·
                  refine ⟨180941910526747625546089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 965023522809320669579141 180941910526747625546089)
                  ·
                    rfl

theorem cell21_792862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_792862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792862 prefixEnd_792862 := by exact prefixLift 792862
  have htrace : WordTrace (prefixWord ++ tailWord_792862) baseStart_792862 baseEnd_792862 := by
    simpa [prefixWord, tailWord_792862, baseEnd_792862] using wordTrace_append hprefix tailTrace_792862
  have hstable : (prefixWord ++ tailWord_792862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792862).length < 2 ^ (prefixWord ++ tailWord_792862).sum := by decide
  have hdescent : baseEnd_792862 < baseStart_792862 := by decide
  rcases family_descends (prefixWord ++ tailWord_792862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792890 : List Nat := [3, 1, 1, 1, 4, 2, 1, 5, 3]
def baseStart_792890 : Nat := 118140960795 + 792890 * 2 ^ 59
def prefixEnd_792890 : Nat := 4983230072969 + 3 ^ 40 * 792890 * 2
def baseEnd_792890 : Nat := 180948300508225799079365

theorem tailTrace_792890 : CollatzResearch.WordTrace tailWord_792890 prefixEnd_792890 180948300508225799079365 := by
  unfold tailWord_792890
  simp only [CollatzResearch.WordTrace]
  refine ⟨7229768524375604919046031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19279382731668279784122749 7229768524375604919046031)
  ·
    refine ⟨10844652786563407378569047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7229768524375604919046031 10844652786563407378569047)
    ·
      refine ⟨16266979179845111067853571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10844652786563407378569047 16266979179845111067853571)
      ·
        refine ⟨24400468769767666601780357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16266979179845111067853571 24400468769767666601780357)
        ·
          refine ⟨4575087894331437487833817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24400468769767666601780357 4575087894331437487833817)
          ·
            refine ⟨3431315920748578115875363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4575087894331437487833817 3431315920748578115875363)
            ·
              refine ⟨5146973881122867173813045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3431315920748578115875363 5146973881122867173813045)
              ·
                refine ⟨482528801355268797544973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5146973881122867173813045 482528801355268797544973)
                ·
                  refine ⟨180948300508225799079365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 482528801355268797544973 180948300508225799079365)
                  ·
                    rfl

theorem cell21_792890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_792890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792890 prefixEnd_792890 := by exact prefixLift 792890
  have htrace : WordTrace (prefixWord ++ tailWord_792890) baseStart_792890 baseEnd_792890 := by
    simpa [prefixWord, tailWord_792890, baseEnd_792890] using wordTrace_append hprefix tailTrace_792890
  have hstable : (prefixWord ++ tailWord_792890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792890).length < 2 ^ (prefixWord ++ tailWord_792890).sum := by decide
  have hdescent : baseEnd_792890 < baseStart_792890 := by decide
  rcases family_descends (prefixWord ++ tailWord_792890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792904 : List Nat := [2, 1, 3, 1, 1, 2, 5, 2, 4]
def baseStart_792904 : Nat := 118140960795 + 792904 * 2 ^ 59
def prefixEnd_792904 : Nat := 4983230072969 + 3 ^ 40 * 792904 * 2
def baseEnd_792904 : Nat := 180951495498964885846003

theorem tailTrace_792904 : CollatzResearch.WordTrace tailWord_792904 prefixEnd_792904 180951495498964885846003 := by
  unfold tailWord_792904
  simp only [CollatzResearch.WordTrace]
  refine ⟨14459792359725850033596883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19279723146301133378129177 14459792359725850033596883)
  ·
    refine ⟨21689688539588775050395325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14459792359725850033596883 21689688539588775050395325)
    ·
      refine ⟨8133633202345790643898247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21689688539588775050395325 8133633202345790643898247)
      ·
        refine ⟨12200449803518685965847371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8133633202345790643898247 12200449803518685965847371)
        ·
          refine ⟨18300674705278028948771057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12200449803518685965847371 18300674705278028948771057)
          ·
            refine ⟨13725506028958521711578293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18300674705278028948771057 13725506028958521711578293)
            ·
              refine ⟨1286766190214861410460465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13725506028958521711578293 1286766190214861410460465)
              ·
                refine ⟨965074642661146057845349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286766190214861410460465 965074642661146057845349)
                ·
                  refine ⟨180951495498964885846003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 965074642661146057845349 180951495498964885846003)
                  ·
                    rfl

theorem cell21_792904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_792904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792904 prefixEnd_792904 := by exact prefixLift 792904
  have htrace : WordTrace (prefixWord ++ tailWord_792904) baseStart_792904 baseEnd_792904 := by
    simpa [prefixWord, tailWord_792904, baseEnd_792904] using wordTrace_append hprefix tailTrace_792904
  have hstable : (prefixWord ++ tailWord_792904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792904).length < 2 ^ (prefixWord ++ tailWord_792904).sum := by decide
  have hdescent : baseEnd_792904 < baseStart_792904 := by decide
  rcases family_descends (prefixWord ++ tailWord_792904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792935 : List Nat := [1, 1, 5, 1, 3, 1, 4, 5]
def baseStart_792935 : Nat := 118140960795 + 792935 * 2 ^ 59
def prefixEnd_792935 : Nat := 4983230072969 + 3 ^ 40 * 792935 * 2
def baseEnd_792935 : Nat := 60319523373771906943091

theorem tailTrace_792935 : CollatzResearch.WordTrace tailWord_792935 prefixEnd_792935 60319523373771906943091 := by
  unfold tailWord_792935
  simp only [CollatzResearch.WordTrace]
  refine ⟨28920715382339392361572259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19280476921559594907714839 28920715382339392361572259)
  ·
    refine ⟨43381073073509088542358389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28920715382339392361572259 43381073073509088542358389)
    ·
      refine ⟨4066975600641477050846099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43381073073509088542358389 4066975600641477050846099)
      ·
        refine ⟨6100463400962215576269149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4066975600641477050846099 6100463400962215576269149)
        ·
          refine ⟨2287673775360830841100931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6100463400962215576269149 2287673775360830841100931)
          ·
            refine ⟨3431510663041246261651397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2287673775360830841100931 3431510663041246261651397)
            ·
              refine ⟨643408249320233674059637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3431510663041246261651397 643408249320233674059637)
              ·
                refine ⟨60319523373771906943091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 643408249320233674059637 60319523373771906943091)
                ·
                  rfl

theorem cell21_792935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 5].length) (baseStart_792935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792935 prefixEnd_792935 := by exact prefixLift 792935
  have htrace : WordTrace (prefixWord ++ tailWord_792935) baseStart_792935 baseEnd_792935 := by
    simpa [prefixWord, tailWord_792935, baseEnd_792935] using wordTrace_append hprefix tailTrace_792935
  have hstable : (prefixWord ++ tailWord_792935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792935).length < 2 ^ (prefixWord ++ tailWord_792935).sum := by decide
  have hdescent : baseEnd_792935 < baseStart_792935 := by decide
  rcases family_descends (prefixWord ++ tailWord_792935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_792994 : List Nat := [3, 3, 1, 2, 1, 1, 1, 9]
def baseStart_792994 : Nat := 118140960795 + 792994 * 2 ^ 59
def prefixEnd_792994 : Nat := 4983230072969 + 3 ^ 40 * 792994 * 2
def baseEnd_792994 : Nat := 60324011575048243115273

theorem tailTrace_792994 : CollatzResearch.WordTrace tailWord_792994 prefixEnd_792994 60324011575048243115273 := by
  unfold tailWord_792994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7230716822281411359492509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19281911526083763625313357 7230716822281411359492509)
  ·
    refine ⟨2711518808355529259809691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7230716822281411359492509 2711518808355529259809691)
    ·
      refine ⟨4067278212533293889714537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2711518808355529259809691 4067278212533293889714537)
      ·
        refine ⟨3050458659399970417285903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4067278212533293889714537 3050458659399970417285903)
        ·
          refine ⟨4575687989099955625928855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3050458659399970417285903 4575687989099955625928855)
          ·
            refine ⟨6863531983649933438893283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4575687989099955625928855 6863531983649933438893283)
            ·
              refine ⟨10295297975474900158339925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6863531983649933438893283 10295297975474900158339925)
              ·
                refine ⟨60324011575048243115273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10295297975474900158339925 60324011575048243115273)
                ·
                  rfl

theorem cell21_792994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_792994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_792994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_792994 prefixEnd_792994 := by exact prefixLift 792994
  have htrace : WordTrace (prefixWord ++ tailWord_792994) baseStart_792994 baseEnd_792994 := by
    simpa [prefixWord, tailWord_792994, baseEnd_792994] using wordTrace_append hprefix tailTrace_792994
  have hstable : (prefixWord ++ tailWord_792994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_792994).length < 2 ^ (prefixWord ++ tailWord_792994).sum := by decide
  have hdescent : baseEnd_792994 < baseStart_792994 := by decide
  rcases family_descends (prefixWord ++ tailWord_792994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793028 : List Nat := [2, 3, 3, 2, 2, 2, 1, 6]
def baseStart_793028 : Nat := 118140960795 + 793028 * 2 ^ 59
def prefixEnd_793028 : Nat := 4983230072969 + 3 ^ 40 * 793028 * 2
def baseEnd_793028 : Nat := 60326597996122741926361

theorem tailTrace_793028 : CollatzResearch.WordTrace tailWord_793028 prefixEnd_793028 60326597996122741926361 := by
  unfold tailWord_793028
  simp only [CollatzResearch.WordTrace]
  refine ⟨14462053685501234622353869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19282738247334979496471825 14462053685501234622353869)
  ·
    refine ⟨5423270132062962983382701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14462053685501234622353869 5423270132062962983382701)
    ·
      refine ⟨2033726299523611118768513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5423270132062962983382701 2033726299523611118768513)
      ·
        refine ⟨1525294724642708339076385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2033726299523611118768513 1525294724642708339076385)
        ·
          refine ⟨1143971043482031254307289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1525294724642708339076385 1143971043482031254307289)
          ·
            refine ⟨857978282611523440730467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1143971043482031254307289 857978282611523440730467)
            ·
              refine ⟨1286967423917285161095701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 857978282611523440730467 1286967423917285161095701)
              ·
                refine ⟨60326597996122741926361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1286967423917285161095701 60326597996122741926361)
                ·
                  rfl

theorem cell21_793028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 6].length) (baseStart_793028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793028 prefixEnd_793028 := by exact prefixLift 793028
  have htrace : WordTrace (prefixWord ++ tailWord_793028) baseStart_793028 baseEnd_793028 := by
    simpa [prefixWord, tailWord_793028, baseEnd_793028] using wordTrace_append hprefix tailTrace_793028
  have hstable : (prefixWord ++ tailWord_793028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793028).length < 2 ^ (prefixWord ++ tailWord_793028).sum := by decide
  have hdescent : baseEnd_793028 < baseStart_793028 := by decide
  rcases family_descends (prefixWord ++ tailWord_793028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793059 : List Nat := [1, 1, 1, 6, 3, 1, 2, 3, 3]
def baseStart_793059 : Nat := 118140960795 + 793059 * 2 ^ 59
def prefixEnd_793059 : Nat := 4983230072969 + 3 ^ 40 * 793059 * 2
def baseEnd_793059 : Nat := 180986868610719060762353

theorem tailTrace_793059 : CollatzResearch.WordTrace tailWord_793059 prefixEnd_793059 180986868610719060762353 := by
  unfold tailWord_793059
  simp only [CollatzResearch.WordTrace]
  refine ⟨28925238033890161539086231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19283492022593441026057487 28925238033890161539086231)
  ·
    refine ⟨43387857050835242308629347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28925238033890161539086231 43387857050835242308629347)
    ·
      refine ⟨65081785576252863462944021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43387857050835242308629347 65081785576252863462944021)
      ·
        refine ⟨3050708698886852974825501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65081785576252863462944021 3050708698886852974825501)
        ·
          refine ⟨1144015762082569865559563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3050708698886852974825501 1144015762082569865559563)
          ·
            refine ⟨1716023643123854798339345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144015762082569865559563 1716023643123854798339345)
            ·
              refine ⟨1287017732342891098754509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1716023643123854798339345 1287017732342891098754509)
              ·
                refine ⟨482631649628584162032941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1287017732342891098754509 482631649628584162032941)
                ·
                  refine ⟨180986868610719060762353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 482631649628584162032941 180986868610719060762353)
                  ·
                    rfl

theorem cell21_793059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 3].length) (baseStart_793059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793059 prefixEnd_793059 := by exact prefixLift 793059
  have htrace : WordTrace (prefixWord ++ tailWord_793059) baseStart_793059 baseEnd_793059 := by
    simpa [prefixWord, tailWord_793059, baseEnd_793059] using wordTrace_append hprefix tailTrace_793059
  have hstable : (prefixWord ++ tailWord_793059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793059).length < 2 ^ (prefixWord ++ tailWord_793059).sum := by decide
  have hdescent : baseEnd_793059 < baseStart_793059 := by decide
  rcases family_descends (prefixWord ++ tailWord_793059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793070 : List Nat := [4, 1, 2, 1, 2, 3, 8]
def baseStart_793070 : Nat := 118140960795 + 793070 * 2 ^ 59
def prefixEnd_793070 : Nat := 4983230072969 + 3 ^ 40 * 793070 * 2
def baseEnd_793070 : Nat := 20109930995620609564333

theorem tailTrace_793070 : CollatzResearch.WordTrace tailWord_793070 prefixEnd_793070 20109930995620609564333 := by
  unfold tailWord_793070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3615704904606288802217083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19283759491233540278491109 3615704904606288802217083)
  ·
    refine ⟨5423557356909433203325625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3615704904606288802217083 5423557356909433203325625)
    ·
      refine ⟨4067668017682074902494219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5423557356909433203325625 4067668017682074902494219)
      ·
        refine ⟨6101502026523112353741329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4067668017682074902494219 6101502026523112353741329)
        ·
          refine ⟨4576126519892334265305997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6101502026523112353741329 4576126519892334265305997)
          ·
            refine ⟨1716047444959625349489749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4576126519892334265305997 1716047444959625349489749)
            ·
              refine ⟨20109930995620609564333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1716047444959625349489749 20109930995620609564333)
              ·
                rfl

theorem cell21_793070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 8].length) (baseStart_793070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793070 prefixEnd_793070 := by exact prefixLift 793070
  have htrace : WordTrace (prefixWord ++ tailWord_793070) baseStart_793070 baseEnd_793070 := by
    simpa [prefixWord, tailWord_793070, baseEnd_793070] using wordTrace_append hprefix tailTrace_793070
  have hstable : (prefixWord ++ tailWord_793070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793070).length < 2 ^ (prefixWord ++ tailWord_793070).sum := by decide
  have hdescent : baseEnd_793070 < baseStart_793070 := by decide
  rcases family_descends (prefixWord ++ tailWord_793070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793146 : List Nat := [3, 1, 1, 1, 3, 4, 2, 6]
def baseStart_793146 : Nat := 118140960795 + 793146 * 2 ^ 59
def prefixEnd_793146 : Nat := 4983230072969 + 3 ^ 40 * 793146 * 2
def baseEnd_793146 : Nat := 60335574398675414270725

theorem tailTrace_793146 : CollatzResearch.WordTrace tailWord_793146 prefixEnd_793146 60335574398675414270725 := by
  unfold tailWord_793146
  simp only [CollatzResearch.WordTrace]
  refine ⟨7232102796143743849375823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19285607456383316931668861 7232102796143743849375823)
  ·
    refine ⟨10848154194215615774063735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7232102796143743849375823 10848154194215615774063735)
    ·
      refine ⟨16272231291323423661095603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10848154194215615774063735 16272231291323423661095603)
      ·
        refine ⟨24408346936985135491643405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16272231291323423661095603 24408346936985135491643405)
        ·
          refine ⟨9153130101369425809366277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24408346936985135491643405 9153130101369425809366277)
          ·
            refine ⟨1716211894006767339256177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9153130101369425809366277 1716211894006767339256177)
            ·
              refine ⟨1287158920505075504442133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1716211894006767339256177 1287158920505075504442133)
              ·
                refine ⟨60335574398675414270725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1287158920505075504442133 60335574398675414270725)
                ·
                  rfl

theorem cell21_793146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_793146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793146 prefixEnd_793146 := by exact prefixLift 793146
  have htrace : WordTrace (prefixWord ++ tailWord_793146) baseStart_793146 baseEnd_793146 := by
    simpa [prefixWord, tailWord_793146, baseEnd_793146] using wordTrace_append hprefix tailTrace_793146
  have hstable : (prefixWord ++ tailWord_793146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793146).length < 2 ^ (prefixWord ++ tailWord_793146).sum := by decide
  have hdescent : baseEnd_793146 < baseStart_793146 := by decide
  rcases family_descends (prefixWord ++ tailWord_793146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793149 : List Nat := [1, 4, 1, 3, 2, 1, 4, 1, 4]
def baseStart_793149 : Nat := 118140960795 + 793149 * 2 ^ 59
def prefixEnd_793149 : Nat := 4983230072969 + 3 ^ 40 * 793149 * 2
def baseEnd_793149 : Nat := 181007407836898904262169

theorem tailTrace_793149 : CollatzResearch.WordTrace tailWord_793149 prefixEnd_793149 181007407836898904262169 := by
  unfold tailWord_793149
  simp only [CollatzResearch.WordTrace]
  refine ⟨28928520603564106909862501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19285680402376071273241667 28928520603564106909862501)
  ·
    refine ⟨5424097613168270045599219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28928520603564106909862501 5424097613168270045599219)
    ·
      refine ⟨8136146419752405068398829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5424097613168270045599219 8136146419752405068398829)
      ·
        refine ⟨3051054907407151900649561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8136146419752405068398829 3051054907407151900649561)
        ·
          refine ⟨2288291180555363925487171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3051054907407151900649561 2288291180555363925487171)
          ·
            refine ⟨3432436770833045888230757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2288291180555363925487171 3432436770833045888230757)
            ·
              refine ⟨643581894531196104043267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3432436770833045888230757 643581894531196104043267)
              ·
                refine ⟨965372841796794156064901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643581894531196104043267 965372841796794156064901)
                ·
                  refine ⟨181007407836898904262169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 965372841796794156064901 181007407836898904262169)
                  ·
                    rfl

theorem cell21_793149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_793149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793149 prefixEnd_793149 := by exact prefixLift 793149
  have htrace : WordTrace (prefixWord ++ tailWord_793149) baseStart_793149 baseEnd_793149 := by
    simpa [prefixWord, tailWord_793149, baseEnd_793149] using wordTrace_append hprefix tailTrace_793149
  have hstable : (prefixWord ++ tailWord_793149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793149).length < 2 ^ (prefixWord ++ tailWord_793149).sum := by decide
  have hdescent : baseEnd_793149 < baseStart_793149 := by decide
  rcases family_descends (prefixWord ++ tailWord_793149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793160 : List Nat := [2, 1, 3, 1, 1, 1, 1, 6, 5]
def baseStart_793160 : Nat := 118140960795 + 793160 * 2 ^ 59
def prefixEnd_793160 : Nat := 4983230072969 + 3 ^ 40 * 793160 * 2
def baseEnd_793160 : Nat := 181009918186765329578813

theorem tailTrace_793160 : CollatzResearch.WordTrace tailWord_793160 prefixEnd_793160 181009918186765329578813 := by
  unfold tailWord_793160
  simp only [CollatzResearch.WordTrace]
  refine ⟨14464460903262127894256467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19285947871016170525675289 14464460903262127894256467)
  ·
    refine ⟨21696691354893191841384701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14464460903262127894256467 21696691354893191841384701)
    ·
      refine ⟨8136259258084946940519263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21696691354893191841384701 8136259258084946940519263)
      ·
        refine ⟨12204388887127420410778895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8136259258084946940519263 12204388887127420410778895)
        ·
          refine ⟨18306583330691130616168343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12204388887127420410778895 18306583330691130616168343)
          ·
            refine ⟨27459874996036695924252515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18306583330691130616168343 27459874996036695924252515)
            ·
              refine ⟨41189812494055043886378773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27459874996036695924252515 41189812494055043886378773)
              ·
                refine ⟨1930772460658830182174005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41189812494055043886378773 1930772460658830182174005)
                ·
                  refine ⟨181009918186765329578813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1930772460658830182174005 181009918186765329578813)
                  ·
                    rfl

theorem cell21_793160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_793160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793160 prefixEnd_793160 := by exact prefixLift 793160
  have htrace : WordTrace (prefixWord ++ tailWord_793160) baseStart_793160 baseEnd_793160 := by
    simpa [prefixWord, tailWord_793160, baseEnd_793160] using wordTrace_append hprefix tailTrace_793160
  have hstable : (prefixWord ++ tailWord_793160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793160).length < 2 ^ (prefixWord ++ tailWord_793160).sum := by decide
  have hdescent : baseEnd_793160 < baseStart_793160 := by decide
  rcases family_descends (prefixWord ++ tailWord_793160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793186 : List Nat := [3, 3, 2, 3, 2, 1, 2, 2, 3]
def baseStart_793186 : Nat := 118140960795 + 793186 * 2 ^ 59
def prefixEnd_793186 : Nat := 4983230072969 + 3 ^ 40 * 793186 * 2
def baseEnd_793186 : Nat := 181015851740995062145427

theorem tailTrace_793186 : CollatzResearch.WordTrace tailWord_793186 prefixEnd_793186 181015851740995062145427 := by
  unfold tailWord_793186
  simp only [CollatzResearch.WordTrace]
  refine ⟨7232467526107515557239853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19286580069620041485972941 7232467526107515557239853)
  ·
    refine ⟨2712175322290318333964945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7232467526107515557239853 2712175322290318333964945)
    ·
      refine ⟨2034131491717738750473709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2712175322290318333964945 2034131491717738750473709)
      ·
        refine ⟨762799309394152031427641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2034131491717738750473709 762799309394152031427641)
        ·
          refine ⟨572099482045614023570731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 762799309394152031427641 572099482045614023570731)
          ·
            refine ⟨858149223068421035356097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572099482045614023570731 858149223068421035356097)
            ·
              refine ⟨643611917301315776517073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 858149223068421035356097 643611917301315776517073)
              ·
                refine ⟨482708937975986832387805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 643611917301315776517073 482708937975986832387805)
                ·
                  refine ⟨181015851740995062145427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 482708937975986832387805 181015851740995062145427)
                  ·
                    rfl

theorem cell21_793186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_793186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793186 prefixEnd_793186 := by exact prefixLift 793186
  have htrace : WordTrace (prefixWord ++ tailWord_793186) baseStart_793186 baseEnd_793186 := by
    simpa [prefixWord, tailWord_793186, baseEnd_793186] using wordTrace_append hprefix tailTrace_793186
  have hstable : (prefixWord ++ tailWord_793186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793186).length < 2 ^ (prefixWord ++ tailWord_793186).sum := by decide
  have hdescent : baseEnd_793186 < baseStart_793186 := by decide
  rcases family_descends (prefixWord ++ tailWord_793186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793194 : List Nat := [3, 1, 3, 2, 1, 1, 3, 4, 3]
def baseStart_793194 : Nat := 118140960795 + 793194 * 2 ^ 59
def prefixEnd_793194 : Nat := 4983230072969 + 3 ^ 40 * 793194 * 2
def baseEnd_793194 : Nat := 181017677449988826012077

theorem tailTrace_793194 : CollatzResearch.WordTrace tailWord_793194 prefixEnd_793194 181017677449988826012077 := by
  unfold tailWord_793194
  simp only [CollatzResearch.WordTrace]
  refine ⟨7232540472100269898812659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19286774592267386396833757 7232540472100269898812659)
  ·
    refine ⟨10848810708150404848218989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7232540472100269898812659 10848810708150404848218989)
    ·
      refine ⟨4068304015556401818082121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10848810708150404848218989 4068304015556401818082121)
      ·
        refine ⟨3051228011667301363561591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4068304015556401818082121 3051228011667301363561591)
        ·
          refine ⟨4576842017500952045342387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3051228011667301363561591 4576842017500952045342387)
          ·
            refine ⟨6865263026251428068013581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4576842017500952045342387 6865263026251428068013581)
            ·
              refine ⟨2574473634844285525505093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6865263026251428068013581 2574473634844285525505093)
              ·
                refine ⟨482713806533303536032205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2574473634844285525505093 482713806533303536032205)
                ·
                  refine ⟨181017677449988826012077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 482713806533303536032205 181017677449988826012077)
                  ·
                    rfl

theorem cell21_793194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_793194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793194 prefixEnd_793194 := by exact prefixLift 793194
  have htrace : WordTrace (prefixWord ++ tailWord_793194) baseStart_793194 baseEnd_793194 := by
    simpa [prefixWord, tailWord_793194, baseEnd_793194] using wordTrace_append hprefix tailTrace_793194
  have hstable : (prefixWord ++ tailWord_793194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793194).length < 2 ^ (prefixWord ++ tailWord_793194).sum := by decide
  have hdescent : baseEnd_793194 < baseStart_793194 := by decide
  rcases family_descends (prefixWord ++ tailWord_793194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793242 : List Nat := [3, 1, 1, 6, 1, 2, 1, 2, 4]
def baseStart_793242 : Nat := 118140960795 + 793242 * 2 ^ 59
def prefixEnd_793242 : Nat := 4983230072969 + 3 ^ 40 * 793242 * 2
def baseEnd_793242 : Nat := 181028631703951409211979

theorem tailTrace_793242 : CollatzResearch.WordTrace tailWord_793242 prefixEnd_793242 181028631703951409211979 := by
  unfold tailWord_793242
  simp only [CollatzResearch.WordTrace]
  refine ⟨7232978148056795948249495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19287941728151455861998653 7232978148056795948249495)
  ·
    refine ⟨10849467222085193922374243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7232978148056795948249495 10849467222085193922374243)
    ·
      refine ⟨16274200833127790883561365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10849467222085193922374243 16274200833127790883561365)
      ·
        refine ⟨762853164052865197666939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16274200833127790883561365 762853164052865197666939)
        ·
          refine ⟨1144279746079297796500409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 762853164052865197666939 1144279746079297796500409)
          ·
            refine ⟨858209809559473347375307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1144279746079297796500409 858209809559473347375307)
            ·
              refine ⟨1287314714339210021062961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858209809559473347375307 1287314714339210021062961)
              ·
                refine ⟨965486035754407515797221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1287314714339210021062961 965486035754407515797221)
                ·
                  refine ⟨181028631703951409211979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 965486035754407515797221 181028631703951409211979)
                  ·
                    rfl

theorem cell21_793242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_793242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793242 prefixEnd_793242 := by exact prefixLift 793242
  have htrace : WordTrace (prefixWord ++ tailWord_793242) baseStart_793242 baseEnd_793242 := by
    simpa [prefixWord, tailWord_793242, baseEnd_793242] using wordTrace_append hprefix tailTrace_793242
  have hstable : (prefixWord ++ tailWord_793242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793242).length < 2 ^ (prefixWord ++ tailWord_793242).sum := by decide
  have hdescent : baseEnd_793242 < baseStart_793242 := by decide
  rcases family_descends (prefixWord ++ tailWord_793242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793388 : List Nat := [2, 2, 1, 1, 1, 4, 3, 2, 5]
def baseStart_793388 : Nat := 118140960795 + 793388 * 2 ^ 59
def prefixEnd_793388 : Nat := 4983230072969 + 3 ^ 40 * 793388 * 2
def baseEnd_793388 : Nat := 181061950893087599778347

theorem tailTrace_793388 : CollatzResearch.WordTrace tailWord_793388 prefixEnd_793388 181061950893087599778347 := by
  unfold tailWord_793388
  simp only [CollatzResearch.WordTrace]
  refine ⟨14468618824849125363906409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19291491766465500485208545 14468618824849125363906409)
  ·
    refine ⟨10851464118636844022929807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14468618824849125363906409 10851464118636844022929807)
    ·
      refine ⟨16277196177955266034394711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10851464118636844022929807 16277196177955266034394711)
      ·
        refine ⟨24415794266932899051592067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16277196177955266034394711 24415794266932899051592067)
        ·
          refine ⟨36623691400399348577388101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24415794266932899051592067 36623691400399348577388101)
          ·
            refine ⟨6866942137574877858260269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36623691400399348577388101 6866942137574877858260269)
            ·
              refine ⟨2575103301590579196847601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6866942137574877858260269 2575103301590579196847601)
              ·
                refine ⟨1931327476192934397635701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2575103301590579196847601 1931327476192934397635701)
                ·
                  refine ⟨181061950893087599778347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1931327476192934397635701 181061950893087599778347)
                  ·
                    rfl

theorem cell21_793388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_793388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793388 prefixEnd_793388 := by exact prefixLift 793388
  have htrace : WordTrace (prefixWord ++ tailWord_793388) baseStart_793388 baseEnd_793388 := by
    simpa [prefixWord, tailWord_793388, baseEnd_793388] using wordTrace_append hprefix tailTrace_793388
  have hstable : (prefixWord ++ tailWord_793388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793388).length < 2 ^ (prefixWord ++ tailWord_793388).sum := by decide
  have hdescent : baseEnd_793388 < baseStart_793388 := by decide
  rcases family_descends (prefixWord ++ tailWord_793388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793481 : List Nat := [1, 2, 1, 1, 5, 4, 1, 1, 5]
def baseStart_793481 : Nat := 118140960795 + 793481 * 2 ^ 59
def prefixEnd_793481 : Nat := 4983230072969 + 3 ^ 40 * 793481 * 2
def baseEnd_793481 : Nat := 181083174760140104728157

theorem tailTrace_793481 : CollatzResearch.WordTrace tailWord_793481 prefixEnd_793481 181083174760140104728157 := by
  unfold tailWord_793481
  simp only [CollatzResearch.WordTrace]
  refine ⟨28940629638361327610948297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19293753092240885073965531 28940629638361327610948297)
  ·
    refine ⟨21705472228770995708211223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28940629638361327610948297 21705472228770995708211223)
    ·
      refine ⟨32558208343156493562316835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21705472228770995708211223 32558208343156493562316835)
      ·
        refine ⟨48837312514734740343475253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32558208343156493562316835 48837312514734740343475253)
        ·
          refine ⟨4578498048256381907200805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48837312514734740343475253 4578498048256381907200805)
          ·
            refine ⟨858468384048071607600151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4578498048256381907200805 858468384048071607600151)
            ·
              refine ⟨1287702576072107411400227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858468384048071607600151 1287702576072107411400227)
              ·
                refine ⟨1931553864108161117100341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1287702576072107411400227 1931553864108161117100341)
                ·
                  refine ⟨181083174760140104728157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1931553864108161117100341 181083174760140104728157)
                  ·
                    rfl

theorem cell21_793481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 5].length) (baseStart_793481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793481 prefixEnd_793481 := by exact prefixLift 793481
  have htrace : WordTrace (prefixWord ++ tailWord_793481) baseStart_793481 baseEnd_793481 := by
    simpa [prefixWord, tailWord_793481, baseEnd_793481] using wordTrace_append hprefix tailTrace_793481
  have hstable : (prefixWord ++ tailWord_793481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793481).length < 2 ^ (prefixWord ++ tailWord_793481).sum := by decide
  have hdescent : baseEnd_793481 < baseStart_793481 := by decide
  rcases family_descends (prefixWord ++ tailWord_793481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793495 : List Nat := [1, 1, 3, 3, 1, 2, 3, 3, 4]
def baseStart_793495 : Nat := 118140960795 + 793495 * 2 ^ 59
def prefixEnd_793495 : Nat := 4983230072969 + 3 ^ 40 * 793495 * 2
def baseEnd_793495 : Nat := 181086369750879191494795

theorem tailTrace_793495 : CollatzResearch.WordTrace tailWord_793495 prefixEnd_793495 181086369750879191494795 := by
  unfold tailWord_793495
  simp only [CollatzResearch.WordTrace]
  refine ⟨28941140260310608001957939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19294093506873738667971959 28941140260310608001957939)
  ·
    refine ⟨43411710390465912002936909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28941140260310608001957939 43411710390465912002936909)
    ·
      refine ⟨16279391396424717001101341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43411710390465912002936909 16279391396424717001101341)
      ·
        refine ⟨6104771773659268875413003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16279391396424717001101341 6104771773659268875413003)
        ·
          refine ⟨9157157660488903313119505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6104771773659268875413003 9157157660488903313119505)
          ·
            refine ⟨6867868245366677484839629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9157157660488903313119505 6867868245366677484839629)
            ·
              refine ⟨2575450592012504056814861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6867868245366677484839629 2575450592012504056814861)
              ·
                refine ⟨965793972004689021305573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2575450592012504056814861 965793972004689021305573)
                ·
                  refine ⟨181086369750879191494795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 965793972004689021305573 181086369750879191494795)
                  ·
                    rfl

theorem cell21_793495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 4].length) (baseStart_793495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793495 prefixEnd_793495 := by exact prefixLift 793495
  have htrace : WordTrace (prefixWord ++ tailWord_793495) baseStart_793495 baseEnd_793495 := by
    simpa [prefixWord, tailWord_793495, baseEnd_793495] using wordTrace_append hprefix tailTrace_793495
  have hstable : (prefixWord ++ tailWord_793495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793495).length < 2 ^ (prefixWord ++ tailWord_793495).sum := by decide
  have hdescent : baseEnd_793495 < baseStart_793495 := by decide
  rcases family_descends (prefixWord ++ tailWord_793495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793523 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 9]
def baseStart_793523 : Nat := 118140960795 + 793523 * 2 ^ 59
def prefixEnd_793523 : Nat := 4983230072969 + 3 ^ 40 * 793523 * 2
def baseEnd_793523 : Nat := 181092759732357365028071

theorem tailTrace_793523 : CollatzResearch.WordTrace tailWord_793523 prefixEnd_793523 181092759732357365028071 := by
  unfold tailWord_793523
  simp only [CollatzResearch.WordTrace]
  refine ⟨28942161504209168783977223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19294774336139445855984815 28942161504209168783977223)
  ·
    refine ⟨43413242256313753175965835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28942161504209168783977223 43413242256313753175965835)
    ·
      refine ⟨65119863384470629763948753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43413242256313753175965835 65119863384470629763948753)
      ·
        refine ⟨48839897538352972322961565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65119863384470629763948753 48839897538352972322961565)
        ·
          refine ⟨18314961576882364621110587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48839897538352972322961565 18314961576882364621110587)
          ·
            refine ⟨27472442365323546931665881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18314961576882364621110587 27472442365323546931665881)
            ·
              refine ⟨20604331773992660198749411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27472442365323546931665881 20604331773992660198749411)
              ·
                refine ⟨30906497660988990298124117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20604331773992660198749411 30906497660988990298124117)
                ·
                  refine ⟨181092759732357365028071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30906497660988990298124117 181092759732357365028071)
                  ·
                    rfl

theorem cell21_793523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 9].length) (baseStart_793523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793523 prefixEnd_793523 := by exact prefixLift 793523
  have htrace : WordTrace (prefixWord ++ tailWord_793523) baseStart_793523 baseEnd_793523 := by
    simpa [prefixWord, tailWord_793523, baseEnd_793523] using wordTrace_append hprefix tailTrace_793523
  have hstable : (prefixWord ++ tailWord_793523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793523).length < 2 ^ (prefixWord ++ tailWord_793523).sum := by decide
  have hdescent : baseEnd_793523 < baseStart_793523 := by decide
  rcases family_descends (prefixWord ++ tailWord_793523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793557 : List Nat := [1, 3, 2, 3, 3, 1, 1, 2, 5]
def baseStart_793557 : Nat := 118140960795 + 793557 * 2 ^ 59
def prefixEnd_793557 : Nat := 4983230072969 + 3 ^ 40 * 793557 * 2
def baseEnd_793557 : Nat := 181100518995580861461335

theorem tailTrace_793557 : CollatzResearch.WordTrace tailWord_793557 prefixEnd_793557 181100518995580861461335 := by
  unfold tailWord_793557
  simp only [CollatzResearch.WordTrace]
  refine ⟨28943401586085992590714925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19295601057390661727143283 28943401586085992590714925)
  ·
    refine ⟨10853775594782247221518097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28943401586085992590714925 10853775594782247221518097)
    ·
      refine ⟨8140331696086685416138573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10853775594782247221518097 8140331696086685416138573)
      ·
        refine ⟨3052624386032507031051965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8140331696086685416138573 3052624386032507031051965)
        ·
          refine ⟨1144734144762190136644487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3052624386032507031051965 1144734144762190136644487)
          ·
            refine ⟨1717101217143285204966731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144734144762190136644487 1717101217143285204966731)
            ·
              refine ⟨2575651825714927807450097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1717101217143285204966731 2575651825714927807450097)
              ·
                refine ⟨1931738869286195855587573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2575651825714927807450097 1931738869286195855587573)
                ·
                  refine ⟨181100518995580861461335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1931738869286195855587573 181100518995580861461335)
                  ·
                    rfl

theorem cell21_793557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_793557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793557 prefixEnd_793557 := by exact prefixLift 793557
  have htrace : WordTrace (prefixWord ++ tailWord_793557) baseStart_793557 baseEnd_793557 := by
    simpa [prefixWord, tailWord_793557, baseEnd_793557] using wordTrace_append hprefix tailTrace_793557
  have hstable : (prefixWord ++ tailWord_793557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793557).length < 2 ^ (prefixWord ++ tailWord_793557).sum := by decide
  have hdescent : baseEnd_793557 < baseStart_793557 := by decide
  rcases family_descends (prefixWord ++ tailWord_793557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793585 : List Nat := [1, 2, 2, 2, 4, 2, 8]
def baseStart_793585 : Nat := 118140960795 + 793585 * 2 ^ 59
def prefixEnd_793585 : Nat := 4983230072969 + 3 ^ 40 * 793585 * 2
def baseEnd_793585 : Nat := 20122989886339892777179

theorem tailTrace_793585 : CollatzResearch.WordTrace tailWord_793585 prefixEnd_793585 20122989886339892777179 := by
  unfold tailWord_793585
  simp only [CollatzResearch.WordTrace]
  refine ⟨28944422829984553372734209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19296281886656368915156139 28944422829984553372734209)
  ·
    refine ⟨21708317122488415029550657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28944422829984553372734209 21708317122488415029550657)
    ·
      refine ⟨16281237841866311272162993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21708317122488415029550657 16281237841866311272162993)
      ·
        refine ⟨12210928381399733454122245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16281237841866311272162993 12210928381399733454122245)
        ·
          refine ⟨2289549071512450022647921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12210928381399733454122245 2289549071512450022647921)
          ·
            refine ⟨1717161803634337516985941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2289549071512450022647921 1717161803634337516985941)
            ·
              refine ⟨20122989886339892777179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1717161803634337516985941 20122989886339892777179)
              ·
                rfl

theorem cell21_793585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 8].length) (baseStart_793585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793585 prefixEnd_793585 := by exact prefixLift 793585
  have htrace : WordTrace (prefixWord ++ tailWord_793585) baseStart_793585 baseEnd_793585 := by
    simpa [prefixWord, tailWord_793585, baseEnd_793585] using wordTrace_append hprefix tailTrace_793585
  have hstable : (prefixWord ++ tailWord_793585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793585).length < 2 ^ (prefixWord ++ tailWord_793585).sum := by decide
  have hdescent : baseEnd_793585 < baseStart_793585 := by decide
  rcases family_descends (prefixWord ++ tailWord_793585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793650 : List Nat := [3, 2, 1, 1, 2, 2, 5, 2, 3]
def baseStart_793650 : Nat := 118140960795 + 793650 * 2 ^ 59
def prefixEnd_793650 : Nat := 4983230072969 + 3 ^ 40 * 793650 * 2
def baseEnd_793650 : Nat := 181121742862633366411145

theorem tailTrace_793650 : CollatzResearch.WordTrace tailWord_793650 prefixEnd_793650 181121742862633366411145 := by
  unfold tailWord_793650
  simp only [CollatzResearch.WordTrace]
  refine ⟨7236698393687267368462601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19297862383166046315900269 7236698393687267368462601)
  ·
    refine ⟨5427523795265450526346951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7236698393687267368462601 5427523795265450526346951)
    ·
      refine ⟨8141285692898175789520427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5427523795265450526346951 8141285692898175789520427)
      ·
        refine ⟨12211928539347263684280641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8141285692898175789520427 12211928539347263684280641)
        ·
          refine ⟨9158946404510447763210481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12211928539347263684280641 9158946404510447763210481)
          ·
            refine ⟨6869209803382835822407861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9158946404510447763210481 6869209803382835822407861)
            ·
              refine ⟨643988419067140858350737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6869209803382835822407861 643988419067140858350737)
              ·
                refine ⟨482991314300355643763053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 643988419067140858350737 482991314300355643763053)
                ·
                  refine ⟨181121742862633366411145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 482991314300355643763053 181121742862633366411145)
                  ·
                    rfl

theorem cell21_793650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_793650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793650 prefixEnd_793650 := by exact prefixLift 793650
  have htrace : WordTrace (prefixWord ++ tailWord_793650) baseStart_793650 baseEnd_793650 := by
    simpa [prefixWord, tailWord_793650, baseEnd_793650] using wordTrace_append hprefix tailTrace_793650
  have hstable : (prefixWord ++ tailWord_793650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793650).length < 2 ^ (prefixWord ++ tailWord_793650).sum := by decide
  have hdescent : baseEnd_793650 < baseStart_793650 := by decide
  rcases family_descends (prefixWord ++ tailWord_793650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793661 : List Nat := [1, 4, 1, 3, 1, 2, 1, 8]
def baseStart_793661 : Nat := 118140960795 + 793661 * 2 ^ 59
def prefixEnd_793661 : Nat := 4983230072969 + 3 ^ 40 * 793661 * 2
def baseEnd_793661 : Nat := 60374751070833263909263

theorem tailTrace_793661 : CollatzResearch.WordTrace tailWord_793661 prefixEnd_793661 60374751070833263909263 := by
  unfold tailWord_793661
  simp only [CollatzResearch.WordTrace]
  refine ⟨28947194777709218352500837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19298129851806145568333891 28947194777709218352500837)
  ·
    refine ⟨5427599020820478441093907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28947194777709218352500837 5427599020820478441093907)
    ·
      refine ⟨8141398531230717661640861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5427599020820478441093907 8141398531230717661640861)
      ·
        refine ⟨3053024449211519123115323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8141398531230717661640861 3053024449211519123115323)
        ·
          refine ⟨4579536673817278684672985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3053024449211519123115323 4579536673817278684672985)
          ·
            refine ⟨3434652505362959013504739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4579536673817278684672985 3434652505362959013504739)
            ·
              refine ⟨5151978758044438520257109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3434652505362959013504739 5151978758044438520257109)
              ·
                refine ⟨60374751070833263909263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5151978758044438520257109 60374751070833263909263)
                ·
                  rfl

theorem cell21_793661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 8].length) (baseStart_793661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793661 prefixEnd_793661 := by exact prefixLift 793661
  have htrace : WordTrace (prefixWord ++ tailWord_793661) baseStart_793661 baseEnd_793661 := by
    simpa [prefixWord, tailWord_793661, baseEnd_793661] using wordTrace_append hprefix tailTrace_793661
  have hstable : (prefixWord ++ tailWord_793661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793661).length < 2 ^ (prefixWord ++ tailWord_793661).sum := by decide
  have hdescent : baseEnd_793661 < baseStart_793661 := by decide
  rcases family_descends (prefixWord ++ tailWord_793661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793802 : List Nat := [3, 1, 2, 1, 3, 4, 1, 3, 3]
def baseStart_793802 : Nat := 118140960795 + 793802 * 2 ^ 59
def prefixEnd_793802 : Nat := 4983230072969 + 3 ^ 40 * 793802 * 2
def baseEnd_793802 : Nat := 181156431333514879877501

theorem tailTrace_793802 : CollatzResearch.WordTrace tailWord_793802 prefixEnd_793802 181156431333514879877501 := by
  unfold tailWord_793802
  simp only [CollatzResearch.WordTrace]
  refine ⟨7238084367549599858345915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19301558313465599622255773 7238084367549599858345915)
  ·
    refine ⟨10857126551324399787518873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7238084367549599858345915 10857126551324399787518873)
    ·
      refine ⟨8142844913493299840639155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10857126551324399787518873 8142844913493299840639155)
      ·
        refine ⟨12214267370239949760958733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8142844913493299840639155 12214267370239949760958733)
        ·
          refine ⟨4580350263839981160359525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12214267370239949760958733 4580350263839981160359525)
          ·
            refine ⟨858815674469996467567411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4580350263839981160359525 858815674469996467567411)
            ·
              refine ⟨1288223511704994701351117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 858815674469996467567411 1288223511704994701351117)
              ·
                refine ⟨483083816889373013006669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1288223511704994701351117 483083816889373013006669)
                ·
                  refine ⟨181156431333514879877501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483083816889373013006669 181156431333514879877501)
                  ·
                    rfl

theorem cell21_793802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_793802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793802 prefixEnd_793802 := by exact prefixLift 793802
  have htrace : WordTrace (prefixWord ++ tailWord_793802) baseStart_793802 baseEnd_793802 := by
    simpa [prefixWord, tailWord_793802, baseEnd_793802] using wordTrace_append hprefix tailTrace_793802
  have hstable : (prefixWord ++ tailWord_793802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793802).length < 2 ^ (prefixWord ++ tailWord_793802).sum := by decide
  have hdescent : baseEnd_793802 < baseStart_793802 := by decide
  rcases family_descends (prefixWord ++ tailWord_793802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793813 : List Nat := [1, 3, 2, 4, 1, 1, 9]
def baseStart_793813 : Nat := 118140960795 + 793813 * 2 ^ 59
def prefixEnd_793813 : Nat := 4983230072969 + 3 ^ 40 * 793813 * 2
def baseEnd_793813 : Nat := 20128771298153478354905

theorem tailTrace_793813 : CollatzResearch.WordTrace tailWord_793813 prefixEnd_793813 20128771298153478354905 := by
  unfold tailWord_793813
  simp only [CollatzResearch.WordTrace]
  refine ⟨28952738673158548312034093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19301825782105698874689395 28952738673158548312034093)
  ·
    refine ⟨10857277002434455617012785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28952738673158548312034093 10857277002434455617012785)
    ·
      refine ⟨8142957751825841712759589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10857277002434455617012785 8142957751825841712759589)
      ·
        refine ⟨1526804578467345321142423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8142957751825841712759589 1526804578467345321142423)
        ·
          refine ⟨2290206867701017981713635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1526804578467345321142423 2290206867701017981713635)
          ·
            refine ⟨3435310301551526972570453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2290206867701017981713635 3435310301551526972570453)
            ·
              refine ⟨20128771298153478354905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3435310301551526972570453 20128771298153478354905)
              ·
                rfl

theorem cell21_793813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 9].length) (baseStart_793813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793813 prefixEnd_793813 := by exact prefixLift 793813
  have htrace : WordTrace (prefixWord ++ tailWord_793813) baseStart_793813 baseEnd_793813 := by
    simpa [prefixWord, tailWord_793813, baseEnd_793813] using wordTrace_append hprefix tailTrace_793813
  have hstable : (prefixWord ++ tailWord_793813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793813).length < 2 ^ (prefixWord ++ tailWord_793813).sum := by decide
  have hdescent : baseEnd_793813 < baseStart_793813 := by decide
  rcases family_descends (prefixWord ++ tailWord_793813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793906 : List Nat := [3, 2, 1, 1, 4, 2, 3, 5]
def baseStart_793906 : Nat := 118140960795 + 793906 * 2 ^ 59
def prefixEnd_793906 : Nat := 4983230072969 + 3 ^ 40 * 793906 * 2
def baseEnd_793906 : Nat := 60393388516811270047985

theorem tailTrace_793906 : CollatzResearch.WordTrace tailWord_793906 prefixEnd_793906 60393388516811270047985 := by
  unfold tailWord_793906
  simp only [CollatzResearch.WordTrace]
  refine ⟨7239032665455406298792393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19304087107881083463446381 7239032665455406298792393)
  ·
    refine ⟨5429274499091554724094295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7239032665455406298792393 5429274499091554724094295)
    ·
      refine ⟨8143911748637332086141443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5429274499091554724094295 8143911748637332086141443)
      ·
        refine ⟨12215867622955998129212165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8143911748637332086141443 12215867622955998129212165)
        ·
          refine ⟨2290475179304249649227281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12215867622955998129212165 2290475179304249649227281)
          ·
            refine ⟨1717856384478187236920461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2290475179304249649227281 1717856384478187236920461)
            ·
              refine ⟨644196144179320213845173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1717856384478187236920461 644196144179320213845173)
              ·
                refine ⟨60393388516811270047985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 644196144179320213845173 60393388516811270047985)
                ·
                  rfl

theorem cell21_793906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_793906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793906 prefixEnd_793906 := by exact prefixLift 793906
  have htrace : WordTrace (prefixWord ++ tailWord_793906) baseStart_793906 baseEnd_793906 := by
    simpa [prefixWord, tailWord_793906, baseEnd_793906] using wordTrace_append hprefix tailTrace_793906
  have hstable : (prefixWord ++ tailWord_793906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793906).length < 2 ^ (prefixWord ++ tailWord_793906).sum := by decide
  have hdescent : baseEnd_793906 < baseStart_793906 := by decide
  rcases family_descends (prefixWord ++ tailWord_793906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793934 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_793934 : Nat := 118140960795 + 793934 * 2 ^ 59
def prefixEnd_793934 : Nat := 4983230072969 + 3 ^ 40 * 793934 * 2
def baseEnd_793934 : Nat := 181186555531911983677231

theorem tailTrace_793934 : CollatzResearch.WordTrace tailWord_793934 prefixEnd_793934 181186555531911983677231 := by
  unfold tailWord_793934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3619643988215023247148607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19304767937146790651459237 3619643988215023247148607)
  ·
    refine ⟨5429465982322534870722911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3619643988215023247148607 5429465982322534870722911)
    ·
      refine ⟨8144198973483802306084367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5429465982322534870722911 8144198973483802306084367)
      ·
        refine ⟨12216298460225703459126551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8144198973483802306084367 12216298460225703459126551)
        ·
          refine ⟨18324447690338555188689827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12216298460225703459126551 18324447690338555188689827)
          ·
            refine ⟨27486671535507832783034741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18324447690338555188689827 27486671535507832783034741)
            ·
              refine ⟨2576875456453859323409507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27486671535507832783034741 2576875456453859323409507)
              ·
                refine ⟨3865313184680788985114261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2576875456453859323409507 3865313184680788985114261)
                ·
                  refine ⟨181186555531911983677231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3865313184680788985114261 181186555531911983677231)
                  ·
                    rfl

theorem cell21_793934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_793934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793934 prefixEnd_793934 := by exact prefixLift 793934
  have htrace : WordTrace (prefixWord ++ tailWord_793934) baseStart_793934 baseEnd_793934 := by
    simpa [prefixWord, tailWord_793934, baseEnd_793934] using wordTrace_append hprefix tailTrace_793934
  have hstable : (prefixWord ++ tailWord_793934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793934).length < 2 ^ (prefixWord ++ tailWord_793934).sum := by decide
  have hdescent : baseEnd_793934 < baseStart_793934 := by decide
  rcases family_descends (prefixWord ++ tailWord_793934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_793965 : List Nat := [1, 5, 1, 1, 1, 4, 1, 7]
def baseStart_793965 : Nat := 118140960795 + 793965 * 2 ^ 59
def prefixEnd_793965 : Nat := 4983230072969 + 3 ^ 40 * 793965 * 2
def baseEnd_793965 : Nat := 60397876718087606220167

theorem tailTrace_793965 : CollatzResearch.WordTrace tailWord_793965 prefixEnd_793965 60397876718087606220167 := by
  unfold tailWord_793965
  simp only [CollatzResearch.WordTrace]
  refine ⟨28958282568607878271567349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19305521712405252181044899 28958282568607878271567349)
  ·
    refine ⟨2714838990806988587959439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28958282568607878271567349 2714838990806988587959439)
    ·
      refine ⟨4072258486210482881939159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2714838990806988587959439 4072258486210482881939159)
      ·
        refine ⟨6108387729315724322908739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4072258486210482881939159 6108387729315724322908739)
        ·
          refine ⟨9162581593973586484363109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6108387729315724322908739 9162581593973586484363109)
          ·
            refine ⟨1717984048870047465818083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9162581593973586484363109 1717984048870047465818083)
            ·
              refine ⟨2576976073305071198727125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1717984048870047465818083 2576976073305071198727125)
              ·
                refine ⟨60397876718087606220167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2576976073305071198727125 60397876718087606220167)
                ·
                  rfl

theorem cell21_793965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 7].length) (baseStart_793965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_793965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_793965 prefixEnd_793965 := by exact prefixLift 793965
  have htrace : WordTrace (prefixWord ++ tailWord_793965) baseStart_793965 baseEnd_793965 := by
    simpa [prefixWord, tailWord_793965, baseEnd_793965] using wordTrace_append hprefix tailTrace_793965
  have hstable : (prefixWord ++ tailWord_793965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_793965).length < 2 ^ (prefixWord ++ tailWord_793965).sum := by decide
  have hdescent : baseEnd_793965 < baseStart_793965 := by decide
  rcases family_descends (prefixWord ++ tailWord_793965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794002 : List Nat := [3, 2, 3, 3, 1, 2, 2, 1, 4]
def baseStart_794002 : Nat := 118140960795 + 794002 * 2 ^ 59
def prefixEnd_794002 : Nat := 4983230072969 + 3 ^ 40 * 794002 * 2
def baseEnd_794002 : Nat := 181202074058358976543759

theorem tailTrace_794002 : CollatzResearch.WordTrace tailWord_794002 prefixEnd_794002 181202074058358976543759 := by
  unfold tailWord_794002
  simp only [CollatzResearch.WordTrace]
  refine ⟨7239908017368458397666065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19306421379649222393776173 7239908017368458397666065)
  ·
    refine ⟨5429931013026343798249549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7239908017368458397666065 5429931013026343798249549)
    ·
      refine ⟨2036224129884878924343581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5429931013026343798249549 2036224129884878924343581)
      ·
        refine ⟨763584048706829596628843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2036224129884878924343581 763584048706829596628843)
        ·
          refine ⟨1145376073060244394943265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 763584048706829596628843 1145376073060244394943265)
          ·
            refine ⟨859032054795183296207449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1145376073060244394943265 859032054795183296207449)
            ·
              refine ⟨644274041096387472155587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 859032054795183296207449 644274041096387472155587)
              ·
                refine ⟨966411061644581208233381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644274041096387472155587 966411061644581208233381)
                ·
                  refine ⟨181202074058358976543759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 966411061644581208233381 181202074058358976543759)
                  ·
                    rfl

theorem cell21_794002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_794002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_794002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_794002 prefixEnd_794002 := by exact prefixLift 794002
  have htrace : WordTrace (prefixWord ++ tailWord_794002) baseStart_794002 baseEnd_794002 := by
    simpa [prefixWord, tailWord_794002, baseEnd_794002] using wordTrace_append hprefix tailTrace_794002
  have hstable : (prefixWord ++ tailWord_794002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794002).length < 2 ^ (prefixWord ++ tailWord_794002).sum := by decide
  have hdescent : baseEnd_794002 < baseStart_794002 := by decide
  rcases family_descends (prefixWord ++ tailWord_794002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794041 : List Nat := [1, 2, 1, 4, 5, 8]
def baseStart_794041 : Nat := 118140960795 + 794041 * 2 ^ 59
def prefixEnd_794041 : Nat := 4983230072969 + 3 ^ 40 * 794041 * 2
def baseEnd_794041 : Nat := 6711517569989021310877

theorem tailTrace_794041 : CollatzResearch.WordTrace tailWord_794041 prefixEnd_794041 6711517569989021310877 := by
  unfold tailWord_794041
  simp only [CollatzResearch.WordTrace]
  refine ⟨28961054516332543251333977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19307369677555028834222651 28961054516332543251333977)
  ·
    refine ⟨21720790887249407438500483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28961054516332543251333977 21720790887249407438500483)
    ·
      refine ⟨32581186330874111157750725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21720790887249407438500483 32581186330874111157750725)
      ·
        refine ⟨6108972437038895842078261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32581186330874111157750725 6108972437038895842078261)
        ·
          refine ⟨572716165972396485194837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6108972437038895842078261 572716165972396485194837)
          ·
            refine ⟨6711517569989021310877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 572716165972396485194837 6711517569989021310877)
            ·
              rfl

theorem cell21_794041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 8].length) (baseStart_794041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_794041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_794041 prefixEnd_794041 := by exact prefixLift 794041
  have htrace : WordTrace (prefixWord ++ tailWord_794041) baseStart_794041 baseEnd_794041 := by
    simpa [prefixWord, tailWord_794041, baseEnd_794041] using wordTrace_append hprefix tailTrace_794041
  have hstable : (prefixWord ++ tailWord_794041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794041).length < 2 ^ (prefixWord ++ tailWord_794041).sum := by decide
  have hdescent : baseEnd_794041 < baseStart_794041 := by decide
  rcases family_descends (prefixWord ++ tailWord_794041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794044 : List Nat := [2, 2, 2, 4, 2, 1, 2, 2, 4]
def baseStart_794044 : Nat := 118140960795 + 794044 * 2 ^ 59
def prefixEnd_794044 : Nat := 4983230072969 + 3 ^ 40 * 794044 * 2
def baseEnd_794044 : Nat := 181211659030576236843673

theorem tailTrace_794044 : CollatzResearch.WordTrace tailWord_794044 prefixEnd_794044 181211659030576236843673 := by
  unfold tailWord_794044
  simp only [CollatzResearch.WordTrace]
  refine ⟨14480581967660837381846593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19307442623547783175795457 14480581967660837381846593)
  ·
    refine ⟨10860436475745628036384945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14480581967660837381846593 10860436475745628036384945)
    ·
      refine ⟨8145327356809221027288709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10860436475745628036384945 8145327356809221027288709)
      ·
        refine ⟨1527248879401728942616633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8145327356809221027288709 1527248879401728942616633)
        ·
          refine ⟨1145436659551296706962475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1527248879401728942616633 1145436659551296706962475)
          ·
            refine ⟨1718154989326945060443713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1145436659551296706962475 1718154989326945060443713)
            ·
              refine ⟨1288616241995208795332785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1718154989326945060443713 1288616241995208795332785)
              ·
                refine ⟨966462181496406596499589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1288616241995208795332785 966462181496406596499589)
                ·
                  refine ⟨181211659030576236843673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 966462181496406596499589 181211659030576236843673)
                  ·
                    rfl

theorem cell21_794044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_794044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_794044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_794044 prefixEnd_794044 := by exact prefixLift 794044
  have htrace : WordTrace (prefixWord ++ tailWord_794044) baseStart_794044 baseEnd_794044 := by
    simpa [prefixWord, tailWord_794044, baseEnd_794044] using wordTrace_append hprefix tailTrace_794044
  have hstable : (prefixWord ++ tailWord_794044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794044).length < 2 ^ (prefixWord ++ tailWord_794044).sum := by decide
  have hdescent : baseEnd_794044 < baseStart_794044 := by decide
  rcases family_descends (prefixWord ++ tailWord_794044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794050 : List Nat := [3, 5, 2, 1, 2, 1, 1, 6]
def baseStart_794050 : Nat := 118140960795 + 794050 * 2 ^ 59
def prefixEnd_794050 : Nat := 4983230072969 + 3 ^ 40 * 794050 * 2
def baseEnd_794050 : Nat := 60404342770773853247887

theorem tailTrace_794050 : CollatzResearch.WordTrace tailWord_794050 prefixEnd_794050 60404342770773853247887 := by
  unfold tailWord_794050
  simp only [CollatzResearch.WordTrace]
  refine ⟨7240345693324984447102901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19307588515533291858941069 7240345693324984447102901)
  ·
    refine ⟨678782408749217291915897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7240345693324984447102901 678782408749217291915897)
    ·
      refine ⟨509086806561912968936923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 678782408749217291915897 509086806561912968936923)
      ·
        refine ⟨763630209842869453405385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509086806561912968936923 763630209842869453405385)
        ·
          refine ⟨572722657382152090054039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 763630209842869453405385 572722657382152090054039)
          ·
            refine ⟨859083986073228135081059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 572722657382152090054039 859083986073228135081059)
            ·
              refine ⟨1288625979109842202621589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859083986073228135081059 1288625979109842202621589)
              ·
                refine ⟨60404342770773853247887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1288625979109842202621589 60404342770773853247887)
                ·
                  rfl

theorem cell21_794050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_794050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_794050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_794050 prefixEnd_794050 := by exact prefixLift 794050
  have htrace : WordTrace (prefixWord ++ tailWord_794050) baseStart_794050 baseEnd_794050 := by
    simpa [prefixWord, tailWord_794050, baseEnd_794050] using wordTrace_append hprefix tailTrace_794050
  have hstable : (prefixWord ++ tailWord_794050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794050).length < 2 ^ (prefixWord ++ tailWord_794050).sum := by decide
  have hdescent : baseEnd_794050 < baseStart_794050 := by decide
  rcases family_descends (prefixWord ++ tailWord_794050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794055 : List Nat := [1, 1, 4, 1, 1, 3, 2, 3, 5]
def baseStart_794055 : Nat := 118140960795 + 794055 * 2 ^ 59
def prefixEnd_794055 : Nat := 4983230072969 + 3 ^ 40 * 794055 * 2
def baseEnd_794055 : Nat := 181214169380442662160317

theorem tailTrace_794055 : CollatzResearch.WordTrace tailWord_794055 prefixEnd_794055 181214169380442662160317 := by
  unfold tailWord_794055
  simp only [CollatzResearch.WordTrace]
  refine ⟨28961565138281823642343619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19307710092187882428229079 28961565138281823642343619)
  ·
    refine ⟨43442347707422735463515429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28961565138281823642343619 43442347707422735463515429)
    ·
      refine ⟨8145440195141762899409143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43442347707422735463515429 8145440195141762899409143)
      ·
        refine ⟨12218160292712644349113715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8145440195141762899409143 12218160292712644349113715)
        ·
          refine ⟨18327240439068966523670573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12218160292712644349113715 18327240439068966523670573)
          ·
            refine ⟨6872715164650862446376465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18327240439068966523670573 6872715164650862446376465)
            ·
              refine ⟨5154536373488146834782349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6872715164650862446376465 5154536373488146834782349)
              ·
                refine ⟨1932951140058055063043381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5154536373488146834782349 1932951140058055063043381)
                ·
                  refine ⟨181214169380442662160317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1932951140058055063043381 181214169380442662160317)
                  ·
                    rfl

theorem cell21_794055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 5].length) (baseStart_794055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_794055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_794055 prefixEnd_794055 := by exact prefixLift 794055
  have htrace : WordTrace (prefixWord ++ tailWord_794055) baseStart_794055 baseEnd_794055 := by
    simpa [prefixWord, tailWord_794055, baseEnd_794055] using wordTrace_append hprefix tailTrace_794055
  have hstable : (prefixWord ++ tailWord_794055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794055).length < 2 ^ (prefixWord ++ tailWord_794055).sum := by decide
  have hdescent : baseEnd_794055 < baseStart_794055 := by decide
  rcases family_descends (prefixWord ++ tailWord_794055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794131 : List Nat := [1, 1, 1, 2, 1, 6, 2, 2, 5]
def baseStart_794131 : Nat := 118140960795 + 794131 * 2 ^ 59
def prefixEnd_794131 : Nat := 4983230072969 + 3 ^ 40 * 794131 * 2
def baseEnd_794131 : Nat := 181231513615883418893495

theorem tailTrace_794131 : CollatzResearch.WordTrace tailWord_794131 prefixEnd_794131 181231513615883418893495 := by
  unfold tailWord_794131
  simp only [CollatzResearch.WordTrace]
  refine ⟨28964337086006488622110247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19309558057337659081406831 28964337086006488622110247)
  ·
    refine ⟨43446505629009732933165371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28964337086006488622110247 43446505629009732933165371)
    ·
      refine ⟨65169758443514599399748057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43446505629009732933165371 65169758443514599399748057)
      ·
        refine ⟨48877318832635949549811043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65169758443514599399748057 48877318832635949549811043)
        ·
          refine ⟨73315978248953924324716565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48877318832635949549811043 73315978248953924324716565)
          ·
            refine ⟨3436686480419715202721089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73315978248953924324716565 3436686480419715202721089)
            ·
              refine ⟨2577514860314786402040817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3436686480419715202721089 2577514860314786402040817)
              ·
                refine ⟨1933136145236089801530613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2577514860314786402040817 1933136145236089801530613)
                ·
                  refine ⟨181231513615883418893495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1933136145236089801530613 181231513615883418893495)
                  ·
                    rfl

theorem cell21_794131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 5].length) (baseStart_794131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_794131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_794131 prefixEnd_794131 := by exact prefixLift 794131
  have htrace : WordTrace (prefixWord ++ tailWord_794131) baseStart_794131 baseEnd_794131 := by
    simpa [prefixWord, tailWord_794131, baseEnd_794131] using wordTrace_append hprefix tailTrace_794131
  have hstable : (prefixWord ++ tailWord_794131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794131).length < 2 ^ (prefixWord ++ tailWord_794131).sum := by decide
  have hdescent : baseEnd_794131 < baseStart_794131 := by decide
  rcases family_descends (prefixWord ++ tailWord_794131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794162 : List Nat := [3, 2, 1, 1, 2, 1, 1, 6, 4]
def baseStart_794162 : Nat := 118140960795 + 794162 * 2 ^ 59
def prefixEnd_794162 : Nat := 4983230072969 + 3 ^ 40 * 794162 * 2
def baseEnd_794162 : Nat := 181238588238234253876765

theorem tailTrace_794162 : CollatzResearch.WordTrace tailWord_794162 prefixEnd_794162 181238588238234253876765 := by
  unfold tailWord_794162
  simp only [CollatzResearch.WordTrace]
  refine ⟨7241366937223545229122185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19310311832596120610992493 7241366937223545229122185)
  ·
    refine ⟨5431025202917658921841639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7241366937223545229122185 5431025202917658921841639)
    ·
      refine ⟨8146537804376488382762459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5431025202917658921841639 8146537804376488382762459)
      ·
        refine ⟨12219806706564732574143689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8146537804376488382762459 12219806706564732574143689)
        ·
          refine ⟨9164855029923549430607767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12219806706564732574143689 9164855029923549430607767)
          ·
            refine ⟨13747282544885324145911651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9164855029923549430607767 13747282544885324145911651)
            ·
              refine ⟨20620923817327986218867477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13747282544885324145911651 20620923817327986218867477)
              ·
                refine ⟨966605803937249354009413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20620923817327986218867477 966605803937249354009413)
                ·
                  refine ⟨181238588238234253876765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 966605803937249354009413 181238588238234253876765)
                  ·
                    rfl

theorem cell21_794162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_794162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_794162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_794162 prefixEnd_794162 := by exact prefixLift 794162
  have htrace : WordTrace (prefixWord ++ tailWord_794162) baseStart_794162 baseEnd_794162 := by
    simpa [prefixWord, tailWord_794162, baseEnd_794162] using wordTrace_append hprefix tailTrace_794162
  have hstable : (prefixWord ++ tailWord_794162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794162).length < 2 ^ (prefixWord ++ tailWord_794162).sum := by decide
  have hdescent : baseEnd_794162 < baseStart_794162 := by decide
  rcases family_descends (prefixWord ++ tailWord_794162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794258 : List Nat := [3, 2, 3, 1, 3, 1, 2, 3, 3]
def baseStart_794258 : Nat := 118140960795 + 794258 * 2 ^ 59
def prefixEnd_794258 : Nat := 4983230072969 + 3 ^ 40 * 794258 * 2
def baseEnd_794258 : Nat := 181260496746159420276569

theorem tailTrace_794258 : CollatzResearch.WordTrace tailWord_794258 prefixEnd_794258 181260496746159420276569 := by
  unfold tailWord_794258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7242242289136597327995857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19312646104364259541322285 7242242289136597327995857)
  ·
    refine ⟨5431681716852447995996893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7242242289136597327995857 5431681716852447995996893)
    ·
      refine ⟨2036880643819667998498835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5431681716852447995996893 2036880643819667998498835)
      ·
        refine ⟨3055320965729501997748253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2036880643819667998498835 3055320965729501997748253)
        ·
          refine ⟨1145745362148563249155595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3055320965729501997748253 1145745362148563249155595)
          ·
            refine ⟨1718618043222844873733393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1145745362148563249155595 1718618043222844873733393)
            ·
              refine ⟨1288963532417133655300045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1718618043222844873733393 1288963532417133655300045)
              ·
                refine ⟨483361324656425120737517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1288963532417133655300045 483361324656425120737517)
                ·
                  refine ⟨181260496746159420276569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483361324656425120737517 181260496746159420276569)
                  ·
                    rfl

theorem cell21_794258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_794258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_794258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_794258 prefixEnd_794258 := by exact prefixLift 794258
  have htrace : WordTrace (prefixWord ++ tailWord_794258) baseStart_794258 baseEnd_794258 := by
    simpa [prefixWord, tailWord_794258, baseEnd_794258] using wordTrace_append hprefix tailTrace_794258
  have hstable : (prefixWord ++ tailWord_794258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794258).length < 2 ^ (prefixWord ++ tailWord_794258).sum := by decide
  have hdescent : baseEnd_794258 < baseStart_794258 := by decide
  rcases family_descends (prefixWord ++ tailWord_794258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794376 : List Nat := [2, 1, 3, 2, 2, 1, 2, 5, 3]
def baseStart_794376 : Nat := 118140960795 + 794376 * 2 ^ 59
def prefixEnd_794376 : Nat := 4983230072969 + 3 ^ 40 * 794376 * 2
def baseEnd_794376 : Nat := 181287425953817437309661

theorem tailTrace_794376 : CollatzResearch.WordTrace tailWord_794376 prefixEnd_794376 181287425953817437309661 := by
  unfold tailWord_794376
  simp only [CollatzResearch.WordTrace]
  refine ⟨14486636485059447732389491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19315515313412596976519321 14486636485059447732389491)
  ·
    refine ⟨21729954727589171598584237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14486636485059447732389491 21729954727589171598584237)
    ·
      refine ⟨8148733022845939349469089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21729954727589171598584237 8148733022845939349469089)
      ·
        refine ⟨6111549767134454512101817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8148733022845939349469089 6111549767134454512101817)
        ·
          refine ⟨4583662325350840884076363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6111549767134454512101817 4583662325350840884076363)
          ·
            refine ⟨6875493488026261326114545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4583662325350840884076363 6875493488026261326114545)
            ·
              refine ⟨5156620116019695994585909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6875493488026261326114545 5156620116019695994585909)
              ·
                refine ⟨483433135876846499492429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5156620116019695994585909 483433135876846499492429)
                ·
                  refine ⟨181287425953817437309661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483433135876846499492429 181287425953817437309661)
                  ·
                    rfl

theorem cell21_794376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 3].length) (baseStart_794376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_794376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_794376 prefixEnd_794376 := by exact prefixLift 794376
  have htrace : WordTrace (prefixWord ++ tailWord_794376) baseStart_794376 baseEnd_794376 := by
    simpa [prefixWord, tailWord_794376, baseEnd_794376] using wordTrace_append hprefix tailTrace_794376
  have hstable : (prefixWord ++ tailWord_794376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794376).length < 2 ^ (prefixWord ++ tailWord_794376).sum := by decide
  have hdescent : baseEnd_794376 < baseStart_794376 := by decide
  rcases family_descends (prefixWord ++ tailWord_794376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794438 : List Nat := [6, 1, 1, 2, 1, 2, 8]
def baseStart_794438 : Nat := 118140960795 + 794438 * 2 ^ 59
def prefixEnd_794438 : Nat := 4983230072969 + 3 ^ 40 * 794438 * 2
def baseEnd_794438 : Nat := 20144619466502123030689

theorem tailTrace_794438 : CollatzResearch.WordTrace tailWord_794438 prefixEnd_794438 20144619466502123030689 := by
  unfold tailWord_794438
  simp only [CollatzResearch.WordTrace]
  refine ⟨905485446746696251672999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 19317022863929520035690645 905485446746696251672999)
  ·
    refine ⟨1358228170120044377509499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 905485446746696251672999 1358228170120044377509499)
    ·
      refine ⟨2037342255180066566264249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1358228170120044377509499 2037342255180066566264249)
      ·
        refine ⟨1528006691385049924698187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2037342255180066566264249 1528006691385049924698187)
        ·
          refine ⟨2292010037077574887047281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1528006691385049924698187 2292010037077574887047281)
          ·
            refine ⟨1719007527808181165285461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2292010037077574887047281 1719007527808181165285461)
            ·
              refine ⟨20144619466502123030689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1719007527808181165285461 20144619466502123030689)
              ·
                rfl

theorem cell21_794438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 8].length) (baseStart_794438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_794438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_794438 prefixEnd_794438 := by exact prefixLift 794438
  have htrace : WordTrace (prefixWord ++ tailWord_794438) baseStart_794438 baseEnd_794438 := by
    simpa [prefixWord, tailWord_794438, baseEnd_794438] using wordTrace_append hprefix tailTrace_794438
  have hstable : (prefixWord ++ tailWord_794438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794438).length < 2 ^ (prefixWord ++ tailWord_794438).sum := by decide
  have hdescent : baseEnd_794438 < baseStart_794438 := by decide
  rcases family_descends (prefixWord ++ tailWord_794438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794452 : List Nat := [2, 4, 1, 1, 3, 2, 2, 1, 5]
def baseStart_794452 : Nat := 118140960795 + 794452 * 2 ^ 59
def prefixEnd_794452 : Nat := 4983230072969 + 3 ^ 40 * 794452 * 2
def baseEnd_794452 : Nat := 181304770189258194042839

theorem tailTrace_794452 : CollatzResearch.WordTrace tailWord_794452 prefixEnd_794452 181304770189258194042839 := by
  unfold tailWord_794452
  simp only [CollatzResearch.WordTrace]
  refine ⟨14488022458921780222272805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19317363278562373629697073 14488022458921780222272805)
  ·
    refine ⟨2716504211047833791676151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14488022458921780222272805 2716504211047833791676151)
    ·
      refine ⟨4074756316571750687514227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2716504211047833791676151 4074756316571750687514227)
      ·
        refine ⟨6112134474857626031271341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4074756316571750687514227 6112134474857626031271341)
        ·
          refine ⟨2292050428071609761726753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6112134474857626031271341 2292050428071609761726753)
          ·
            refine ⟨1719037821053707321295065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2292050428071609761726753 1719037821053707321295065)
            ·
              refine ⟨1289278365790280490971299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1719037821053707321295065 1289278365790280490971299)
              ·
                refine ⟨1933917548685420736456949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1289278365790280490971299 1933917548685420736456949)
                ·
                  refine ⟨181304770189258194042839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1933917548685420736456949 181304770189258194042839)
                  ·
                    rfl

theorem cell21_794452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_794452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_794452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_794452 prefixEnd_794452 := by exact prefixLift 794452
  have htrace : WordTrace (prefixWord ++ tailWord_794452) baseStart_794452 baseEnd_794452 := by
    simpa [prefixWord, tailWord_794452, baseEnd_794452] using wordTrace_append hprefix tailTrace_794452
  have hstable : (prefixWord ++ tailWord_794452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794452).length < 2 ^ (prefixWord ++ tailWord_794452).sum := by decide
  have hdescent : baseEnd_794452 < baseStart_794452 := by decide
  rcases family_descends (prefixWord ++ tailWord_794452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794556 : List Nat := [2, 2, 2, 5, 10]
def baseStart_794556 : Nat := 118140960795 + 794556 * 2 ^ 59
def prefixEnd_794556 : Nat := 4983230072969 + 3 ^ 40 * 794556 * 2
def baseEnd_794556 : Nat := 2238623511187371905053

theorem tailTrace_794556 : CollatzResearch.WordTrace tailWord_794556 prefixEnd_794556 2238623511187371905053 := by
  unfold tailWord_794556
  simp only [CollatzResearch.WordTrace]
  refine ⟨14489919054733393103165761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19319892072977857470887681 14489919054733393103165761)
  ·
    refine ⟨10867439291050044827374321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14489919054733393103165761 10867439291050044827374321)
    ·
      refine ⟨8150579468287533620530741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10867439291050044827374321 8150579468287533620530741)
      ·
        refine ⟨764116825151956276924757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8150579468287533620530741 764116825151956276924757)
        ·
          refine ⟨2238623511187371905053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 764116825151956276924757 2238623511187371905053)
          ·
            rfl

theorem cell21_794556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 10].length) (baseStart_794556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_794556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_794556 prefixEnd_794556 := by exact prefixLift 794556
  have htrace : WordTrace (prefixWord ++ tailWord_794556) baseStart_794556 baseEnd_794556 := by
    simpa [prefixWord, tailWord_794556, baseEnd_794556] using wordTrace_append hprefix tailTrace_794556
  have hstable : (prefixWord ++ tailWord_794556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794556).length < 2 ^ (prefixWord ++ tailWord_794556).sum := by decide
  have hdescent : baseEnd_794556 < baseStart_794556 := by decide
  rcases family_descends (prefixWord ++ tailWord_794556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794677 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 6]
def baseStart_794677 : Nat := 118140960795 + 794677 * 2 ^ 59
def prefixEnd_794677 : Nat := 4983230072969 + 3 ^ 40 * 794677 * 2
def baseEnd_794677 : Nat := 181356118254707802792379

theorem tailTrace_794677 : CollatzResearch.WordTrace tailWord_794677 prefixEnd_794677 181356118254707802792379 := by
  unfold tailWord_794677
  simp only [CollatzResearch.WordTrace]
  refine ⟨28984251342028423871486285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19322834228018949247657523 28984251342028423871486285)
  ·
    refine ⟨10869094253260658951807357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28984251342028423871486285 10869094253260658951807357)
    ·
      refine ⟨4075910344972747106927759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10869094253260658951807357 4075910344972747106927759)
      ·
        refine ⟨6113865517459120660391639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4075910344972747106927759 6113865517459120660391639)
        ·
          refine ⟨9170798276188680990587459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6113865517459120660391639 9170798276188680990587459)
          ·
            refine ⟨13756197414283021485881189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9170798276188680990587459 13756197414283021485881189)
            ·
              refine ⟨2579287015178066528602723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13756197414283021485881189 2579287015178066528602723)
              ·
                refine ⟨3868930522767099792904085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2579287015178066528602723 3868930522767099792904085)
                ·
                  refine ⟨181356118254707802792379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3868930522767099792904085 181356118254707802792379)
                  ·
                    rfl

theorem cell21_794677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_794677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_794677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_794677 prefixEnd_794677 := by exact prefixLift 794677
  have htrace : WordTrace (prefixWord ++ tailWord_794677) baseStart_794677 baseEnd_794677 := by
    simpa [prefixWord, tailWord_794677, baseEnd_794677] using wordTrace_append hprefix tailTrace_794677
  have hstable : (prefixWord ++ tailWord_794677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794677).length < 2 ^ (prefixWord ++ tailWord_794677).sum := by decide
  have hdescent : baseEnd_794677 < baseStart_794677 := by decide
  rcases family_descends (prefixWord ++ tailWord_794677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794680 : List Nat := [2, 1, 2, 1, 6, 2, 1, 1, 5]
def baseStart_794680 : Nat := 118140960795 + 794680 * 2 ^ 59
def prefixEnd_794680 : Nat := 4983230072969 + 3 ^ 40 * 794680 * 2
def baseEnd_794680 : Nat := 181356802895580464242373

theorem tailTrace_794680 : CollatzResearch.WordTrace tailWord_794680 prefixEnd_794680 181356802895580464242373 := by
  unfold tailWord_794680
  simp only [CollatzResearch.WordTrace]
  refine ⟨14492180380508777691922747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19322907174011703589230329 14492180380508777691922747)
  ·
    refine ⟨21738270570763166537884121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14492180380508777691922747 21738270570763166537884121)
    ·
      refine ⟨16303702928072374903413091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21738270570763166537884121 16303702928072374903413091)
      ·
        refine ⟨24455554392108562355119637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16303702928072374903413091 24455554392108562355119637)
        ·
          refine ⟨1146354112130088860396233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24455554392108562355119637 1146354112130088860396233)
          ·
            refine ⟨859765584097566645297175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1146354112130088860396233 859765584097566645297175)
            ·
              refine ⟨1289648376146349967945763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859765584097566645297175 1289648376146349967945763)
              ·
                refine ⟨1934472564219524951918645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1289648376146349967945763 1934472564219524951918645)
                ·
                  refine ⟨181356802895580464242373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1934472564219524951918645 181356802895580464242373)
                  ·
                    rfl

theorem cell21_794680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 5].length) (baseStart_794680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_794680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_794680 prefixEnd_794680 := by exact prefixLift 794680
  have htrace : WordTrace (prefixWord ++ tailWord_794680) baseStart_794680 baseEnd_794680 := by
    simpa [prefixWord, tailWord_794680, baseEnd_794680] using wordTrace_append hprefix tailTrace_794680
  have hstable : (prefixWord ++ tailWord_794680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794680).length < 2 ^ (prefixWord ++ tailWord_794680).sum := by decide
  have hdescent : baseEnd_794680 < baseStart_794680 := by decide
  rcases family_descends (prefixWord ++ tailWord_794680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794818 : List Nat := [3, 5, 1, 1, 1, 2, 1, 7]
def baseStart_794818 : Nat := 118140960795 + 794818 * 2 ^ 59
def prefixEnd_794818 : Nat := 4983230072969 + 3 ^ 40 * 794818 * 2
def baseEnd_794818 : Nat := 60462765458574296980697

theorem tailTrace_794818 : CollatzResearch.WordTrace tailWord_794818 prefixEnd_794818 60462765458574296980697 := by
  unfold tailWord_794818
  simp only [CollatzResearch.WordTrace]
  refine ⟨7247348508629401238092277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19326262689678403301579405 7247348508629401238092277)
  ·
    refine ⟨679438922684006366071151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7247348508629401238092277 679438922684006366071151)
    ·
      refine ⟨1019158384026009549106727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 679438922684006366071151 1019158384026009549106727)
      ·
        refine ⟨1528737576039014323660091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1019158384026009549106727 1528737576039014323660091)
        ·
          refine ⟨2293106364058521485490137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1528737576039014323660091 2293106364058521485490137)
          ·
            refine ⟨1719829773043891114117603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2293106364058521485490137 1719829773043891114117603)
            ·
              refine ⟨2579744659565836671176405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1719829773043891114117603 2579744659565836671176405)
              ·
                refine ⟨60462765458574296980697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2579744659565836671176405 60462765458574296980697)
                ·
                  rfl

theorem cell21_794818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_794818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_794818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_794818 prefixEnd_794818 := by exact prefixLift 794818
  have htrace : WordTrace (prefixWord ++ tailWord_794818) baseStart_794818 baseEnd_794818 := by
    simpa [prefixWord, tailWord_794818, baseEnd_794818] using wordTrace_append hprefix tailTrace_794818
  have hstable : (prefixWord ++ tailWord_794818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794818).length < 2 ^ (prefixWord ++ tailWord_794818).sum := by decide
  have hdescent : baseEnd_794818 < baseStart_794818 := by decide
  rcases family_descends (prefixWord ++ tailWord_794818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794863 : List Nat := [1, 1, 2, 1, 6, 3, 2, 1, 4]
def baseStart_794863 : Nat := 118140960795 + 794863 * 2 ^ 59
def prefixEnd_794863 : Nat := 4983230072969 + 3 ^ 40 * 794863 * 2
def baseEnd_794863 : Nat := 181398565988812812691999

theorem tailTrace_794863 : CollatzResearch.WordTrace tailWord_794863 prefixEnd_794863 181398565988812812691999 := by
  unfold tailWord_794863
  simp only [CollatzResearch.WordTrace]
  refine ⟨28991035319354577637757243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19327356879569718425171495 28991035319354577637757243)
  ·
    refine ⟨43486552979031866456635865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28991035319354577637757243 43486552979031866456635865)
    ·
      refine ⟨32614914734273899842476899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43486552979031866456635865 32614914734273899842476899)
      ·
        refine ⟨48922372101410849763715349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32614914734273899842476899 48922372101410849763715349)
        ·
          refine ⟨2293236192253633582674157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48922372101410849763715349 2293236192253633582674157)
          ·
            refine ⟨859963572095112593502809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2293236192253633582674157 859963572095112593502809)
            ·
              refine ⟨644972679071334445127107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 859963572095112593502809 644972679071334445127107)
              ·
                refine ⟨967459018607001667690661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644972679071334445127107 967459018607001667690661)
                ·
                  refine ⟨181398565988812812691999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 967459018607001667690661 181398565988812812691999)
                  ·
                    rfl

theorem cell21_794863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 4].length) (baseStart_794863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_794863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_794863 prefixEnd_794863 := by exact prefixLift 794863
  have htrace : WordTrace (prefixWord ++ tailWord_794863) baseStart_794863 baseEnd_794863 := by
    simpa [prefixWord, tailWord_794863, baseEnd_794863] using wordTrace_append hprefix tailTrace_794863
  have hstable : (prefixWord ++ tailWord_794863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794863).length < 2 ^ (prefixWord ++ tailWord_794863).sum := by decide
  have hdescent : baseEnd_794863 < baseStart_794863 := by decide
  rcases family_descends (prefixWord ++ tailWord_794863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794891 : List Nat := [1, 1, 1, 1, 5, 2, 2, 5, 3]
def baseStart_794891 : Nat := 118140960795 + 794891 * 2 ^ 59
def prefixEnd_794891 : Nat := 4983230072969 + 3 ^ 40 * 794891 * 2
def baseEnd_794891 : Nat := 181404955970290986225275

theorem tailTrace_794891 : CollatzResearch.WordTrace tailWord_794891 prefixEnd_794891 181404955970290986225275 := by
  unfold tailWord_794891
  simp only [CollatzResearch.WordTrace]
  refine ⟨28992056563253138419776527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19328037708835425613184351 28992056563253138419776527)
  ·
    refine ⟨43488084844879707629664791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28992056563253138419776527 43488084844879707629664791)
    ·
      refine ⟨65232127267319561444497187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43488084844879707629664791 65232127267319561444497187)
      ·
        refine ⟨97848190900979342166745781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65232127267319561444497187 97848190900979342166745781)
        ·
          refine ⟨9173267896966813328132417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97848190900979342166745781 9173267896966813328132417)
          ·
            refine ⟨6879950922725109996099313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9173267896966813328132417 6879950922725109996099313)
            ·
              refine ⟨5159963192043832497074485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6879950922725109996099313 5159963192043832497074485)
              ·
                refine ⟨483746549254109296600733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5159963192043832497074485 483746549254109296600733)
                ·
                  refine ⟨181404955970290986225275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483746549254109296600733 181404955970290986225275)
                  ·
                    rfl

theorem cell21_794891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 5, 3].length) (baseStart_794891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_794891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_794891 prefixEnd_794891 := by exact prefixLift 794891
  have htrace : WordTrace (prefixWord ++ tailWord_794891) baseStart_794891 baseEnd_794891 := by
    simpa [prefixWord, tailWord_794891, baseEnd_794891] using wordTrace_append hprefix tailTrace_794891
  have hstable : (prefixWord ++ tailWord_794891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794891).length < 2 ^ (prefixWord ++ tailWord_794891).sum := by decide
  have hdescent : baseEnd_794891 < baseStart_794891 := by decide
  rcases family_descends (prefixWord ++ tailWord_794891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_794967 : List Nat := [1, 1, 3, 2, 3, 1, 1, 6, 3]
def baseStart_794967 : Nat := 118140960795 + 794967 * 2 ^ 59
def prefixEnd_794967 : Nat := 4983230072969 + 3 ^ 40 * 794967 * 2
def baseEnd_794967 : Nat := 181422300205731742958453

theorem tailTrace_794967 : CollatzResearch.WordTrace tailWord_794967 prefixEnd_794967 181422300205731742958453 := by
  unfold tailWord_794967
  simp only [CollatzResearch.WordTrace]
  refine ⟨28994828510977803399543155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19329885673985202266362103 28994828510977803399543155)
  ·
    refine ⟨43492242766466705099314733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28994828510977803399543155 43492242766466705099314733)
    ·
      refine ⟨16309591037425014412243025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43492242766466705099314733 16309591037425014412243025)
      ·
        refine ⟨12232193278068760809182269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16309591037425014412243025 12232193278068760809182269)
        ·
          refine ⟨4587072479275785303443351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12232193278068760809182269 4587072479275785303443351)
          ·
            refine ⟨6880608718913677955165027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4587072479275785303443351 6880608718913677955165027)
            ·
              refine ⟨10320913078370516932747541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6880608718913677955165027 10320913078370516932747541)
              ·
                refine ⟨483792800548617981222541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10320913078370516932747541 483792800548617981222541)
                ·
                  refine ⟨181422300205731742958453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483792800548617981222541 181422300205731742958453)
                  ·
                    rfl

theorem cell21_794967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 3].length) (baseStart_794967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_794967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_794967 prefixEnd_794967 := by exact prefixLift 794967
  have htrace : WordTrace (prefixWord ++ tailWord_794967) baseStart_794967 baseEnd_794967 := by
    simpa [prefixWord, tailWord_794967, baseEnd_794967] using wordTrace_append hprefix tailTrace_794967
  have hstable : (prefixWord ++ tailWord_794967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_794967).length < 2 ^ (prefixWord ++ tailWord_794967).sum := by decide
  have hdescent : baseEnd_794967 < baseStart_794967 := by decide
  rcases family_descends (prefixWord ++ tailWord_794967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795018 : List Nat := [3, 1, 2, 5, 1, 1, 3, 2, 3]
def baseStart_795018 : Nat := 118140960795 + 795018 * 2 ^ 59
def prefixEnd_795018 : Nat := 4983230072969 + 3 ^ 40 * 795018 * 2
def baseEnd_795018 : Nat := 181433939100566987608349

theorem tailTrace_795018 : CollatzResearch.WordTrace tailWord_795018 prefixEnd_795018 181433939100566987608349 := by
  unfold tailWord_795018
  simp only [CollatzResearch.WordTrace]
  refine ⟨7249172158448259777412427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19331125755862026073099805 7249172158448259777412427)
  ·
    refine ⟨10873758237672389666118641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7249172158448259777412427 10873758237672389666118641)
    ·
      refine ⟨8155318678254292249588981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10873758237672389666118641 8155318678254292249588981)
      ·
        refine ⟨764561126086339898398967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8155318678254292249588981 764561126086339898398967)
        ·
          refine ⟨1146841689129509847598451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764561126086339898398967 1146841689129509847598451)
          ·
            refine ⟨1720262533694264771397677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146841689129509847598451 1720262533694264771397677)
            ·
              refine ⟨645098450135349289274129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1720262533694264771397677 645098450135349289274129)
              ·
                refine ⟨483823837601511966955597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 645098450135349289274129 483823837601511966955597)
                ·
                  refine ⟨181433939100566987608349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483823837601511966955597 181433939100566987608349)
                  ·
                    rfl

theorem cell21_795018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_795018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_795018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_795018 prefixEnd_795018 := by exact prefixLift 795018
  have htrace : WordTrace (prefixWord ++ tailWord_795018) baseStart_795018 baseEnd_795018 := by
    simpa [prefixWord, tailWord_795018, baseEnd_795018] using wordTrace_append hprefix tailTrace_795018
  have hstable : (prefixWord ++ tailWord_795018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795018).length < 2 ^ (prefixWord ++ tailWord_795018).sum := by decide
  have hdescent : baseEnd_795018 < baseStart_795018 := by decide
  rcases family_descends (prefixWord ++ tailWord_795018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795116 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 6]
def baseStart_795116 : Nat := 118140960795 + 795116 * 2 ^ 59
def prefixEnd_795116 : Nat := 4983230072969 + 3 ^ 40 * 795116 * 2
def baseEnd_795116 : Nat := 181456304035740594974815

theorem tailTrace_795116 : CollatzResearch.WordTrace tailWord_795116 prefixEnd_795116 181456304035740594974815 := by
  unfold tailWord_795116
  simp only [CollatzResearch.WordTrace]
  refine ⟨14500131493719000923358601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19333508658292001231144801 14500131493719000923358601)
  ·
    refine ⟨10875098620289250692518951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14500131493719000923358601 10875098620289250692518951)
    ·
      refine ⟨16312647930433876038778427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10875098620289250692518951 16312647930433876038778427)
      ·
        refine ⟨24468971895650814058167641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16312647930433876038778427 24468971895650814058167641)
        ·
          refine ⟨18351728921738110543625731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24468971895650814058167641 18351728921738110543625731)
          ·
            refine ⟨27527593382607165815438597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18351728921738110543625731 27527593382607165815438597)
            ·
              refine ⟨5161423759238843590394737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27527593382607165815438597 5161423759238843590394737)
              ·
                refine ⟨3871067819429132692796053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5161423759238843590394737 3871067819429132692796053)
                ·
                  refine ⟨181456304035740594974815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3871067819429132692796053 181456304035740594974815)
                  ·
                    rfl

theorem cell21_795116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_795116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_795116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_795116 prefixEnd_795116 := by exact prefixLift 795116
  have htrace : WordTrace (prefixWord ++ tailWord_795116) baseStart_795116 baseEnd_795116 := by
    simpa [prefixWord, tailWord_795116, baseEnd_795116] using wordTrace_append hprefix tailTrace_795116
  have hstable : (prefixWord ++ tailWord_795116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795116).length < 2 ^ (prefixWord ++ tailWord_795116).sum := by decide
  have hdescent : baseEnd_795116 < baseStart_795116 := by decide
  rcases family_descends (prefixWord ++ tailWord_795116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795164 : List Nat := [2, 2, 3, 1, 2, 2, 4, 5]
def baseStart_795164 : Nat := 118140960795 + 795164 * 2 ^ 59
def prefixEnd_795164 : Nat := 4983230072969 + 3 ^ 40 * 795164 * 2
def baseEnd_795164 : Nat := 60489086096567726058239

theorem tailTrace_795164 : CollatzResearch.WordTrace tailWord_795164 prefixEnd_795164 60489086096567726058239 := by
  unfold tailWord_795164
  simp only [CollatzResearch.WordTrace]
  refine ⟨14501006845632053022232273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19334675794176070696309697 14501006845632053022232273)
  ·
    refine ⟨10875755134224039766674205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14501006845632053022232273 10875755134224039766674205)
    ·
      refine ⟨4078408175334014912502827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10875755134224039766674205 4078408175334014912502827)
      ·
        refine ⟨6117612263001022368754241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4078408175334014912502827 6117612263001022368754241)
        ·
          refine ⟨4588209197250766776565681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6117612263001022368754241 4588209197250766776565681)
          ·
            refine ⟨3441156897938075082424261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4588209197250766776565681 3441156897938075082424261)
            ·
              refine ⟨645216918363389077954549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3441156897938075082424261 645216918363389077954549)
              ·
                refine ⟨60489086096567726058239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 645216918363389077954549 60489086096567726058239)
                ·
                  rfl

theorem cell21_795164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 5].length) (baseStart_795164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_795164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_795164 prefixEnd_795164 := by exact prefixLift 795164
  have htrace : WordTrace (prefixWord ++ tailWord_795164) baseStart_795164 baseEnd_795164 := by
    simpa [prefixWord, tailWord_795164, baseEnd_795164] using wordTrace_append hprefix tailTrace_795164
  have hstable : (prefixWord ++ tailWord_795164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795164).length < 2 ^ (prefixWord ++ tailWord_795164).sum := by decide
  have hdescent : baseEnd_795164 < baseStart_795164 := by decide
  rcases family_descends (prefixWord ++ tailWord_795164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795192 : List Nat := [2, 1, 2, 1, 4, 1, 1, 3, 6]
def baseStart_795192 : Nat := 118140960795 + 795192 * 2 ^ 59
def prefixEnd_795192 : Nat := 4983230072969 + 3 ^ 40 * 795192 * 2
def baseEnd_795192 : Nat := 181473648271181351707993

theorem tailTrace_795192 : CollatzResearch.WordTrace tailWord_795192 prefixEnd_795192 181473648271181351707993 := by
  unfold tailWord_795192
  simp only [CollatzResearch.WordTrace]
  refine ⟨14501517467581333413241915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19335356623441777884322553 14501517467581333413241915)
  ·
    refine ⟨21752276201372000119862873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14501517467581333413241915 21752276201372000119862873)
    ·
      refine ⟨16314207151029000089897155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21752276201372000119862873 16314207151029000089897155)
      ·
        refine ⟨24471310726543500134845733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16314207151029000089897155 24471310726543500134845733)
        ·
          refine ⟨4588370761226906275283575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24471310726543500134845733 4588370761226906275283575)
          ·
            refine ⟨6882556141840359412925363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4588370761226906275283575 6882556141840359412925363)
            ·
              refine ⟨10323834212760539119388045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6882556141840359412925363 10323834212760539119388045)
              ·
                refine ⟨3871437829785202169770517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10323834212760539119388045 3871437829785202169770517)
                ·
                  refine ⟨181473648271181351707993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3871437829785202169770517 181473648271181351707993)
                  ·
                    rfl

theorem cell21_795192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_795192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_795192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_795192 prefixEnd_795192 := by exact prefixLift 795192
  have htrace : WordTrace (prefixWord ++ tailWord_795192) baseStart_795192 baseEnd_795192 := by
    simpa [prefixWord, tailWord_795192, baseEnd_795192] using wordTrace_append hprefix tailTrace_795192
  have hstable : (prefixWord ++ tailWord_795192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795192).length < 2 ^ (prefixWord ++ tailWord_795192).sum := by decide
  have hdescent : baseEnd_795192 < baseStart_795192 := by decide
  rcases family_descends (prefixWord ++ tailWord_795192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795240 : List Nat := [2, 1, 4, 3, 3, 8]
def baseStart_795240 : Nat := 118140960795 + 795240 * 2 ^ 59
def prefixEnd_795240 : Nat := 4983230072969 + 3 ^ 40 * 795240 * 2
def baseEnd_795240 : Nat := 6721651945375701292885

theorem tailTrace_795240 : CollatzResearch.WordTrace tailWord_795240 prefixEnd_795240 6721651945375701292885 := by
  unfold tailWord_795240
  simp only [CollatzResearch.WordTrace]
  refine ⟨14502392819494385512115587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19336523759325847349487449 14502392819494385512115587)
  ·
    refine ⟨21753589229241578268173381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14502392819494385512115587 21753589229241578268173381)
    ·
      refine ⟨4078797980482795925282509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21753589229241578268173381 4078797980482795925282509)
      ·
        refine ⟨1529549242681048471980941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4078797980482795925282509 1529549242681048471980941)
        ·
          refine ⟨573580966005393176992853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1529549242681048471980941 573580966005393176992853)
          ·
            refine ⟨6721651945375701292885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 573580966005393176992853 6721651945375701292885)
            ·
              rfl

theorem cell21_795240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 8].length) (baseStart_795240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_795240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_795240 prefixEnd_795240 := by exact prefixLift 795240
  have htrace : WordTrace (prefixWord ++ tailWord_795240) baseStart_795240 baseEnd_795240 := by
    simpa [prefixWord, tailWord_795240, baseEnd_795240] using wordTrace_append hprefix tailTrace_795240
  have hstable : (prefixWord ++ tailWord_795240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795240).length < 2 ^ (prefixWord ++ tailWord_795240).sum := by decide
  have hdescent : baseEnd_795240 < baseStart_795240 := by decide
  rcases family_descends (prefixWord ++ tailWord_795240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795364 : List Nat := [2, 3, 1, 1, 1, 5, 3, 2, 3]
def baseStart_795364 : Nat := 118140960795 + 795364 * 2 ^ 59
def prefixEnd_795364 : Nat := 4983230072969 + 3 ^ 40 * 795364 * 2
def baseEnd_795364 : Nat := 181512901014547274840975

theorem tailTrace_795364 : CollatzResearch.WordTrace tailWord_795364 prefixEnd_795364 181512901014547274840975 := by
  unfold tailWord_795364
  simp only [CollatzResearch.WordTrace]
  refine ⟨14504654145269770100872573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19339538860359693467830097 14504654145269770100872573)
  ·
    refine ⟨5439245304476163787827215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14504654145269770100872573 5439245304476163787827215)
    ·
      refine ⟨8158867956714245681740823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5439245304476163787827215 8158867956714245681740823)
      ·
        refine ⟨12238301935071368522611235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8158867956714245681740823 12238301935071368522611235)
        ·
          refine ⟨18357452902607052783916853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12238301935071368522611235 18357452902607052783916853)
          ·
            refine ⟨1721011209619411198492205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18357452902607052783916853 1721011209619411198492205)
            ·
              refine ⟨645379203607279199434577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1721011209619411198492205 645379203607279199434577)
              ·
                refine ⟨484034402705459399575933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 645379203607279199434577 484034402705459399575933)
                ·
                  refine ⟨181512901014547274840975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 484034402705459399575933 181512901014547274840975)
                  ·
                    rfl

theorem cell21_795364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_795364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_795364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_795364 prefixEnd_795364 := by exact prefixLift 795364
  have htrace : WordTrace (prefixWord ++ tailWord_795364) baseStart_795364 baseEnd_795364 := by
    simpa [prefixWord, tailWord_795364, baseEnd_795364] using wordTrace_append hprefix tailTrace_795364
  have hstable : (prefixWord ++ tailWord_795364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795364).length < 2 ^ (prefixWord ++ tailWord_795364).sum := by decide
  have hdescent : baseEnd_795364 < baseStart_795364 := by decide
  rcases family_descends (prefixWord ++ tailWord_795364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795375 : List Nat := [1, 1, 2, 1, 5, 3, 2, 6]
def baseStart_795375 : Nat := 118140960795 + 795375 * 2 ^ 59
def prefixEnd_795375 : Nat := 4983230072969 + 3 ^ 40 * 795375 * 2
def baseEnd_795375 : Nat := 60505137121471233385873

theorem tailTrace_795375 : CollatzResearch.WordTrace tailWord_795375 prefixEnd_795375 60505137121471233385873 := by
  unfold tailWord_795375
  simp only [CollatzResearch.WordTrace]
  refine ⟨29009709493499689080395579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19339806328999792720263719 29009709493499689080395579)
  ·
    refine ⟨43514564240249533620593369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29009709493499689080395579 43514564240249533620593369)
    ·
      refine ⟨32635923180187150215445027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43514564240249533620593369 32635923180187150215445027)
      ·
        refine ⟨48953884770280725323167541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32635923180187150215445027 48953884770280725323167541)
        ·
          refine ⟨4589426697213817999046957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48953884770280725323167541 4589426697213817999046957)
          ·
            refine ⟨1721035011455181749642609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4589426697213817999046957 1721035011455181749642609)
            ·
              refine ⟨1290776258591386312231957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1721035011455181749642609 1290776258591386312231957)
              ·
                refine ⟨60505137121471233385873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1290776258591386312231957 60505137121471233385873)
                ·
                  rfl

theorem cell21_795375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 6].length) (baseStart_795375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_795375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_795375 prefixEnd_795375 := by exact prefixLift 795375
  have htrace : WordTrace (prefixWord ++ tailWord_795375) baseStart_795375 baseEnd_795375 := by
    simpa [prefixWord, tailWord_795375, baseEnd_795375] using wordTrace_append hprefix tailTrace_795375
  have hstable : (prefixWord ++ tailWord_795375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795375).length < 2 ^ (prefixWord ++ tailWord_795375).sum := by decide
  have hdescent : baseEnd_795375 < baseStart_795375 := by decide
  rcases family_descends (prefixWord ++ tailWord_795375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795378 : List Nat := [3, 2, 1, 3, 1, 2, 4, 1, 4]
def baseStart_795378 : Nat := 118140960795 + 795378 * 2 ^ 59
def prefixEnd_795378 : Nat := 4983230072969 + 3 ^ 40 * 795378 * 2
def baseEnd_795378 : Nat := 181516096005286361607613

theorem tailTrace_795378 : CollatzResearch.WordTrace tailWord_795378 prefixEnd_795378 181516096005286361607613 := by
  unfold tailWord_795378
  simp only [CollatzResearch.WordTrace]
  refine ⟨7252454728122205148188697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19339879274992547061836525 7252454728122205148188697)
  ·
    refine ⟨5439341046091653861141523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7252454728122205148188697 5439341046091653861141523)
    ·
      refine ⟨8159011569137480791712285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5439341046091653861141523 8159011569137480791712285)
      ·
        refine ⟨3059629338426555296892107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8159011569137480791712285 3059629338426555296892107)
        ·
          refine ⟨4589444007639832945338161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3059629338426555296892107 4589444007639832945338161)
          ·
            refine ⟨3442083005729874709003621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4589444007639832945338161 3442083005729874709003621)
            ·
              refine ⟨645390563574351507938179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3442083005729874709003621 645390563574351507938179)
              ·
                refine ⟨968085845361527261907269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645390563574351507938179 968085845361527261907269)
                ·
                  refine ⟨181516096005286361607613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 968085845361527261907269 181516096005286361607613)
                  ·
                    rfl

theorem cell21_795378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_795378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_795378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_795378 prefixEnd_795378 := by exact prefixLift 795378
  have htrace : WordTrace (prefixWord ++ tailWord_795378) baseStart_795378 baseEnd_795378 := by
    simpa [prefixWord, tailWord_795378, baseEnd_795378] using wordTrace_append hprefix tailTrace_795378
  have hstable : (prefixWord ++ tailWord_795378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795378).length < 2 ^ (prefixWord ++ tailWord_795378).sum := by decide
  have hdescent : baseEnd_795378 < baseStart_795378 := by decide
  rcases family_descends (prefixWord ++ tailWord_795378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795389 : List Nat := [1, 4, 1, 1, 1, 1, 4, 1, 7]
def baseStart_795389 : Nat := 118140960795 + 795389 * 2 ^ 59
def prefixEnd_795389 : Nat := 4983230072969 + 3 ^ 40 * 795389 * 2
def baseEnd_795389 : Nat := 181518606355152786924257

theorem tailTrace_795389 : CollatzResearch.WordTrace tailWord_795389 prefixEnd_795389 181518606355152786924257 := by
  unfold tailWord_795389
  simp only [CollatzResearch.WordTrace]
  refine ⟨29010220115448969471405221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19340146743632646314270147 29010220115448969471405221)
  ·
    refine ⟨5439416271646681775888479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29010220115448969471405221 5439416271646681775888479)
    ·
      refine ⟨8159124407470022663832719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5439416271646681775888479 8159124407470022663832719)
      ·
        refine ⟨12238686611205033995749079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8159124407470022663832719 12238686611205033995749079)
        ·
          refine ⟨18358029916807550993623619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12238686611205033995749079 18358029916807550993623619)
          ·
            refine ⟨27537044875211326490435429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18358029916807550993623619 27537044875211326490435429)
            ·
              refine ⟨5163195914102123716956643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27537044875211326490435429 5163195914102123716956643)
              ·
                refine ⟨7744793871153185575434965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5163195914102123716956643 7744793871153185575434965)
                ·
                  refine ⟨181518606355152786924257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7744793871153185575434965 181518606355152786924257)
                  ·
                    rfl

theorem cell21_795389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_795389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_795389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_795389 prefixEnd_795389 := by exact prefixLift 795389
  have htrace : WordTrace (prefixWord ++ tailWord_795389) baseStart_795389 baseEnd_795389 := by
    simpa [prefixWord, tailWord_795389, baseEnd_795389] using wordTrace_append hprefix tailTrace_795389
  have hstable : (prefixWord ++ tailWord_795389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795389).length < 2 ^ (prefixWord ++ tailWord_795389).sum := by decide
  have hdescent : baseEnd_795389 < baseStart_795389 := by decide
  rcases family_descends (prefixWord ++ tailWord_795389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795423 : List Nat := [1, 1, 2, 4, 2, 3, 1, 4, 3]
def baseStart_795423 : Nat := 118140960795 + 795423 * 2 ^ 59
def prefixEnd_795423 : Nat := 4983230072969 + 3 ^ 40 * 795423 * 2
def baseEnd_795423 : Nat := 181526365618376283357521

theorem tailTrace_795423 : CollatzResearch.WordTrace tailWord_795423 prefixEnd_795423 181526365618376283357521 := by
  unfold tailWord_795423
  simp only [CollatzResearch.WordTrace]
  refine ⟨29011460197325793278142923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19340973464883862185428615 29011460197325793278142923)
  ·
    refine ⟨43517190295988689917214385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29011460197325793278142923 43517190295988689917214385)
    ·
      refine ⟨32637892721991517437910789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43517190295988689917214385 32637892721991517437910789)
      ·
        refine ⟨6119604885373409519608273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32637892721991517437910789 6119604885373409519608273)
        ·
          refine ⟨4589703664030057139706205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6119604885373409519608273 4589703664030057139706205)
          ·
            refine ⟨1721138874011271427389827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4589703664030057139706205 1721138874011271427389827)
            ·
              refine ⟨2581708311016907141084741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1721138874011271427389827 2581708311016907141084741)
              ·
                refine ⟨484070308315670088953389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2581708311016907141084741 484070308315670088953389)
                ·
                  refine ⟨181526365618376283357521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 484070308315670088953389 181526365618376283357521)
                  ·
                    rfl

theorem cell21_795423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 4, 3].length) (baseStart_795423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_795423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_795423 prefixEnd_795423 := by exact prefixLift 795423
  have htrace : WordTrace (prefixWord ++ tailWord_795423) baseStart_795423 baseEnd_795423 := by
    simpa [prefixWord, tailWord_795423, baseEnd_795423] using wordTrace_append hprefix tailTrace_795423
  have hstable : (prefixWord ++ tailWord_795423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795423).length < 2 ^ (prefixWord ++ tailWord_795423).sum := by decide
  have hdescent : baseEnd_795423 < baseStart_795423 := by decide
  rcases family_descends (prefixWord ++ tailWord_795423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795457 : List Nat := [1, 2, 5, 3, 1, 1, 2, 3, 3]
def baseStart_795457 : Nat := 118140960795 + 795457 * 2 ^ 59
def prefixEnd_795457 : Nat := 4983230072969 + 3 ^ 40 * 795457 * 2
def baseEnd_795457 : Nat := 181534124881599779790785

theorem tailTrace_795457 : CollatzResearch.WordTrace tailWord_795457 prefixEnd_795457 181534124881599779790785 := by
  unfold tailWord_795457
  simp only [CollatzResearch.WordTrace]
  refine ⟨29012700279202617084880625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19341800186135078056587083 29012700279202617084880625)
  ·
    refine ⟨21759525209401962813660469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29012700279202617084880625 21759525209401962813660469)
    ·
      refine ⟨2039955488381434013780669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21759525209401962813660469 2039955488381434013780669)
      ·
        refine ⟨764983308143037755167751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2039955488381434013780669 764983308143037755167751)
        ·
          refine ⟨1147474962214556632751627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764983308143037755167751 1147474962214556632751627)
          ·
            refine ⟨1721212443321834949127441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1147474962214556632751627 1721212443321834949127441)
            ·
              refine ⟨1290909332491376211845581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1721212443321834949127441 1290909332491376211845581)
              ·
                refine ⟨484090999684266079442093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1290909332491376211845581 484090999684266079442093)
                ·
                  refine ⟨181534124881599779790785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 484090999684266079442093 181534124881599779790785)
                  ·
                    rfl

theorem cell21_795457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 3].length) (baseStart_795457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_795457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_795457 prefixEnd_795457 := by exact prefixLift 795457
  have htrace : WordTrace (prefixWord ++ tailWord_795457) baseStart_795457 baseEnd_795457 := by
    simpa [prefixWord, tailWord_795457, baseEnd_795457] using wordTrace_append hprefix tailTrace_795457
  have hstable : (prefixWord ++ tailWord_795457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795457).length < 2 ^ (prefixWord ++ tailWord_795457).sum := by decide
  have hdescent : baseEnd_795457 < baseStart_795457 := by decide
  rcases family_descends (prefixWord ++ tailWord_795457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795482 : List Nat := [3, 1, 1, 2, 1, 5, 2, 1, 5]
def baseStart_795482 : Nat := 118140960795 + 795482 * 2 ^ 59
def prefixEnd_795482 : Nat := 4983230072969 + 3 ^ 40 * 795482 * 2
def baseEnd_795482 : Nat := 181539830222205291874067

theorem tailTrace_795482 : CollatzResearch.WordTrace tailWord_795482 prefixEnd_795482 181539830222205291874067 := by
  unfold tailWord_795482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7253403026028011588635175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19342408069408030903027133 7253403026028011588635175)
  ·
    refine ⟨10880104539042017382952763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7253403026028011588635175 10880104539042017382952763)
    ·
      refine ⟨16320156808563026074429145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10880104539042017382952763 16320156808563026074429145)
      ·
        refine ⟨12240117606422269555821859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16320156808563026074429145 12240117606422269555821859)
        ·
          refine ⟨18360176409633404333732789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12240117606422269555821859 18360176409633404333732789)
          ·
            refine ⟨1721266538403131656287449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18360176409633404333732789 1721266538403131656287449)
            ·
              refine ⟨1290949903802348742215587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1721266538403131656287449 1290949903802348742215587)
              ·
                refine ⟨1936424855703523113323381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1290949903802348742215587 1936424855703523113323381)
                ·
                  refine ⟨181539830222205291874067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1936424855703523113323381 181539830222205291874067)
                  ·
                    rfl

theorem cell21_795482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_795482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_795482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_795482 prefixEnd_795482 := by exact prefixLift 795482
  have htrace : WordTrace (prefixWord ++ tailWord_795482) baseStart_795482 baseEnd_795482 := by
    simpa [prefixWord, tailWord_795482, baseEnd_795482] using wordTrace_append hprefix tailTrace_795482
  have hstable : (prefixWord ++ tailWord_795482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795482).length < 2 ^ (prefixWord ++ tailWord_795482).sum := by decide
  have hdescent : baseEnd_795482 < baseStart_795482 := by decide
  rcases family_descends (prefixWord ++ tailWord_795482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795502 : List Nat := [4, 1, 2, 3, 3, 1, 2, 5]
def baseStart_795502 : Nat := 118140960795 + 795502 * 2 ^ 59
def prefixEnd_795502 : Nat := 4983230072969 + 3 ^ 40 * 795502 * 2
def baseEnd_795502 : Nat := 60514798164896567180231

theorem tailTrace_795502 : CollatzResearch.WordTrace tailWord_795502 prefixEnd_795502 60514798164896567180231 := by
  unfold tailWord_795502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3626792695504948721283595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19342894376026393180179173 3626792695504948721283595)
  ·
    refine ⟨5440189043257423081925393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3626792695504948721283595 5440189043257423081925393)
    ·
      refine ⟨4080141782443067311444045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5440189043257423081925393 4080141782443067311444045)
      ·
        refine ⟨1530053168416150241791517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4080141782443067311444045 1530053168416150241791517)
        ·
          refine ⟨573769938156056340671819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1530053168416150241791517 573769938156056340671819)
          ·
            refine ⟨860654907234084511007729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573769938156056340671819 860654907234084511007729)
            ·
              refine ⟨645491180425563383255797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 860654907234084511007729 645491180425563383255797)
              ·
                refine ⟨60514798164896567180231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 645491180425563383255797 60514798164896567180231)
                ·
                  rfl

theorem cell21_795502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_795502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_795502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_795502 prefixEnd_795502 := by exact prefixLift 795502
  have htrace : WordTrace (prefixWord ++ tailWord_795502) baseStart_795502 baseEnd_795502 := by
    simpa [prefixWord, tailWord_795502, baseEnd_795502] using wordTrace_append hprefix tailTrace_795502
  have hstable : (prefixWord ++ tailWord_795502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795502).length < 2 ^ (prefixWord ++ tailWord_795502).sum := by decide
  have hdescent : baseEnd_795502 < baseStart_795502 := by decide
  rcases family_descends (prefixWord ++ tailWord_795502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795527 : List Nat := [1, 1, 4, 2, 3, 3, 7]
def baseStart_795527 : Nat := 118140960795 + 795527 * 2 ^ 59
def prefixEnd_795527 : Nat := 4983230072969 + 3 ^ 40 * 795527 * 2
def baseEnd_795527 : Nat := 20172233315032801513775

theorem tailTrace_795527 : CollatzResearch.WordTrace tailWord_795527 prefixEnd_795527 20172233315032801513775 := by
  unfold tailWord_795527
  simp only [CollatzResearch.WordTrace]
  refine ⟨29015253388949019039928835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19343502259299346026619223 29015253388949019039928835)
  ·
    refine ⟨43522880083423528559893253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29015253388949019039928835 43522880083423528559893253)
    ·
      refine ⟨8160540015641911604979985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43522880083423528559893253 8160540015641911604979985)
      ·
        refine ⟨6120405011731433703734989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8160540015641911604979985 6120405011731433703734989)
        ·
          refine ⟨2295151879399287638900621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6120405011731433703734989 2295151879399287638900621)
          ·
            refine ⟨860681954774732864587733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2295151879399287638900621 860681954774732864587733)
            ·
              refine ⟨20172233315032801513775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 860681954774732864587733 20172233315032801513775)
              ·
                rfl

theorem cell21_795527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 7].length) (baseStart_795527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_795527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_795527 prefixEnd_795527 := by exact prefixLift 795527
  have htrace : WordTrace (prefixWord ++ tailWord_795527) baseStart_795527 baseEnd_795527 := by
    simpa [prefixWord, tailWord_795527, baseEnd_795527] using wordTrace_append hprefix tailTrace_795527
  have hstable : (prefixWord ++ tailWord_795527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795527).length < 2 ^ (prefixWord ++ tailWord_795527).sum := by decide
  have hdescent : baseEnd_795527 < baseStart_795527 := by decide
  rcases family_descends (prefixWord ++ tailWord_795527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795606 : List Nat := [5, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_795606 : Nat := 118140960795 + 795606 * 2 ^ 59
def prefixEnd_795606 : Nat := 4983230072969 + 3 ^ 40 * 795606 * 2
def baseEnd_795606 : Nat := 181568128711608631807147

theorem tailTrace_795606 : CollatzResearch.WordTrace tailWord_795606 prefixEnd_795606 181568128711608631807147 := by
  unfold tailWord_795606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1813633422228925970753417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19345423170441877021369781 1813633422228925970753417)
  ·
    refine ⟨1360225066671694478065063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1813633422228925970753417 1360225066671694478065063)
    ·
      refine ⟨2040337600007541717097595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1360225066671694478065063 2040337600007541717097595)
      ·
        refine ⟨3060506400011312575646393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2040337600007541717097595 3060506400011312575646393)
        ·
          refine ⟨2295379800008484431734795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3060506400011312575646393 2295379800008484431734795)
          ·
            refine ⟨3443069700012726647602193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295379800008484431734795 3443069700012726647602193)
            ·
              refine ⟨2582302275009544985701645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3443069700012726647602193 2582302275009544985701645)
              ·
                refine ⟨968363353128579369638117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2582302275009544985701645 968363353128579369638117)
                ·
                  refine ⟨181568128711608631807147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 968363353128579369638117 181568128711608631807147)
                  ·
                    rfl

theorem cell21_795606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_795606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_795606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_795606 prefixEnd_795606 := by exact prefixLift 795606
  have htrace : WordTrace (prefixWord ++ tailWord_795606) baseStart_795606 baseEnd_795606 := by
    simpa [prefixWord, tailWord_795606, baseEnd_795606] using wordTrace_append hprefix tailTrace_795606
  have hstable : (prefixWord ++ tailWord_795606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795606).length < 2 ^ (prefixWord ++ tailWord_795606).sum := by decide
  have hdescent : baseEnd_795606 < baseStart_795606 := by decide
  rcases family_descends (prefixWord ++ tailWord_795606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795679 : List Nat := [1, 1, 2, 4, 1, 3, 4, 5]
def baseStart_795679 : Nat := 118140960795 + 795679 * 2 ^ 59
def prefixEnd_795679 : Nat := 4983230072969 + 3 ^ 40 * 795679 * 2
def baseEnd_795679 : Nat := 60528262768725575696777

theorem tailTrace_795679 : CollatzResearch.WordTrace tailWord_795679 prefixEnd_795679 60528262768725575696777 := by
  unfold tailWord_795679
  simp only [CollatzResearch.WordTrace]
  refine ⟨29020797284398348999462091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19347198189598899332974727 29020797284398348999462091)
  ·
    refine ⟨43531195926597523499193137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29020797284398348999462091 43531195926597523499193137)
    ·
      refine ⟨32648396944948142624394853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43531195926597523499193137 32648396944948142624394853)
      ·
        refine ⟨6121574427177776742074035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32648396944948142624394853 6121574427177776742074035)
        ·
          refine ⟨9182361640766665113111053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6121574427177776742074035 9182361640766665113111053)
          ·
            refine ⟨3443385615287499417416645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9182361640766665113111053 3443385615287499417416645)
            ·
              refine ⟨645634802866406140765621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3443385615287499417416645 645634802866406140765621)
              ·
                refine ⟨60528262768725575696777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 645634802866406140765621 60528262768725575696777)
                ·
                  rfl

theorem cell21_795679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 5].length) (baseStart_795679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_795679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_795679 prefixEnd_795679 := by exact prefixLift 795679
  have htrace : WordTrace (prefixWord ++ tailWord_795679) baseStart_795679 baseEnd_795679 := by
    simpa [prefixWord, tailWord_795679, baseEnd_795679] using wordTrace_append hprefix tailTrace_795679
  have hstable : (prefixWord ++ tailWord_795679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795679).length < 2 ^ (prefixWord ++ tailWord_795679).sum := by decide
  have hdescent : baseEnd_795679 < baseStart_795679 := by decide
  rcases family_descends (prefixWord ++ tailWord_795679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795783 : List Nat := [1, 1, 4, 2, 1, 1, 1, 2, 8]
def baseStart_795783 : Nat := 118140960795 + 795783 * 2 ^ 59
def prefixEnd_795783 : Nat := 4983230072969 + 3 ^ 40 * 795783 * 2
def baseEnd_795783 : Nat := 181608522523095657356785

theorem tailTrace_795783 : CollatzResearch.WordTrace tailWord_795783 prefixEnd_795783 181608522523095657356785 := by
  unfold tailWord_795783
  simp only [CollatzResearch.WordTrace]
  refine ⟨29024590476021574761248003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19349726984014383174165335 29024590476021574761248003)
  ·
    refine ⟨43536885714032362141872005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29024590476021574761248003 43536885714032362141872005)
    ·
      refine ⟨8163166071381067901601001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43536885714032362141872005 8163166071381067901601001)
      ·
        refine ⟨6122374553535800926200751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8163166071381067901601001 6122374553535800926200751)
        ·
          refine ⟨9183561830303701389301127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6122374553535800926200751 9183561830303701389301127)
          ·
            refine ⟨13775342745455552083951691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9183561830303701389301127 13775342745455552083951691)
            ·
              refine ⟨20663014118183328125927537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13775342745455552083951691 20663014118183328125927537)
              ·
                refine ⟨15497260588637496094445653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20663014118183328125927537 15497260588637496094445653)
                ·
                  refine ⟨181608522523095657356785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15497260588637496094445653 181608522523095657356785)
                  ·
                    rfl

theorem cell21_795783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 2, 8].length) (baseStart_795783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_795783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_795783 prefixEnd_795783 := by exact prefixLift 795783
  have htrace : WordTrace (prefixWord ++ tailWord_795783) baseStart_795783 baseEnd_795783 := by
    simpa [prefixWord, tailWord_795783, baseEnd_795783] using wordTrace_append hprefix tailTrace_795783
  have hstable : (prefixWord ++ tailWord_795783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795783).length < 2 ^ (prefixWord ++ tailWord_795783).sum := by decide
  have hdescent : baseEnd_795783 < baseStart_795783 := by decide
  rcases family_descends (prefixWord ++ tailWord_795783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795879 : List Nat := [1, 1, 5, 3, 2, 2, 1, 1, 5]
def baseStart_795879 : Nat := 118140960795 + 795879 * 2 ^ 59
def prefixEnd_795879 : Nat := 4983230072969 + 3 ^ 40 * 795879 * 2
def baseEnd_795879 : Nat := 181630431031020823756589

theorem tailTrace_795879 : CollatzResearch.WordTrace tailWord_795879 prefixEnd_795879 181630431031020823756589 := by
  unfold tailWord_795879
  simp only [CollatzResearch.WordTrace]
  refine ⟨29028091883673783156742691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19352061255782522104495127 29028091883673783156742691)
  ·
    refine ⟨43542137825510674735114037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29028091883673783156742691 43542137825510674735114037)
    ·
      refine ⟨4082075421141625756416941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43542137825510674735114037 4082075421141625756416941)
      ·
        refine ⟨1530778282928109658656353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4082075421141625756416941 1530778282928109658656353)
        ·
          refine ⟨1148083712196082243992265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1530778282928109658656353 1148083712196082243992265)
          ·
            refine ⟨861062784147061682994199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1148083712196082243992265 861062784147061682994199)
            ·
              refine ⟨1291594176220592524491299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861062784147061682994199 1291594176220592524491299)
              ·
                refine ⟨1937391264330888786736949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1291594176220592524491299 1937391264330888786736949)
                ·
                  refine ⟨181630431031020823756589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1937391264330888786736949 181630431031020823756589)
                  ·
                    rfl

theorem cell21_795879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 5].length) (baseStart_795879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_795879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_795879 prefixEnd_795879 := by exact prefixLift 795879
  have htrace : WordTrace (prefixWord ++ tailWord_795879) baseStart_795879 baseEnd_795879 := by
    simpa [prefixWord, tailWord_795879, baseEnd_795879] using wordTrace_append hprefix tailTrace_795879
  have hstable : (prefixWord ++ tailWord_795879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795879).length < 2 ^ (prefixWord ++ tailWord_795879).sum := by decide
  have hdescent : baseEnd_795879 < baseStart_795879 := by decide
  rcases family_descends (prefixWord ++ tailWord_795879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795904 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 7]
def baseStart_795904 : Nat := 118140960795 + 795904 * 2 ^ 59
def prefixEnd_795904 : Nat := 4983230072969 + 3 ^ 40 * 795904 * 2
def baseEnd_795904 : Nat := 181636136371626335839871

theorem tailTrace_795904 : CollatzResearch.WordTrace tailWord_795904 prefixEnd_795904 181636136371626335839871 := by
  unfold tailWord_795904
  simp only [CollatzResearch.WordTrace]
  refine ⟨14514501854291606213201383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19352669139055474950935177 14514501854291606213201383)
  ·
    refine ⟨21771752781437409319802075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14514501854291606213201383 21771752781437409319802075)
    ·
      refine ⟨32657629172156113979703113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21771752781437409319802075 32657629172156113979703113)
      ·
        refine ⟨24493221879117085484777335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32657629172156113979703113 24493221879117085484777335)
        ·
          refine ⟨36739832818675628227166003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24493221879117085484777335 36739832818675628227166003)
          ·
            refine ⟨55109749228013442340749005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36739832818675628227166003 55109749228013442340749005)
            ·
              refine ⟨20666155960505040877780877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55109749228013442340749005 20666155960505040877780877)
              ·
                refine ⟨7749808485189390329167829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20666155960505040877780877 7749808485189390329167829)
                ·
                  refine ⟨181636136371626335839871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7749808485189390329167829 181636136371626335839871)
                  ·
                    rfl

theorem cell21_795904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_795904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_795904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_795904 prefixEnd_795904 := by exact prefixLift 795904
  have htrace : WordTrace (prefixWord ++ tailWord_795904) baseStart_795904 baseEnd_795904 := by
    simpa [prefixWord, tailWord_795904, baseEnd_795904] using wordTrace_append hprefix tailTrace_795904
  have hstable : (prefixWord ++ tailWord_795904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795904).length < 2 ^ (prefixWord ++ tailWord_795904).sum := by decide
  have hdescent : baseEnd_795904 < baseStart_795904 := by decide
  rcases family_descends (prefixWord ++ tailWord_795904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_795972 : List Nat := [2, 3, 4, 1, 1, 2, 2, 3, 3]
def baseStart_795972 : Nat := 118140960795 + 795972 * 2 ^ 59
def prefixEnd_795972 : Nat := 4983230072969 + 3 ^ 40 * 795972 * 2
def baseEnd_795972 : Nat := 181651654898073328706399

theorem tailTrace_795972 : CollatzResearch.WordTrace tailWord_795972 prefixEnd_795972 181651654898073328706399 := by
  unfold tailWord_795972
  simp only [CollatzResearch.WordTrace]
  refine ⟨14515741936168430019939085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19354322581557906693252113 14515741936168430019939085)
  ·
    refine ⟨5443403226063161257477157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14515741936168430019939085 5443403226063161257477157)
    ·
      refine ⟨1020638104886842735776967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5443403226063161257477157 1020638104886842735776967)
      ·
        refine ⟨1530957157330264103665451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1020638104886842735776967 1530957157330264103665451)
        ·
          refine ⟨2296435735995396155498177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1530957157330264103665451 2296435735995396155498177)
          ·
            refine ⟨1722326801996547116623633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2296435735995396155498177 1722326801996547116623633)
            ·
              refine ⟨1291745101497410337467725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1722326801996547116623633 1291745101497410337467725)
              ·
                refine ⟨484404413061528876550397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1291745101497410337467725 484404413061528876550397)
                ·
                  refine ⟨181651654898073328706399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 484404413061528876550397 181651654898073328706399)
                  ·
                    rfl

theorem cell21_795972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_795972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_795972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_795972 prefixEnd_795972 := by exact prefixLift 795972
  have htrace : WordTrace (prefixWord ++ tailWord_795972) baseStart_795972 baseEnd_795972 := by
    simpa [prefixWord, tailWord_795972, baseEnd_795972] using wordTrace_append hprefix tailTrace_795972
  have hstable : (prefixWord ++ tailWord_795972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_795972).length < 2 ^ (prefixWord ++ tailWord_795972).sum := by decide
  have hdescent : baseEnd_795972 < baseStart_795972 := by decide
  rcases family_descends (prefixWord ++ tailWord_795972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796062 : List Nat := [4, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_796062 : Nat := 118140960795 + 796062 * 2 ^ 59
def prefixEnd_796062 : Nat := 4983230072969 + 3 ^ 40 * 796062 * 2
def baseEnd_796062 : Nat := 181672194124253172206215

theorem tailTrace_796062 : CollatzResearch.WordTrace tailWord_796062 prefixEnd_796062 181672194124253172206215 := by
  unfold tailWord_796062
  simp only [CollatzResearch.WordTrace]
  refine ⟨3629345805251350676331805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19356510961340536940436293 3629345805251350676331805)
  ·
    refine ⟨1361004676969256503624427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3629345805251350676331805 1361004676969256503624427)
    ·
      refine ⟨2041507015453884755436641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1361004676969256503624427 2041507015453884755436641)
      ·
        refine ⟨1531130261590413566577481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2041507015453884755436641 1531130261590413566577481)
        ·
          refine ⟨1148347696192810174933111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1531130261590413566577481 1148347696192810174933111)
          ·
            refine ⟨1722521544289215262399667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148347696192810174933111 1722521544289215262399667)
            ·
              refine ⟨2583782316433822893599501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1722521544289215262399667 2583782316433822893599501)
              ·
                refine ⟨968918368662683585099813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2583782316433822893599501 968918368662683585099813)
                ·
                  refine ⟨181672194124253172206215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 968918368662683585099813 181672194124253172206215)
                  ·
                    rfl

theorem cell21_796062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_796062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796062 prefixEnd_796062 := by exact prefixLift 796062
  have htrace : WordTrace (prefixWord ++ tailWord_796062) baseStart_796062 baseEnd_796062 := by
    simpa [prefixWord, tailWord_796062, baseEnd_796062] using wordTrace_append hprefix tailTrace_796062
  have hstable : (prefixWord ++ tailWord_796062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796062).length < 2 ^ (prefixWord ++ tailWord_796062).sum := by decide
  have hdescent : baseEnd_796062 < baseStart_796062 := by decide
  rcases family_descends (prefixWord ++ tailWord_796062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796104 : List Nat := [2, 1, 3, 1, 3, 1, 4, 2, 4]
def baseStart_796104 : Nat := 118140960795 + 796104 * 2 ^ 59
def prefixEnd_796104 : Nat := 4983230072969 + 3 ^ 40 * 796104 * 2
def baseEnd_796104 : Nat := 181681779096470432506129

theorem tailTrace_796104 : CollatzResearch.WordTrace tailWord_796104 prefixEnd_796104 181681779096470432506129 := by
  unfold tailWord_796104
  simp only [CollatzResearch.WordTrace]
  refine ⟨14518149153929323291841683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19357532205239097722455577 14518149153929323291841683)
  ·
    refine ⟨21777223730893984937762525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14518149153929323291841683 21777223730893984937762525)
    ·
      refine ⟨8166458899085244351660947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21777223730893984937762525 8166458899085244351660947)
      ·
        refine ⟨12249688348627866527491421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8166458899085244351660947 12249688348627866527491421)
        ·
          refine ⟨4593633130735449947809283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12249688348627866527491421 4593633130735449947809283)
          ·
            refine ⟨6890449696103174921713925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4593633130735449947809283 6890449696103174921713925)
            ·
              refine ⟨1291959318019345297821361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6890449696103174921713925 1291959318019345297821361)
              ·
                refine ⟨968969488514508973366021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1291959318019345297821361 968969488514508973366021)
                ·
                  refine ⟨181681779096470432506129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 968969488514508973366021 181681779096470432506129)
                  ·
                    rfl

theorem cell21_796104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 2, 4].length) (baseStart_796104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796104 prefixEnd_796104 := by exact prefixLift 796104
  have htrace : WordTrace (prefixWord ++ tailWord_796104) baseStart_796104 baseEnd_796104 := by
    simpa [prefixWord, tailWord_796104, baseEnd_796104] using wordTrace_append hprefix tailTrace_796104
  have hstable : (prefixWord ++ tailWord_796104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796104).length < 2 ^ (prefixWord ++ tailWord_796104).sum := by decide
  have hdescent : baseEnd_796104 < baseStart_796104 := by decide
  rcases family_descends (prefixWord ++ tailWord_796104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796135 : List Nat := [1, 1, 5, 2, 1, 3, 3, 5]
def baseStart_796135 : Nat := 118140960795 + 796135 * 2 ^ 59
def prefixEnd_796135 : Nat := 4983230072969 + 3 ^ 40 * 796135 * 2
def baseEnd_796135 : Nat := 60562951239607089163133

theorem tailTrace_796135 : CollatzResearch.WordTrace tailWord_796135 prefixEnd_796135 60562951239607089163133 := by
  unfold tailWord_796135
  simp only [CollatzResearch.WordTrace]
  refine ⟨29037428970746338878061859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19358285980497559252041239 29037428970746338878061859)
  ·
    refine ⟨43556143456119508317092789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29037428970746338878061859 43556143456119508317092789)
    ·
      refine ⟨4083388449011203904727449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43556143456119508317092789 4083388449011203904727449)
      ·
        refine ⟨3062541336758402928545587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4083388449011203904727449 3062541336758402928545587)
        ·
          refine ⟨4593812005137604392818381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3062541336758402928545587 4593812005137604392818381)
          ·
            refine ⟨1722679501926601647306893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4593812005137604392818381 1722679501926601647306893)
            ·
              refine ⟨646004813222475617740085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1722679501926601647306893 646004813222475617740085)
              ·
                refine ⟨60562951239607089163133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 646004813222475617740085 60562951239607089163133)
                ·
                  rfl

theorem cell21_796135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 5].length) (baseStart_796135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796135 prefixEnd_796135 := by exact prefixLift 796135
  have htrace : WordTrace (prefixWord ++ tailWord_796135) baseStart_796135 baseEnd_796135 := by
    simpa [prefixWord, tailWord_796135, baseEnd_796135] using wordTrace_append hprefix tailTrace_796135
  have hstable : (prefixWord ++ tailWord_796135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796135).length < 2 ^ (prefixWord ++ tailWord_796135).sum := by decide
  have hdescent : baseEnd_796135 < baseStart_796135 := by decide
  rcases family_descends (prefixWord ++ tailWord_796135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796163 : List Nat := [1, 1, 1, 3, 2, 1, 2, 6, 4]
def baseStart_796163 : Nat := 118140960795 + 796163 * 2 ^ 59
def prefixEnd_796163 : Nat := 4983230072969 + 3 ^ 40 * 796163 * 2
def baseEnd_796163 : Nat := 181695243700299441022675

theorem tailTrace_796163 : CollatzResearch.WordTrace tailWord_796163 prefixEnd_796163 181695243700299441022675 := by
  unfold tailWord_796163
  simp only [CollatzResearch.WordTrace]
  refine ⟨29038450214644899660081143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19358966809763266440054095 29038450214644899660081143)
  ·
    refine ⟨43557675321967349490121715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29038450214644899660081143 43557675321967349490121715)
    ·
      refine ⟨65336512982951024235182573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43557675321967349490121715 65336512982951024235182573)
      ·
        refine ⟨24501192368606634088193465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65336512982951024235182573 24501192368606634088193465)
        ·
          refine ⟨18375894276454975566145099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24501192368606634088193465 18375894276454975566145099)
          ·
            refine ⟨27563841414682463349217649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18375894276454975566145099 27563841414682463349217649)
            ·
              refine ⟨20672881061011847511913237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27563841414682463349217649 20672881061011847511913237)
              ·
                refine ⟨969041299734930352120933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20672881061011847511913237 969041299734930352120933)
                ·
                  refine ⟨181695243700299441022675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 969041299734930352120933 181695243700299441022675)
                  ·
                    rfl

theorem cell21_796163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 4].length) (baseStart_796163 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796163 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796163 prefixEnd_796163 := by exact prefixLift 796163
  have htrace : WordTrace (prefixWord ++ tailWord_796163) baseStart_796163 baseEnd_796163 := by
    simpa [prefixWord, tailWord_796163, baseEnd_796163] using wordTrace_append hprefix tailTrace_796163
  have hstable : (prefixWord ++ tailWord_796163).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796163).length < 2 ^ (prefixWord ++ tailWord_796163).sum := by decide
  have hdescent : baseEnd_796163 < baseStart_796163 := by decide
  rcases family_descends (prefixWord ++ tailWord_796163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796177 : List Nat := [1, 2, 2, 1, 1, 2, 4, 8]
def baseStart_796177 : Nat := 118140960795 + 796177 * 2 ^ 59
def prefixEnd_796177 : Nat := 4983230072969 + 3 ^ 40 * 796177 * 2
def baseEnd_796177 : Nat := 60566146230346175929771

theorem tailTrace_796177 : CollatzResearch.WordTrace tailWord_796177 prefixEnd_796177 60566146230346175929771 := by
  unfold tailWord_796177
  simp only [CollatzResearch.WordTrace]
  refine ⟨29038960836594180051090785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19359307224396120034060523 29038960836594180051090785)
  ·
    refine ⟨21779220627445635038318089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29038960836594180051090785 21779220627445635038318089)
    ·
      refine ⟨16334415470584226278738567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21779220627445635038318089 16334415470584226278738567)
      ·
        refine ⟨24501623205876339418107851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16334415470584226278738567 24501623205876339418107851)
        ·
          refine ⟨36752434808814509127161777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24501623205876339418107851 36752434808814509127161777)
          ·
            refine ⟨27564326106610881845371333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36752434808814509127161777 27564326106610881845371333)
            ·
              refine ⟨5168311144989540346007125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27564326106610881845371333 5168311144989540346007125)
              ·
                refine ⟨60566146230346175929771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5168311144989540346007125 60566146230346175929771)
                ·
                  rfl

theorem cell21_796177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 8].length) (baseStart_796177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796177 prefixEnd_796177 := by exact prefixLift 796177
  have htrace : WordTrace (prefixWord ++ tailWord_796177) baseStart_796177 baseEnd_796177 := by
    simpa [prefixWord, tailWord_796177, baseEnd_796177] using wordTrace_append hprefix tailTrace_796177
  have hstable : (prefixWord ++ tailWord_796177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796177).length < 2 ^ (prefixWord ++ tailWord_796177).sum := by decide
  have hdescent : baseEnd_796177 < baseStart_796177 := by decide
  rcases family_descends (prefixWord ++ tailWord_796177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796200 : List Nat := [2, 1, 5, 2, 2, 2, 1, 3, 3]
def baseStart_796200 : Nat := 118140960795 + 796200 * 2 ^ 59
def prefixEnd_796200 : Nat := 4983230072969 + 3 ^ 40 * 796200 * 2
def baseEnd_796200 : Nat := 181703687604395598905933

theorem tailTrace_796200 : CollatzResearch.WordTrace tailWord_796200 prefixEnd_796200 181703687604395598905933 := by
  unfold tailWord_796200
  simp only [CollatzResearch.WordTrace]
  refine ⟨14519899857755427489589027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19359866477007236652785369 14519899857755427489589027)
  ·
    refine ⟨21779849786633141234383541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14519899857755427489589027 21779849786633141234383541)
    ·
      refine ⟨2041860917496856990723457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21779849786633141234383541 2041860917496856990723457)
      ·
        refine ⟨1531395688122642743042593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2041860917496856990723457 1531395688122642743042593)
        ·
          refine ⟨1148546766091982057281945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1531395688122642743042593 1148546766091982057281945)
          ·
            refine ⟨861410074568986542961459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1148546766091982057281945 861410074568986542961459)
            ·
              refine ⟨1292115111853479814442189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 861410074568986542961459 1292115111853479814442189)
              ·
                refine ⟨484543166945054930415821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1292115111853479814442189 484543166945054930415821)
                ·
                  refine ⟨181703687604395598905933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 484543166945054930415821 181703687604395598905933)
                  ·
                    rfl

theorem cell21_796200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 3].length) (baseStart_796200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796200 prefixEnd_796200 := by exact prefixLift 796200
  have htrace : WordTrace (prefixWord ++ tailWord_796200) baseStart_796200 baseEnd_796200 := by
    simpa [prefixWord, tailWord_796200, baseEnd_796200] using wordTrace_append hprefix tailTrace_796200
  have hstable : (prefixWord ++ tailWord_796200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796200).length < 2 ^ (prefixWord ++ tailWord_796200).sum := by decide
  have hdescent : baseEnd_796200 < baseStart_796200 := by decide
  rcases family_descends (prefixWord ++ tailWord_796200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796270 : List Nat := [4, 1, 2, 2, 3, 9]
def baseStart_796270 : Nat := 118140960795 + 796270 * 2 ^ 59
def prefixEnd_796270 : Nat := 4983230072969 + 3 ^ 40 * 796270 * 2
def baseEnd_796270 : Nat := 6730357872521890101449

theorem tailTrace_796270 : CollatzResearch.WordTrace tailWord_796270 prefixEnd_796270 6730357872521890101449 := by
  unfold tailWord_796270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3630294103157157116778283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19361568550171504622817509 3630294103157157116778283)
  ·
    refine ⟨5445441154735735675167425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3630294103157157116778283 5445441154735735675167425)
    ·
      refine ⟨4084080866051801756375569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5445441154735735675167425 4084080866051801756375569)
      ·
        refine ⟨3063060649538851317281677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4084080866051801756375569 3063060649538851317281677)
        ·
          refine ⟨1148647743577069243980629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3063060649538851317281677 1148647743577069243980629)
          ·
            refine ⟨6730357872521890101449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1148647743577069243980629 6730357872521890101449)
            ·
              rfl

theorem cell21_796270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 9].length) (baseStart_796270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796270 prefixEnd_796270 := by exact prefixLift 796270
  have htrace : WordTrace (prefixWord ++ tailWord_796270) baseStart_796270 baseEnd_796270 := by
    simpa [prefixWord, tailWord_796270, baseEnd_796270] using wordTrace_append hprefix tailTrace_796270
  have hstable : (prefixWord ++ tailWord_796270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796270).length < 2 ^ (prefixWord ++ tailWord_796270).sum := by decide
  have hdescent : baseEnd_796270 < baseStart_796270 := by decide
  rcases family_descends (prefixWord ++ tailWord_796270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796284 : List Nat := [2, 2, 2, 1, 1, 2, 1, 5, 5]
def baseStart_796284 : Nat := 118140960795 + 796284 * 2 ^ 59
def prefixEnd_796284 : Nat := 4983230072969 + 3 ^ 40 * 796284 * 2
def baseEnd_796284 : Nat := 181722857548830119505761

theorem tailTrace_796284 : CollatzResearch.WordTrace tailWord_796284 prefixEnd_796284 181722857548830119505761 := by
  unfold tailWord_796284
  simp only [CollatzResearch.WordTrace]
  refine ⟨14521431723603268662617953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19361908964804358216823937 14521431723603268662617953)
  ·
    refine ⟨10891073792702451496963465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14521431723603268662617953 10891073792702451496963465)
    ·
      refine ⟨8168305344526838622722599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10891073792702451496963465 8168305344526838622722599)
      ·
        refine ⟨12252458016790257934083899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8168305344526838622722599 12252458016790257934083899)
        ·
          refine ⟨18378687025185386901125849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12252458016790257934083899 18378687025185386901125849)
          ·
            refine ⟨13784015268889040175844387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18378687025185386901125849 13784015268889040175844387)
            ·
              refine ⟨20676022903333560263766581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13784015268889040175844387 20676022903333560263766581)
              ·
                refine ⟨1938377147187521274728117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20676022903333560263766581 1938377147187521274728117)
                ·
                  refine ⟨181722857548830119505761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1938377147187521274728117 181722857548830119505761)
                  ·
                    rfl

theorem cell21_796284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_796284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796284 prefixEnd_796284 := by exact prefixLift 796284
  have htrace : WordTrace (prefixWord ++ tailWord_796284) baseStart_796284 baseEnd_796284 := by
    simpa [prefixWord, tailWord_796284, baseEnd_796284] using wordTrace_append hprefix tailTrace_796284
  have hstable : (prefixWord ++ tailWord_796284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796284).length < 2 ^ (prefixWord ++ tailWord_796284).sum := by decide
  have hdescent : baseEnd_796284 < baseStart_796284 := by decide
  rcases family_descends (prefixWord ++ tailWord_796284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796360 : List Nat := [2, 1, 3, 1, 2, 2, 1, 4, 5]
def baseStart_796360 : Nat := 118140960795 + 796360 * 2 ^ 59
def prefixEnd_796360 : Nat := 4983230072969 + 3 ^ 40 * 796360 * 2
def baseEnd_796360 : Nat := 181740201784270876238939

theorem tailTrace_796360 : CollatzResearch.WordTrace tailWord_796360 prefixEnd_796360 181740201784270876238939 := by
  unfold tailWord_796360
  simp only [CollatzResearch.WordTrace]
  refine ⟨14522817697465601152501267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19363756929954134870001689 14522817697465601152501267)
  ·
    refine ⟨21784226546198401728751901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14522817697465601152501267 21784226546198401728751901)
    ·
      refine ⟨8169084954824400648281963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21784226546198401728751901 8169084954824400648281963)
      ·
        refine ⟨12253627432236600972422945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8169084954824400648281963 12253627432236600972422945)
        ·
          refine ⟨9190220574177450729317209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12253627432236600972422945 9190220574177450729317209)
          ·
            refine ⟨6892665430633088046987907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9190220574177450729317209 6892665430633088046987907)
            ·
              refine ⟨10338998145949632070481861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6892665430633088046987907 10338998145949632070481861)
              ·
                refine ⟨1938562152365556013215349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10338998145949632070481861 1938562152365556013215349)
                ·
                  refine ⟨181740201784270876238939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1938562152365556013215349 181740201784270876238939)
                  ·
                    rfl

theorem cell21_796360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_796360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796360 prefixEnd_796360 := by exact prefixLift 796360
  have htrace : WordTrace (prefixWord ++ tailWord_796360) baseStart_796360 baseEnd_796360 := by
    simpa [prefixWord, tailWord_796360, baseEnd_796360] using wordTrace_append hprefix tailTrace_796360
  have hstable : (prefixWord ++ tailWord_796360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796360).length < 2 ^ (prefixWord ++ tailWord_796360).sum := by decide
  have hdescent : baseEnd_796360 < baseStart_796360 := by decide
  rcases family_descends (prefixWord ++ tailWord_796360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796380 : List Nat := [2, 2, 5, 1, 3, 1, 7]
def baseStart_796380 : Nat := 118140960795 + 796380 * 2 ^ 59
def prefixEnd_796380 : Nat := 4983230072969 + 3 ^ 40 * 796380 * 2
def baseEnd_796380 : Nat := 20193862895195031767285

theorem tailTrace_796380 : CollatzResearch.WordTrace tailWord_796380 prefixEnd_796380 20193862895195031767285 := by
  unfold tailWord_796380
  simp only [CollatzResearch.WordTrace]
  refine ⟨14523182427429372860365297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19364243236572497147153729 14523182427429372860365297)
  ·
    refine ⟨10892386820572029645273973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14523182427429372860365297 10892386820572029645273973)
    ·
      refine ⟨1021161264428627779244435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10892386820572029645273973 1021161264428627779244435)
      ·
        refine ⟨1531741896642941668866653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1021161264428627779244435 1531741896642941668866653)
        ·
          refine ⟨574403211241103125824995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1531741896642941668866653 574403211241103125824995)
          ·
            refine ⟨861604816861654688737493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574403211241103125824995 861604816861654688737493)
            ·
              refine ⟨20193862895195031767285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 861604816861654688737493 20193862895195031767285)
              ·
                rfl

theorem cell21_796380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 7].length) (baseStart_796380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796380 prefixEnd_796380 := by exact prefixLift 796380
  have htrace : WordTrace (prefixWord ++ tailWord_796380) baseStart_796380 baseEnd_796380 := by
    simpa [prefixWord, tailWord_796380, baseEnd_796380] using wordTrace_append hprefix tailTrace_796380
  have hstable : (prefixWord ++ tailWord_796380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796380).length < 2 ^ (prefixWord ++ tailWord_796380).sum := by decide
  have hdescent : baseEnd_796380 < baseStart_796380 := by decide
  rcases family_descends (prefixWord ++ tailWord_796380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796470 : List Nat := [5, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_796470 : Nat := 118140960795 + 796470 * 2 ^ 59
def prefixEnd_796470 : Nat := 4983230072969 + 3 ^ 40 * 796470 * 2
def baseEnd_796470 : Nat := 181765305282935129405381

theorem tailTrace_796470 : CollatzResearch.WordTrace tailWord_796470 prefixEnd_796470 181765305282935129405381 := by
  unfold tailWord_796470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1815602964033293193219179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 19366431616355127394337909 1815602964033293193219179)
  ·
    refine ⟨2723404446049939789828769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1815602964033293193219179 2723404446049939789828769)
    ·
      refine ⟨2042553334537454842371577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2723404446049939789828769 2042553334537454842371577)
      ·
        refine ⟨1531915000903091131778683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2042553334537454842371577 1531915000903091131778683)
        ·
          refine ⟨2297872501354636697668025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1531915000903091131778683 2297872501354636697668025)
          ·
            refine ⟨1723404376015977523251019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2297872501354636697668025 1723404376015977523251019)
            ·
              refine ⟨2585106564023966284876529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723404376015977523251019 2585106564023966284876529)
              ·
                refine ⟨1938829923017974713657397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2585106564023966284876529 1938829923017974713657397)
                ·
                  refine ⟨181765305282935129405381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1938829923017974713657397 181765305282935129405381)
                  ·
                    rfl

theorem cell21_796470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_796470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796470 prefixEnd_796470 := by exact prefixLift 796470
  have htrace : WordTrace (prefixWord ++ tailWord_796470) baseStart_796470 baseEnd_796470 := by
    simpa [prefixWord, tailWord_796470, baseEnd_796470] using wordTrace_append hprefix tailTrace_796470
  have hstable : (prefixWord ++ tailWord_796470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796470).length < 2 ^ (prefixWord ++ tailWord_796470).sum := by decide
  have hdescent : baseEnd_796470 < baseStart_796470 := by decide
  rcases family_descends (prefixWord ++ tailWord_796470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796512 : List Nat := [2, 1, 1, 3, 3, 2, 1, 3, 5]
def baseStart_796512 : Nat := 118140960795 + 796512 * 2 ^ 59
def prefixEnd_796512 : Nat := 4983230072969 + 3 ^ 40 * 796512 * 2
def baseEnd_796512 : Nat := 181774890255152389705295

theorem tailTrace_796512 : CollatzResearch.WordTrace tailWord_796512 prefixEnd_796512 181774890255152389705295 := by
  unfold tailWord_796512
  simp only [CollatzResearch.WordTrace]
  refine ⟨14525589645190266132267895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19367452860253688176357193 14525589645190266132267895)
  ·
    refine ⟨21788384467785399198401843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14525589645190266132267895 21788384467785399198401843)
    ·
      refine ⟨32682576701678098797602765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21788384467785399198401843 32682576701678098797602765)
      ·
        refine ⟨12255966263129287049101037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32682576701678098797602765 12255966263129287049101037)
        ·
          refine ⟨4595987348673482643412889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12255966263129287049101037 4595987348673482643412889)
          ·
            refine ⟨3446990511505111982559667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4595987348673482643412889 3446990511505111982559667)
            ·
              refine ⟨5170485767257667973839501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3446990511505111982559667 5170485767257667973839501)
              ·
                refine ⟨1938932162721625490189813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5170485767257667973839501 1938932162721625490189813)
                ·
                  refine ⟨181774890255152389705295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1938932162721625490189813 181774890255152389705295)
                  ·
                    rfl

theorem cell21_796512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_796512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796512 prefixEnd_796512 := by exact prefixLift 796512
  have htrace : WordTrace (prefixWord ++ tailWord_796512) baseStart_796512 baseEnd_796512 := by
    simpa [prefixWord, tailWord_796512, baseEnd_796512] using wordTrace_append hprefix tailTrace_796512
  have hstable : (prefixWord ++ tailWord_796512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796512).length < 2 ^ (prefixWord ++ tailWord_796512).sum := by decide
  have hdescent : baseEnd_796512 < baseStart_796512 := by decide
  rcases family_descends (prefixWord ++ tailWord_796512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796602 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 6]
def baseStart_796602 : Nat := 118140960795 + 796602 * 2 ^ 59
def prefixEnd_796602 : Nat := 4983230072969 + 3 ^ 40 * 796602 * 2
def baseEnd_796602 : Nat := 181795429481332233205111

theorem tailTrace_796602 : CollatzResearch.WordTrace tailWord_796602 prefixEnd_796602 181795429481332233205111 := by
  unfold tailWord_796602
  simp only [CollatzResearch.WordTrace]
  refine ⟨7263615465013619408828015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19369641240036318423541373 7263615465013619408828015)
  ·
    refine ⟨10895423197520429113242023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7263615465013619408828015 10895423197520429113242023)
    ·
      refine ⟨16343134796280643669863035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10895423197520429113242023 16343134796280643669863035)
      ·
        refine ⟨24514702194420965504794553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16343134796280643669863035 24514702194420965504794553)
        ·
          refine ⟨18386026645815724128595915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24514702194420965504794553 18386026645815724128595915)
          ·
            refine ⟨27579039968723586192893873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18386026645815724128595915 27579039968723586192893873)
            ·
              refine ⟨20684279976542689644670405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27579039968723586192893873 20684279976542689644670405)
              ·
                refine ⟨3878302495601754308375701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20684279976542689644670405 3878302495601754308375701)
                ·
                  refine ⟨181795429481332233205111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3878302495601754308375701 181795429481332233205111)
                  ·
                    rfl

theorem cell21_796602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_796602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796602 prefixEnd_796602 := by exact prefixLift 796602
  have htrace : WordTrace (prefixWord ++ tailWord_796602) baseStart_796602 baseEnd_796602 := by
    simpa [prefixWord, tailWord_796602, baseEnd_796602] using wordTrace_append hprefix tailTrace_796602
  have hstable : (prefixWord ++ tailWord_796602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796602).length < 2 ^ (prefixWord ++ tailWord_796602).sum := by decide
  have hdescent : baseEnd_796602 < baseStart_796602 := by decide
  rcases family_descends (prefixWord ++ tailWord_796602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796619 : List Nat := [1, 1, 1, 1, 3, 4, 4, 2, 4]
def baseStart_796619 : Nat := 118140960795 + 796619 * 2 ^ 59
def prefixEnd_796619 : Nat := 4983230072969 + 3 ^ 40 * 796619 * 2
def baseEnd_796619 : Nat := 181799309112943981421743

theorem tailTrace_796619 : CollatzResearch.WordTrace tailWord_796619 prefixEnd_796619 181799309112943981421743 := by
  unfold tailWord_796619
  simp only [CollatzResearch.WordTrace]
  refine ⟨29055081900992889538680911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19370054600661926359120607 29055081900992889538680911)
  ·
    refine ⟨43582622851489334308021367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29055081900992889538680911 43582622851489334308021367)
    ·
      refine ⟨65373934277234001462032051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43582622851489334308021367 65373934277234001462032051)
      ·
        refine ⟨98060901415851002193048077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65373934277234001462032051 98060901415851002193048077)
        ·
          refine ⟨36772838030944125822393029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98060901415851002193048077 36772838030944125822393029)
          ·
            refine ⟨6894907130802023591698693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36772838030944125822393029 6894907130802023591698693)
            ·
              refine ⟨1292795087025379423443505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6894907130802023591698693 1292795087025379423443505)
              ·
                refine ⟨969596315269034567582629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1292795087025379423443505 969596315269034567582629)
                ·
                  refine ⟨181799309112943981421743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 969596315269034567582629 181799309112943981421743)
                  ·
                    rfl

theorem cell21_796619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 4].length) (baseStart_796619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796619 prefixEnd_796619 := by exact prefixLift 796619
  have htrace : WordTrace (prefixWord ++ tailWord_796619) baseStart_796619 baseEnd_796619 := by
    simpa [prefixWord, tailWord_796619, baseEnd_796619] using wordTrace_append hprefix tailTrace_796619
  have hstable : (prefixWord ++ tailWord_796619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796619).length < 2 ^ (prefixWord ++ tailWord_796619).sum := by decide
  have hdescent : baseEnd_796619 < baseStart_796619 := by decide
  rcases family_descends (prefixWord ++ tailWord_796619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796650 : List Nat := [3, 1, 3, 1, 2, 1, 5, 5]
def baseStart_796650 : Nat := 118140960795 + 796650 * 2 ^ 59
def prefixEnd_796650 : Nat := 4983230072969 + 3 ^ 40 * 796650 * 2
def baseEnd_796650 : Nat := 60602127911764938801671

theorem tailTrace_796650 : CollatzResearch.WordTrace tailWord_796650 prefixEnd_796650 60602127911764938801671 := by
  unfold tailWord_796650
  simp only [CollatzResearch.WordTrace]
  refine ⟨7264053140970145458264851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19370808375920387888706269 7264053140970145458264851)
  ·
    refine ⟨10896079711455218187397277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7264053140970145458264851 10896079711455218187397277)
    ·
      refine ⟨4086029891795706820273979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10896079711455218187397277 4086029891795706820273979)
      ·
        refine ⟨6129044837693560230410969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4086029891795706820273979 6129044837693560230410969)
        ·
          refine ⟨4596783628270170172808227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6129044837693560230410969 4596783628270170172808227)
          ·
            refine ⟨6895175442405255259212341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4596783628270170172808227 6895175442405255259212341)
            ·
              refine ⟨646422697725492680551157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6895175442405255259212341 646422697725492680551157)
              ·
                refine ⟨60602127911764938801671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 646422697725492680551157 60602127911764938801671)
                ·
                  rfl

theorem cell21_796650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_796650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796650 prefixEnd_796650 := by exact prefixLift 796650
  have htrace : WordTrace (prefixWord ++ tailWord_796650) baseStart_796650 baseEnd_796650 := by
    simpa [prefixWord, tailWord_796650, baseEnd_796650] using wordTrace_append hprefix tailTrace_796650
  have hstable : (prefixWord ++ tailWord_796650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796650).length < 2 ^ (prefixWord ++ tailWord_796650).sum := by decide
  have hdescent : baseEnd_796650 < baseStart_796650 := by decide
  rcases family_descends (prefixWord ++ tailWord_796650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796709 : List Nat := [1, 3, 1, 2, 2, 4, 1, 7]
def baseStart_796709 : Nat := 118140960795 + 796709 * 2 ^ 59
def prefixEnd_796709 : Nat := 4983230072969 + 3 ^ 40 * 796709 * 2
def baseEnd_796709 : Nat := 60606616113041274973853

theorem tailTrace_796709 : CollatzResearch.WordTrace tailWord_796709 prefixEnd_796709 60606616113041274973853 := by
  unfold tailWord_796709
  simp only [CollatzResearch.WordTrace]
  refine ⟨29058364470666834909457181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19372242980444556606304787 29058364470666834909457181)
  ·
    refine ⟨10896886676500063091046443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29058364470666834909457181 10896886676500063091046443)
    ·
      refine ⟨16345330014750094636569665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10896886676500063091046443 16345330014750094636569665)
      ·
        refine ⟨12258997511062570977427249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16345330014750094636569665 12258997511062570977427249)
        ·
          refine ⟨9194248133296928233070437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12258997511062570977427249 9194248133296928233070437)
          ·
            refine ⟨1723921524993174043700707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9194248133296928233070437 1723921524993174043700707)
            ·
              refine ⟨2585882287489761065551061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1723921524993174043700707 2585882287489761065551061)
              ·
                refine ⟨60606616113041274973853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2585882287489761065551061 60606616113041274973853)
                ·
                  rfl

theorem cell21_796709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 7].length) (baseStart_796709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796709 prefixEnd_796709 := by exact prefixLift 796709
  have htrace : WordTrace (prefixWord ++ tailWord_796709) baseStart_796709 baseEnd_796709 := by
    simpa [prefixWord, tailWord_796709, baseEnd_796709] using wordTrace_append hprefix tailTrace_796709
  have hstable : (prefixWord ++ tailWord_796709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796709).length < 2 ^ (prefixWord ++ tailWord_796709).sum := by decide
  have hdescent : baseEnd_796709 < baseStart_796709 := by decide
  rcases family_descends (prefixWord ++ tailWord_796709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796723 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 7]
def baseStart_796723 : Nat := 118140960795 + 796723 * 2 ^ 59
def prefixEnd_796723 : Nat := 4983230072969 + 3 ^ 40 * 796723 * 2
def baseEnd_796723 : Nat := 181823043329862911688197

theorem tailTrace_796723 : CollatzResearch.WordTrace tailWord_796723 prefixEnd_796723 181823043329862911688197 := by
  unfold tailWord_796723
  simp only [CollatzResearch.WordTrace]
  refine ⟨29058875092616115300466823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19372583395077410200311215 29058875092616115300466823)
  ·
    refine ⟨43588312638924172950700235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29058875092616115300466823 43588312638924172950700235)
    ·
      refine ⟨65382468958386259426050353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43588312638924172950700235 65382468958386259426050353)
      ·
        refine ⟨49036851718789694569537765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65382468958386259426050353 49036851718789694569537765)
        ·
          refine ⟨9194409697273067731788331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49036851718789694569537765 9194409697273067731788331)
          ·
            refine ⟨13791614545909601597682497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9194409697273067731788331 13791614545909601597682497)
            ·
              refine ⟨10343710909432201198261873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13791614545909601597682497 10343710909432201198261873)
              ·
                refine ⟨7757783182074150898696405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10343710909432201198261873 7757783182074150898696405)
                ·
                  refine ⟨181823043329862911688197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7757783182074150898696405 181823043329862911688197)
                  ·
                    rfl

theorem cell21_796723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 7].length) (baseStart_796723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796723 prefixEnd_796723 := by exact prefixLift 796723
  have htrace : WordTrace (prefixWord ++ tailWord_796723) baseStart_796723 baseEnd_796723 := by
    simpa [prefixWord, tailWord_796723, baseEnd_796723] using wordTrace_append hprefix tailTrace_796723
  have hstable : (prefixWord ++ tailWord_796723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796723).length < 2 ^ (prefixWord ++ tailWord_796723).sum := by decide
  have hdescent : baseEnd_796723 < baseStart_796723 := by decide
  rcases family_descends (prefixWord ++ tailWord_796723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796833 : List Nat := [1, 2, 3, 3, 1, 2, 1, 5, 3]
def baseStart_796833 : Nat := 118140960795 + 796833 * 2 ^ 59
def prefixEnd_796833 : Nat := 4983230072969 + 3 ^ 40 * 796833 * 2
def baseEnd_796833 : Nat := 181848146828527164854639

theorem tailTrace_796833 : CollatzResearch.WordTrace tailWord_796833 prefixEnd_796833 181848146828527164854639 := by
  unfold tailWord_796833
  simp only [CollatzResearch.WordTrace]
  refine ⟨29062887122217604086971153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19375258081478402724647435 29062887122217604086971153)
  ·
    refine ⟨21797165341663203065228365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29062887122217604086971153 21797165341663203065228365)
    ·
      refine ⟨8173937003123701149460637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21797165341663203065228365 8173937003123701149460637)
      ·
        refine ⟨3065226376171387931047739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8173937003123701149460637 3065226376171387931047739)
        ·
          refine ⟨4597839564257081896571609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3065226376171387931047739 4597839564257081896571609)
          ·
            refine ⟨3448379673192811422428707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4597839564257081896571609 3448379673192811422428707)
            ·
              refine ⟨5172569509789217133643061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3448379673192811422428707 5172569509789217133643061)
              ·
                refine ⟨484928391542739106279037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5172569509789217133643061 484928391542739106279037)
                ·
                  refine ⟨181848146828527164854639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 484928391542739106279037 181848146828527164854639)
                  ·
                    rfl

theorem cell21_796833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 5, 3].length) (baseStart_796833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796833 prefixEnd_796833 := by exact prefixLift 796833
  have htrace : WordTrace (prefixWord ++ tailWord_796833) baseStart_796833 baseEnd_796833 := by
    simpa [prefixWord, tailWord_796833, baseEnd_796833] using wordTrace_append hprefix tailTrace_796833
  have hstable : (prefixWord ++ tailWord_796833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796833).length < 2 ^ (prefixWord ++ tailWord_796833).sum := by decide
  have hdescent : baseEnd_796833 < baseStart_796833 := by decide
  rcases family_descends (prefixWord ++ tailWord_796833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796864 : List Nat := [2, 1, 1, 2, 5, 2, 3, 1, 4]
def baseStart_796864 : Nat := 118140960795 + 796864 * 2 ^ 59
def prefixEnd_796864 : Nat := 4983230072969 + 3 ^ 40 * 796864 * 2
def baseEnd_796864 : Nat := 181855221450877999837909

theorem tailTrace_796864 : CollatzResearch.WordTrace tailWord_796864 prefixEnd_796864 181855221450877999837909 := by
  unfold tailWord_796864
  simp only [CollatzResearch.WordTrace]
  refine ⟨14532008892552648190674823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19376011856736864254233097 14532008892552648190674823)
  ·
    refine ⟨21798013338828972286012235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14532008892552648190674823 21798013338828972286012235)
    ·
      refine ⟨32697020008243458429018353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21798013338828972286012235 32697020008243458429018353)
      ·
        refine ⟨24522765006182593821763765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32697020008243458429018353 24522765006182593821763765)
        ·
          refine ⟨2299009219329618170790353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24522765006182593821763765 2299009219329618170790353)
          ·
            refine ⟨1724256914497213628092765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2299009219329618170790353 1724256914497213628092765)
            ·
              refine ⟨646596342936455110534787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1724256914497213628092765 646596342936455110534787)
              ·
                refine ⟨969894514404682665802181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646596342936455110534787 969894514404682665802181)
                ·
                  refine ⟨181855221450877999837909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 969894514404682665802181 181855221450877999837909)
                  ·
                    rfl

theorem cell21_796864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 4].length) (baseStart_796864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796864 prefixEnd_796864 := by exact prefixLift 796864
  have htrace : WordTrace (prefixWord ++ tailWord_796864) baseStart_796864 baseEnd_796864 := by
    simpa [prefixWord, tailWord_796864, baseEnd_796864] using wordTrace_append hprefix tailTrace_796864
  have hstable : (prefixWord ++ tailWord_796864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796864).length < 2 ^ (prefixWord ++ tailWord_796864).sum := by decide
  have hdescent : baseEnd_796864 < baseStart_796864 := by decide
  rcases family_descends (prefixWord ++ tailWord_796864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796875 : List Nat := [1, 1, 1, 1, 3, 2, 3, 4, 5]
def baseStart_796875 : Nat := 118140960795 + 796875 * 2 ^ 59
def prefixEnd_796875 : Nat := 4983230072969 + 3 ^ 40 * 796875 * 2
def baseEnd_796875 : Nat := 181857731800744425154553

theorem tailTrace_796875 : CollatzResearch.WordTrace tailWord_796875 prefixEnd_796875 181857731800744425154553 := by
  unfold tailWord_796875
  simp only [CollatzResearch.WordTrace]
  refine ⟨29064418988065445260000079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19376279325376963506666719 29064418988065445260000079)
  ·
    refine ⟨43596628482098167890000119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29064418988065445260000079 43596628482098167890000119)
    ·
      refine ⟨65394942723147251835000179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43596628482098167890000119 65394942723147251835000179)
      ·
        refine ⟨98092414084720877752500269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65394942723147251835000179 98092414084720877752500269)
        ·
          refine ⟨36784655281770329157187601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98092414084720877752500269 36784655281770329157187601)
          ·
            refine ⟨27588491461327746867890701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36784655281770329157187601 27588491461327746867890701)
            ·
              refine ⟨10345684297997905075459013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27588491461327746867890701 10345684297997905075459013)
              ·
                refine ⟨1939815805874607201648565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10345684297997905075459013 1939815805874607201648565)
                ·
                  refine ⟨181857731800744425154553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1939815805874607201648565 181857731800744425154553)
                  ·
                    rfl

theorem cell21_796875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 4, 5].length) (baseStart_796875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796875 prefixEnd_796875 := by exact prefixLift 796875
  have htrace : WordTrace (prefixWord ++ tailWord_796875) baseStart_796875 baseEnd_796875 := by
    simpa [prefixWord, tailWord_796875, baseEnd_796875] using wordTrace_append hprefix tailTrace_796875
  have hstable : (prefixWord ++ tailWord_796875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796875).length < 2 ^ (prefixWord ++ tailWord_796875).sum := by decide
  have hdescent : baseEnd_796875 < baseStart_796875 := by decide
  rcases family_descends (prefixWord ++ tailWord_796875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796878 : List Nat := [4, 1, 1, 1, 4, 1, 4, 5]
def baseStart_796878 : Nat := 118140960795 + 796878 * 2 ^ 59
def prefixEnd_796878 : Nat := 4983230072969 + 3 ^ 40 * 796878 * 2
def baseEnd_796878 : Nat := 60619472147205695534849

theorem tailTrace_796878 : CollatzResearch.WordTrace tailWord_796878 prefixEnd_796878 60619472147205695534849 := by
  unfold tailWord_796878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3633066050881822096544911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19376352271369717848239525 3633066050881822096544911)
  ·
    refine ⟨5449599076322733144817367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3633066050881822096544911 5449599076322733144817367)
    ·
      refine ⟨8174398614484099717226051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5449599076322733144817367 8174398614484099717226051)
      ·
        refine ⟨12261597921726149575839077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8174398614484099717226051 12261597921726149575839077)
        ·
          refine ⟨2299049610323653045469827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12261597921726149575839077 2299049610323653045469827)
          ·
            refine ⟨3448574415485479568204741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2299049610323653045469827 3448574415485479568204741)
            ·
              refine ⟨646607702903527419038389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3448574415485479568204741 646607702903527419038389)
              ·
                refine ⟨60619472147205695534849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 646607702903527419038389 60619472147205695534849)
                ·
                  rfl

theorem cell21_796878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_796878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796878 prefixEnd_796878 := by exact prefixLift 796878
  have htrace : WordTrace (prefixWord ++ tailWord_796878) baseStart_796878 baseEnd_796878 := by
    simpa [prefixWord, tailWord_796878, baseEnd_796878] using wordTrace_append hprefix tailTrace_796878
  have hstable : (prefixWord ++ tailWord_796878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796878).length < 2 ^ (prefixWord ++ tailWord_796878).sum := by decide
  have hdescent : baseEnd_796878 < baseStart_796878 := by decide
  rcases family_descends (prefixWord ++ tailWord_796878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_796906 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 6]
def baseStart_796906 : Nat := 118140960795 + 796906 * 2 ^ 59
def prefixEnd_796906 : Nat := 4983230072969 + 3 ^ 40 * 796906 * 2
def baseEnd_796906 : Nat := 181864806423095260137823

theorem tailTrace_796906 : CollatzResearch.WordTrace tailWord_796906 prefixEnd_796906 181864806423095260137823 := by
  unfold tailWord_796906
  simp only [CollatzResearch.WordTrace]
  refine ⟨7266387412738284388594643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19377033100635425036252381 7266387412738284388594643)
  ·
    refine ⟨10899581119107426582891965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7266387412738284388594643 10899581119107426582891965)
    ·
      refine ⟨4087342919665284968584487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10899581119107426582891965 4087342919665284968584487)
      ·
        refine ⟨6131014379497927452876731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4087342919665284968584487 6131014379497927452876731)
        ·
          refine ⟨9196521569246891179315097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6131014379497927452876731 9196521569246891179315097)
          ·
            refine ⟨6897391176935168384486323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9196521569246891179315097 6897391176935168384486323)
            ·
              refine ⟨10346086765402752576729485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6897391176935168384486323 10346086765402752576729485)
              ·
                refine ⟨3879782537026032216273557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10346086765402752576729485 3879782537026032216273557)
                ·
                  refine ⟨181864806423095260137823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3879782537026032216273557 181864806423095260137823)
                  ·
                    rfl

theorem cell21_796906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_796906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_796906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_796906 prefixEnd_796906 := by exact prefixLift 796906
  have htrace : WordTrace (prefixWord ++ tailWord_796906) baseStart_796906 baseEnd_796906 := by
    simpa [prefixWord, tailWord_796906, baseEnd_796906] using wordTrace_append hprefix tailTrace_796906
  have hstable : (prefixWord ++ tailWord_796906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_796906).length < 2 ^ (prefixWord ++ tailWord_796906).sum := by decide
  have hdescent : baseEnd_796906 < baseStart_796906 := by decide
  rcases family_descends (prefixWord ++ tailWord_796906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797013 : List Nat := [1, 3, 2, 2, 4, 1, 8]
def baseStart_797013 : Nat := 118140960795 + 797013 * 2 ^ 59
def prefixEnd_797013 : Nat := 4983230072969 + 3 ^ 40 * 797013 * 2
def baseEnd_797013 : Nat := 20209913920098539094919

theorem tailTrace_797013 : CollatzResearch.WordTrace tailWord_797013 prefixEnd_797013 20209913920098539094919 := by
  unfold tailWord_797013
  simp only [CollatzResearch.WordTrace]
  refine ⟨29069452261565494828523693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19379634841043663219015795 29069452261565494828523693)
  ·
    refine ⟨10901044598087060560696385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29069452261565494828523693 10901044598087060560696385)
    ·
      refine ⟨8175783448565295420522289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10901044598087060560696385 8175783448565295420522289)
      ·
        refine ⟨6131837586423971565391717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8175783448565295420522289 6131837586423971565391717)
        ·
          refine ⟨1149719547454494668510947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6131837586423971565391717 1149719547454494668510947)
          ·
            refine ⟨1724579321181742002766421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149719547454494668510947 1724579321181742002766421)
            ·
              refine ⟨20209913920098539094919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1724579321181742002766421 20209913920098539094919)
              ·
                rfl

theorem cell21_797013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 8].length) (baseStart_797013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797013 prefixEnd_797013 := by exact prefixLift 797013
  have htrace : WordTrace (prefixWord ++ tailWord_797013) baseStart_797013 baseEnd_797013 := by
    simpa [prefixWord, tailWord_797013, baseEnd_797013] using wordTrace_append hprefix tailTrace_797013
  have hstable : (prefixWord ++ tailWord_797013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797013).length < 2 ^ (prefixWord ++ tailWord_797013).sum := by decide
  have hdescent : baseEnd_797013 < baseStart_797013 := by decide
  rcases family_descends (prefixWord ++ tailWord_797013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797120 : List Nat := [2, 1, 1, 2, 3, 1, 1, 7, 3]
def baseStart_797120 : Nat := 118140960795 + 797120 * 2 ^ 59
def prefixEnd_797120 : Nat := 4983230072969 + 3 ^ 40 * 797120 * 2
def baseEnd_797120 : Nat := 181913644138678443570719

theorem tailTrace_797120 : CollatzResearch.WordTrace tailWord_797120 prefixEnd_797120 181913644138678443570719 := by
  unfold tailWord_797120
  simp only [CollatzResearch.WordTrace]
  refine ⟨14536677436088926051334407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19382236581451901401779209 14536677436088926051334407)
  ·
    refine ⟨21805016154133389077001611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14536677436088926051334407 21805016154133389077001611)
    ·
      refine ⟨32707524231200083615502417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21805016154133389077001611 32707524231200083615502417)
      ·
        refine ⟨24530643173400062711626813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32707524231200083615502417 24530643173400062711626813)
        ·
          refine ⟨9198991190025023516860055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24530643173400062711626813 9198991190025023516860055)
          ·
            refine ⟨13798486785037535275290083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9198991190025023516860055 13798486785037535275290083)
            ·
              refine ⟨20697730177556302912935125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13798486785037535275290083 20697730177556302912935125)
              ·
                refine ⟨485103051036475849521917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 20697730177556302912935125 485103051036475849521917)
                ·
                  refine ⟨181913644138678443570719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 485103051036475849521917 181913644138678443570719)
                  ·
                    rfl

theorem cell21_797120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 7, 3].length) (baseStart_797120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797120 prefixEnd_797120 := by exact prefixLift 797120
  have htrace : WordTrace (prefixWord ++ tailWord_797120) baseStart_797120 baseEnd_797120 := by
    simpa [prefixWord, tailWord_797120, baseEnd_797120] using wordTrace_append hprefix tailTrace_797120
  have hstable : (prefixWord ++ tailWord_797120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797120).length < 2 ^ (prefixWord ++ tailWord_797120).sum := by decide
  have hdescent : baseEnd_797120 < baseStart_797120 := by decide
  rcases family_descends (prefixWord ++ tailWord_797120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797154 : List Nat := [3, 3, 3, 2, 1, 1, 1, 2, 5]
def baseStart_797154 : Nat := 118140960795 + 797154 * 2 ^ 59
def prefixEnd_797154 : Nat := 4983230072969 + 3 ^ 40 * 797154 * 2
def baseEnd_797154 : Nat := 181921403401901940003983

theorem tailTrace_797154 : CollatzResearch.WordTrace tailWord_797154 prefixEnd_797154 181921403401901940003983 := by
  unfold tailWord_797154
  simp only [CollatzResearch.WordTrace]
  refine ⟨7268648738513668977351629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19383063302703117272937677 7268648738513668977351629)
  ·
    refine ⟨2725743276942625866506861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7268648738513668977351629 2725743276942625866506861)
    ·
      refine ⟨1022153728853484699940073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2725743276942625866506861 1022153728853484699940073)
      ·
        refine ⟨766615296640113524955055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1022153728853484699940073 766615296640113524955055)
        ·
          refine ⟨1149922944960170287432583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 766615296640113524955055 1149922944960170287432583)
          ·
            refine ⟨1724884417440255431148875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149922944960170287432583 1724884417440255431148875)
            ·
              refine ⟨2587326626160383146723313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724884417440255431148875 2587326626160383146723313)
              ·
                refine ⟨1940494969620287360042485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2587326626160383146723313 1940494969620287360042485)
                ·
                  refine ⟨181921403401901940003983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1940494969620287360042485 181921403401901940003983)
                  ·
                    rfl

theorem cell21_797154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_797154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797154 prefixEnd_797154 := by exact prefixLift 797154
  have htrace : WordTrace (prefixWord ++ tailWord_797154) baseStart_797154 baseEnd_797154 := by
    simpa [prefixWord, tailWord_797154, baseEnd_797154] using wordTrace_append hprefix tailTrace_797154
  have hstable : (prefixWord ++ tailWord_797154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797154).length < 2 ^ (prefixWord ++ tailWord_797154).sum := by decide
  have hdescent : baseEnd_797154 < baseStart_797154 := by decide
  rcases family_descends (prefixWord ++ tailWord_797154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797196 : List Nat := [2, 2, 1, 2, 4, 2, 2, 1, 5]
def baseStart_797196 : Nat := 118140960795 + 797196 * 2 ^ 59
def prefixEnd_797196 : Nat := 4983230072969 + 3 ^ 40 * 797196 * 2
def baseEnd_797196 : Nat := 181930988374119200303897

theorem tailTrace_797196 : CollatzResearch.WordTrace tailWord_797196 prefixEnd_797196 181930988374119200303897 := by
  unfold tailWord_797196
  simp only [CollatzResearch.WordTrace]
  refine ⟨14538063409951258541217721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19384084546601678054956961 14538063409951258541217721)
  ·
    refine ⟨10903547557463443905913291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14538063409951258541217721 10903547557463443905913291)
    ·
      refine ⟨16355321336195165858869937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10903547557463443905913291 16355321336195165858869937)
      ·
        refine ⟨12266491002146374394152453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16355321336195165858869937 12266491002146374394152453)
        ·
          refine ⟨2299967062902445198903585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12266491002146374394152453 2299967062902445198903585)
          ·
            refine ⟨1724975297176833899177689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2299967062902445198903585 1724975297176833899177689)
            ·
              refine ⟨1293731472882625424383267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1724975297176833899177689 1293731472882625424383267)
              ·
                refine ⟨1940597209323938136574901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1293731472882625424383267 1940597209323938136574901)
                ·
                  refine ⟨181930988374119200303897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1940597209323938136574901 181930988374119200303897)
                  ·
                    rfl

theorem cell21_797196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_797196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797196 prefixEnd_797196 := by exact prefixLift 797196
  have htrace : WordTrace (prefixWord ++ tailWord_797196) baseStart_797196 baseEnd_797196 := by
    simpa [prefixWord, tailWord_797196, baseEnd_797196] using wordTrace_append hprefix tailTrace_797196
  have hstable : (prefixWord ++ tailWord_797196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797196).length < 2 ^ (prefixWord ++ tailWord_797196).sum := by decide
  have hdescent : baseEnd_797196 < baseStart_797196 := by decide
  rcases family_descends (prefixWord ++ tailWord_797196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797210 : List Nat := [3, 1, 1, 3, 1, 1, 2, 5, 4]
def baseStart_797210 : Nat := 118140960795 + 797210 * 2 ^ 59
def prefixEnd_797210 : Nat := 4983230072969 + 3 ^ 40 * 797210 * 2
def baseEnd_797210 : Nat := 181934183364858287070535

theorem tailTrace_797210 : CollatzResearch.WordTrace tailWord_797210 prefixEnd_797210 181934183364858287070535 := by
  unfold tailWord_797210
  simp only [CollatzResearch.WordTrace]
  refine ⟨7269159360462949368361271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19384424961234531648963389 7269159360462949368361271)
  ·
    refine ⟨10903739040694424052541907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7269159360462949368361271 10903739040694424052541907)
    ·
      refine ⟨16355608561041636078812861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10903739040694424052541907 16355608561041636078812861)
      ·
        refine ⟨6133353210390613529554823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16355608561041636078812861 6133353210390613529554823)
        ·
          refine ⟨9200029815585920294332235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6133353210390613529554823 9200029815585920294332235)
          ·
            refine ⟨13800044723378880441498353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9200029815585920294332235 13800044723378880441498353)
            ·
              refine ⟨10350033542534160331123765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13800044723378880441498353 10350033542534160331123765)
              ·
                refine ⟨970315644612577531042853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10350033542534160331123765 970315644612577531042853)
                ·
                  refine ⟨181934183364858287070535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 970315644612577531042853 181934183364858287070535)
                  ·
                    rfl

theorem cell21_797210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_797210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797210 prefixEnd_797210 := by exact prefixLift 797210
  have htrace : WordTrace (prefixWord ++ tailWord_797210) baseStart_797210 baseEnd_797210 := by
    simpa [prefixWord, tailWord_797210, baseEnd_797210] using wordTrace_append hprefix tailTrace_797210
  have hstable : (prefixWord ++ tailWord_797210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797210).length < 2 ^ (prefixWord ++ tailWord_797210).sum := by decide
  have hdescent : baseEnd_797210 < baseStart_797210 := by decide
  rcases family_descends (prefixWord ++ tailWord_797210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797261 : List Nat := [1, 6, 1, 1, 2, 3, 2, 1, 4]
def baseStart_797261 : Nat := 118140960795 + 797261 * 2 ^ 59
def prefixEnd_797261 : Nat := 4983230072969 + 3 ^ 40 * 797261 * 2
def baseEnd_797261 : Nat := 181945822259693531720431

theorem tailTrace_797261 : CollatzResearch.WordTrace tailWord_797261 prefixEnd_797261 181945822259693531720431 := by
  unfold tailWord_797261
  simp only [CollatzResearch.WordTrace]
  refine ⟨29078497564667033183551637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19385665043111355455701091 29078497564667033183551637)
  ·
    refine ⟨1363054573343767180478983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29078497564667033183551637 1363054573343767180478983)
    ·
      refine ⟨2044581860015650770718475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1363054573343767180478983 2044581860015650770718475)
      ·
        refine ⟨3066872790023476156077713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2044581860015650770718475 3066872790023476156077713)
        ·
          refine ⟨2300154592517607117058285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3066872790023476156077713 2300154592517607117058285)
          ·
            refine ⟨862557972194102668896857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2300154592517607117058285 862557972194102668896857)
            ·
              refine ⟨646918479145577001672643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 862557972194102668896857 646918479145577001672643)
              ·
                refine ⟨970377718718365502508965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646918479145577001672643 970377718718365502508965)
                ·
                  refine ⟨181945822259693531720431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 970377718718365502508965 181945822259693531720431)
                  ·
                    rfl

theorem cell21_797261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_797261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797261 prefixEnd_797261 := by exact prefixLift 797261
  have htrace : WordTrace (prefixWord ++ tailWord_797261) baseStart_797261 baseEnd_797261 := by
    simpa [prefixWord, tailWord_797261, baseEnd_797261] using wordTrace_append hprefix tailTrace_797261
  have hstable : (prefixWord ++ tailWord_797261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797261).length < 2 ^ (prefixWord ++ tailWord_797261).sum := by decide
  have hdescent : baseEnd_797261 < baseStart_797261 := by decide
  rcases family_descends (prefixWord ++ tailWord_797261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797317 : List Nat := [1, 3, 1, 1, 4, 4, 1, 6]
def baseStart_797317 : Nat := 118140960795 + 797317 * 2 ^ 59
def prefixEnd_797317 : Nat := 4983230072969 + 3 ^ 40 * 797317 * 2
def baseEnd_797317 : Nat := 60652867407549959595661

theorem tailTrace_797317 : CollatzResearch.WordTrace tailWord_797317 prefixEnd_797317 60652867407549959595661 := by
  unfold tailWord_797317
  simp only [CollatzResearch.WordTrace]
  refine ⟨29080540052464154747590205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19387026701642769831726803 29080540052464154747590205)
  ·
    refine ⟨10905202519674058030346327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29080540052464154747590205 10905202519674058030346327)
    ·
      refine ⟨16357803779511087045519491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10905202519674058030346327 16357803779511087045519491)
      ·
        refine ⟨24536705669266630568279237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16357803779511087045519491 24536705669266630568279237)
        ·
          refine ⟨4600632312987493231552357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24536705669266630568279237 4600632312987493231552357)
          ·
            refine ⟨862618558685154980916067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4600632312987493231552357 862618558685154980916067)
            ·
              refine ⟨1293927838027732471374101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862618558685154980916067 1293927838027732471374101)
              ·
                refine ⟨60652867407549959595661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1293927838027732471374101 60652867407549959595661)
                ·
                  rfl

theorem cell21_797317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 6].length) (baseStart_797317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797317 prefixEnd_797317 := by exact prefixLift 797317
  have htrace : WordTrace (prefixWord ++ tailWord_797317) baseStart_797317 baseEnd_797317 := by
    simpa [prefixWord, tailWord_797317, baseEnd_797317] using wordTrace_append hprefix tailTrace_797317
  have hstable : (prefixWord ++ tailWord_797317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797317).length < 2 ^ (prefixWord ++ tailWord_797317).sum := by decide
  have hdescent : baseEnd_797317 < baseStart_797317 := by decide
  rcases family_descends (prefixWord ++ tailWord_797317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797354 : List Nat := [3, 1, 5, 2, 2, 1, 1, 2, 4]
def baseStart_797354 : Nat := 118140960795 + 797354 * 2 ^ 59
def prefixEnd_797354 : Nat := 4983230072969 + 3 ^ 40 * 797354 * 2
def baseEnd_797354 : Nat := 181967046126746036670241

theorem tailTrace_797354 : CollatzResearch.WordTrace tailWord_797354 prefixEnd_797354 181967046126746036670241 := by
  unfold tailWord_797354
  simp only [CollatzResearch.WordTrace]
  refine ⟨7270472388332527516671779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 19387926368886740044458077 7270472388332527516671779)
  ·
    refine ⟨10905708582498791275007669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7270472388332527516671779 10905708582498791275007669)
    ·
      refine ⟨1022410179609261682031969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10905708582498791275007669 1022410179609261682031969)
      ·
        refine ⟨766807634706946261523977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1022410179609261682031969 766807634706946261523977)
        ·
          refine ⟨575105726030209696142983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 766807634706946261523977 575105726030209696142983)
          ·
            refine ⟨862658589045314544214475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575105726030209696142983 862658589045314544214475)
            ·
              refine ⟨1293987883567971816321713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862658589045314544214475 1293987883567971816321713)
              ·
                refine ⟨970490912675978862241285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1293987883567971816321713 970490912675978862241285)
                ·
                  refine ⟨181967046126746036670241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 970490912675978862241285 181967046126746036670241)
                  ·
                    rfl

theorem cell21_797354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_797354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797354 prefixEnd_797354 := by exact prefixLift 797354
  have htrace : WordTrace (prefixWord ++ tailWord_797354) baseStart_797354 baseEnd_797354 := by
    simpa [prefixWord, tailWord_797354, baseEnd_797354] using wordTrace_append hprefix tailTrace_797354
  have hstable : (prefixWord ++ tailWord_797354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797354).length < 2 ^ (prefixWord ++ tailWord_797354).sum := by decide
  have hdescent : baseEnd_797354 < baseStart_797354 := by decide
  rcases family_descends (prefixWord ++ tailWord_797354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797365 : List Nat := [1, 3, 3, 3, 1, 1, 2, 4, 3]
def baseStart_797365 : Nat := 118140960795 + 797365 * 2 ^ 59
def prefixEnd_797365 : Nat := 4983230072969 + 3 ^ 40 * 797365 * 2
def baseEnd_797365 : Nat := 181969556476612461986885

theorem tailTrace_797365 : CollatzResearch.WordTrace tailWord_797365 prefixEnd_797365 181969556476612461986885 := by
  unfold tailWord_797365
  simp only [CollatzResearch.WordTrace]
  refine ⟨29082290756290258945337549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19388193837526839296891699 29082290756290258945337549)
  ·
    refine ⟨10905859033608847104501581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29082290756290258945337549 10905859033608847104501581)
    ·
      refine ⟨4089697137603317664188093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10905859033608847104501581 4089697137603317664188093)
      ·
        refine ⟨1533636426601244124070535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4089697137603317664188093 1533636426601244124070535)
        ·
          refine ⟨2300454639901866186105803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1533636426601244124070535 2300454639901866186105803)
          ·
            refine ⟨3450681959852799279158705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2300454639901866186105803 3450681959852799279158705)
            ·
              refine ⟨2588011469889599459369029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3450681959852799279158705 2588011469889599459369029)
              ·
                refine ⟨485252150604299898631693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2588011469889599459369029 485252150604299898631693)
                ·
                  refine ⟨181969556476612461986885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 485252150604299898631693 181969556476612461986885)
                  ·
                    rfl

theorem cell21_797365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_797365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797365 prefixEnd_797365 := by exact prefixLift 797365
  have htrace : WordTrace (prefixWord ++ tailWord_797365) baseStart_797365 baseEnd_797365 := by
    simpa [prefixWord, tailWord_797365, baseEnd_797365] using wordTrace_append hprefix tailTrace_797365
  have hstable : (prefixWord ++ tailWord_797365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797365).length < 2 ^ (prefixWord ++ tailWord_797365).sum := by decide
  have hdescent : baseEnd_797365 < baseStart_797365 := by decide
  rcases family_descends (prefixWord ++ tailWord_797365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797469 : List Nat := [1, 4, 2, 4, 1, 9]
def baseStart_797469 : Nat := 118140960795 + 797469 * 2 ^ 59
def prefixEnd_797469 : Nat := 4983230072969 + 3 ^ 40 * 797469 * 2
def baseEnd_797469 : Nat := 6740492247908570083457

theorem tailTrace_797469 : CollatzResearch.WordTrace tailWord_797469 prefixEnd_797469 6740492247908570083457 := by
  unfold tailWord_797469
  simp only [CollatzResearch.WordTrace]
  refine ⟨29086083947913484707123461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19390722631942323138082307 29086083947913484707123461)
  ·
    refine ⟨5453640740233778382585649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29086083947913484707123461 5453640740233778382585649)
    ·
      refine ⟨4090230555175333786939237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5453640740233778382585649 4090230555175333786939237)
      ·
        refine ⟨766918229095375085051107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4090230555175333786939237 766918229095375085051107)
        ·
          refine ⟨1150377343643062627576661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 766918229095375085051107 1150377343643062627576661)
          ·
            refine ⟨6740492247908570083457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1150377343643062627576661 6740492247908570083457)
            ·
              rfl

theorem cell21_797469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 9].length) (baseStart_797469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797469 prefixEnd_797469 := by exact prefixLift 797469
  have htrace : WordTrace (prefixWord ++ tailWord_797469) baseStart_797469 baseEnd_797469 := by
    simpa [prefixWord, tailWord_797469, baseEnd_797469] using wordTrace_append hprefix tailTrace_797469
  have hstable : (prefixWord ++ tailWord_797469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797469).length < 2 ^ (prefixWord ++ tailWord_797469).sum := by decide
  have hdescent : baseEnd_797469 < baseStart_797469 := by decide
  rcases family_descends (prefixWord ++ tailWord_797469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797486 : List Nat := [4, 1, 3, 2, 1, 3, 1, 6]
def baseStart_797486 : Nat := 118140960795 + 797486 * 2 ^ 59
def prefixEnd_797486 : Nat := 4983230072969 + 3 ^ 40 * 797486 * 2
def baseEnd_797486 : Nat := 60665723441714380156657

theorem tailTrace_797486 : CollatzResearch.WordTrace tailWord_797486 prefixEnd_797486 60665723441714380156657 := by
  unfold tailWord_797486
  simp only [CollatzResearch.WordTrace]
  refine ⟨3635837998606487076311539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19391135992567931073661541 3635837998606487076311539)
  ·
    refine ⟨5453756997909730614467309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3635837998606487076311539 5453756997909730614467309)
    ·
      refine ⟨2045158874216148980425241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5453756997909730614467309 2045158874216148980425241)
      ·
        refine ⟨1533869155662111735318931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2045158874216148980425241 1533869155662111735318931)
        ·
          refine ⟨2300803733493167602978397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1533869155662111735318931 2300803733493167602978397)
          ·
            refine ⟨862801400059937851116899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2300803733493167602978397 862801400059937851116899)
            ·
              refine ⟨1294202100089906776675349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 862801400059937851116899 1294202100089906776675349)
              ·
                refine ⟨60665723441714380156657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1294202100089906776675349 60665723441714380156657)
                ·
                  rfl

theorem cell21_797486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_797486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797486 prefixEnd_797486 := by exact prefixLift 797486
  have htrace : WordTrace (prefixWord ++ tailWord_797486) baseStart_797486 baseEnd_797486 := by
    simpa [prefixWord, tailWord_797486, baseEnd_797486] using wordTrace_append hprefix tailTrace_797486
  have hstable : (prefixWord ++ tailWord_797486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797486).length < 2 ^ (prefixWord ++ tailWord_797486).sum := by decide
  have hdescent : baseEnd_797486 < baseStart_797486 := by decide
  rcases family_descends (prefixWord ++ tailWord_797486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797573 : List Nat := [1, 3, 1, 1, 3, 3, 1, 2, 6]
def baseStart_797573 : Nat := 118140960795 + 797573 * 2 ^ 59
def prefixEnd_797573 : Nat := 4983230072969 + 3 ^ 40 * 797573 * 2
def baseEnd_797573 : Nat := 182017024910450322519793

theorem tailTrace_797573 : CollatzResearch.WordTrace tailWord_797573 prefixEnd_797573 182017024910450322519793 := by
  unfold tailWord_797573
  simp only [CollatzResearch.WordTrace]
  refine ⟨29089877139536710468909373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19393251426357806979272915 29089877139536710468909373)
  ·
    refine ⟨10908703927326266425841015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29089877139536710468909373 10908703927326266425841015)
    ·
      refine ⟨16363055890989399638761523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10908703927326266425841015 16363055890989399638761523)
      ·
        refine ⟨24544583836484099458142285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16363055890989399638761523 24544583836484099458142285)
        ·
          refine ⟨9204218938681537296803357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24544583836484099458142285 9204218938681537296803357)
          ·
            refine ⟨3451582102005576486301259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9204218938681537296803357 3451582102005576486301259)
            ·
              refine ⟨5177373153008364729451889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3451582102005576486301259 5177373153008364729451889)
              ·
                refine ⟨3883029864756273547088917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5177373153008364729451889 3883029864756273547088917)
                ·
                  refine ⟨182017024910450322519793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3883029864756273547088917 182017024910450322519793)
                  ·
                    rfl

theorem cell21_797573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_797573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797573 prefixEnd_797573 := by exact prefixLift 797573
  have htrace : WordTrace (prefixWord ++ tailWord_797573) baseStart_797573 baseEnd_797573 := by
    simpa [prefixWord, tailWord_797573, baseEnd_797573] using wordTrace_append hprefix tailTrace_797573
  have hstable : (prefixWord ++ tailWord_797573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797573).length < 2 ^ (prefixWord ++ tailWord_797573).sum := by decide
  have hdescent : baseEnd_797573 < baseStart_797573 := by decide
  rcases family_descends (prefixWord ++ tailWord_797573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797604 : List Nat := [2, 3, 1, 2, 1, 2, 4, 6]
def baseStart_797604 : Nat := 118140960795 + 797604 * 2 ^ 59
def prefixEnd_797604 : Nat := 4983230072969 + 3 ^ 40 * 797604 * 2
def baseEnd_797604 : Nat := 60674699844267052501021

theorem tailTrace_797604 : CollatzResearch.WordTrace tailWord_797604 prefixEnd_797604 60674699844267052501021 := by
  unfold tailWord_797604
  simp only [CollatzResearch.WordTrace]
  refine ⟨14545503901212201381643933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19394005201616268508858577 14545503901212201381643933)
  ·
    refine ⟨5454563962954575518116475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14545503901212201381643933 5454563962954575518116475)
    ·
      refine ⟨8181845944431863277174713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5454563962954575518116475 8181845944431863277174713)
      ·
        refine ⟨6136384458323897457881035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8181845944431863277174713 6136384458323897457881035)
        ·
          refine ⟨9204576687485846186821553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6136384458323897457881035 9204576687485846186821553)
          ·
            refine ⟨6903432515614384640116165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9204576687485846186821553 6903432515614384640116165)
            ·
              refine ⟨1294393596677697120021781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6903432515614384640116165 1294393596677697120021781)
              ·
                refine ⟨60674699844267052501021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1294393596677697120021781 60674699844267052501021)
                ·
                  rfl

theorem cell21_797604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 6].length) (baseStart_797604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797604 prefixEnd_797604 := by exact prefixLift 797604
  have htrace : WordTrace (prefixWord ++ tailWord_797604) baseStart_797604 baseEnd_797604 := by
    simpa [prefixWord, tailWord_797604, baseEnd_797604] using wordTrace_append hprefix tailTrace_797604
  have hstable : (prefixWord ++ tailWord_797604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797604).length < 2 ^ (prefixWord ++ tailWord_797604).sum := by decide
  have hdescent : baseEnd_797604 < baseStart_797604 := by decide
  rcases family_descends (prefixWord ++ tailWord_797604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797607 : List Nat := [1, 1, 6, 1, 3, 1, 1, 3, 4]
def baseStart_797607 : Nat := 118140960795 + 797607 * 2 ^ 59
def prefixEnd_797607 : Nat := 4983230072969 + 3 ^ 40 * 797607 * 2
def baseEnd_797607 : Nat := 182024784173673818953057

theorem tailTrace_797607 : CollatzResearch.WordTrace tailWord_797607 prefixEnd_797607 182024784173673818953057 := by
  unfold tailWord_797607
  simp only [CollatzResearch.WordTrace]
  refine ⟨29091117221413534275647075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19394078147609022850431383 29091117221413534275647075)
  ·
    refine ⟨43636675832120301413470613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29091117221413534275647075 43636675832120301413470613)
    ·
      refine ⟨2045469179630639128756435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43636675832120301413470613 2045469179630639128756435)
      ·
        refine ⟨3068203769445958693134653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2045469179630639128756435 3068203769445958693134653)
        ·
          refine ⟨1150576413542234509925495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3068203769445958693134653 1150576413542234509925495)
          ·
            refine ⟨1725864620313351764888243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1150576413542234509925495 1725864620313351764888243)
            ·
              refine ⟨2588796930470027647332365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1725864620313351764888243 2588796930470027647332365)
              ·
                refine ⟨970798848926260367749637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2588796930470027647332365 970798848926260367749637)
                ·
                  refine ⟨182024784173673818953057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 970798848926260367749637 182024784173673818953057)
                  ·
                    rfl

theorem cell21_797607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 3, 4].length) (baseStart_797607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797607 prefixEnd_797607 := by exact prefixLift 797607
  have htrace : WordTrace (prefixWord ++ tailWord_797607) baseStart_797607 baseEnd_797607 := by
    simpa [prefixWord, tailWord_797607, baseEnd_797607] using wordTrace_append hprefix tailTrace_797607
  have hstable : (prefixWord ++ tailWord_797607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797607).length < 2 ^ (prefixWord ++ tailWord_797607).sum := by decide
  have hdescent : baseEnd_797607 < baseStart_797607 := by decide
  rcases family_descends (prefixWord ++ tailWord_797607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797739 : List Nat := [1, 1, 1, 1, 2, 1, 7, 7]
def baseStart_797739 : Nat := 118140960795 + 797739 * 2 ^ 59
def prefixEnd_797739 : Nat := 4983230072969 + 3 ^ 40 * 797739 * 2
def baseEnd_797739 : Nat := 60684969457356974250929

theorem tailTrace_797739 : CollatzResearch.WordTrace tailWord_797739 prefixEnd_797739 60684969457356974250929 := by
  unfold tailWord_797739
  simp only [CollatzResearch.WordTrace]
  refine ⟨29095931656935320819452271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19397287771290213879634847 29095931656935320819452271)
  ·
    refine ⟨43643897485402981229178407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29095931656935320819452271 43643897485402981229178407)
    ·
      refine ⟨65465846228104471843767611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43643897485402981229178407 65465846228104471843767611)
      ·
        refine ⟨98198769342156707765651417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65465846228104471843767611 98198769342156707765651417)
        ·
          refine ⟨73649077006617530824238563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98198769342156707765651417 73649077006617530824238563)
          ·
            refine ⟨110473615509926296236357845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73649077006617530824238563 110473615509926296236357845)
            ·
              refine ⟨2589225363513897568039637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 110473615509926296236357845 2589225363513897568039637)
              ·
                refine ⟨60684969457356974250929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2589225363513897568039637 60684969457356974250929)
                ·
                  rfl

theorem cell21_797739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 7].length) (baseStart_797739 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797739 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797739 prefixEnd_797739 := by exact prefixLift 797739
  have htrace : WordTrace (prefixWord ++ tailWord_797739) baseStart_797739 baseEnd_797739 := by
    simpa [prefixWord, tailWord_797739, baseEnd_797739] using wordTrace_append hprefix tailTrace_797739
  have hstable : (prefixWord ++ tailWord_797739).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797739).length < 2 ^ (prefixWord ++ tailWord_797739).sum := by decide
  have hdescent : baseEnd_797739 < baseStart_797739 := by decide
  rcases family_descends (prefixWord ++ tailWord_797739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797756 : List Nat := [2, 2, 2, 2, 2, 4, 7]
def baseStart_797756 : Nat := 118140960795 + 797756 * 2 ^ 59
def prefixEnd_797756 : Nat := 4983230072969 + 3 ^ 40 * 797756 * 2
def baseEnd_797756 : Nat := 20228754222631407885491

theorem tailTrace_797756 : CollatzResearch.WordTrace tailWord_797756 prefixEnd_797756 20228754222631407885491 := by
  unfold tailWord_797756
  simp only [CollatzResearch.WordTrace]
  refine ⟨14548275848936866361410561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19397701131915821815214081 14548275848936866361410561)
  ·
    refine ⟨10911206886702649771057921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14548275848936866361410561 10911206886702649771057921)
    ·
      refine ⟨8183405165026987328293441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10911206886702649771057921 8183405165026987328293441)
      ·
        refine ⟨6137553873770240496220081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8183405165026987328293441 6137553873770240496220081)
        ·
          refine ⟨4603165405327680372165061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6137553873770240496220081 4603165405327680372165061)
          ·
            refine ⟨863093513498940069780949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4603165405327680372165061 863093513498940069780949)
            ·
              refine ⟨20228754222631407885491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 863093513498940069780949 20228754222631407885491)
              ·
                rfl

theorem cell21_797756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 7].length) (baseStart_797756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797756 prefixEnd_797756 := by exact prefixLift 797756
  have htrace : WordTrace (prefixWord ++ tailWord_797756) baseStart_797756 baseEnd_797756 := by
    simpa [prefixWord, tailWord_797756, baseEnd_797756] using wordTrace_append hprefix tailTrace_797756
  have hstable : (prefixWord ++ tailWord_797756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797756).length < 2 ^ (prefixWord ++ tailWord_797756).sum := by decide
  have hdescent : baseEnd_797756 < baseStart_797756 := by decide
  rcases family_descends (prefixWord ++ tailWord_797756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797773 : List Nat := [1, 6, 1, 1, 1, 3, 2, 6]
def baseStart_797773 : Nat := 118140960795 + 797773 * 2 ^ 59
def prefixEnd_797773 : Nat := 4983230072969 + 3 ^ 40 * 797773 * 2
def baseEnd_797773 : Nat := 60687555878431473062017

theorem tailTrace_797773 : CollatzResearch.WordTrace tailWord_797773 prefixEnd_797773 60687555878431473062017 := by
  unfold tailWord_797773
  simp only [CollatzResearch.WordTrace]
  refine ⟨29097171738812144626189973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19398114492541429750793315 29097171738812144626189973)
  ·
    refine ⟨1363929925256819279352655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29097171738812144626189973 1363929925256819279352655)
    ·
      refine ⟨2045894887885228919028983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1363929925256819279352655 2045894887885228919028983)
      ·
        refine ⟨3068842331827843378543475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2045894887885228919028983 3068842331827843378543475)
        ·
          refine ⟨4603263497741765067815213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3068842331827843378543475 4603263497741765067815213)
          ·
            refine ⟨1726223811653161900430705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4603263497741765067815213 1726223811653161900430705)
            ·
              refine ⟨1294667858739871425323029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1726223811653161900430705 1294667858739871425323029)
              ·
                refine ⟨60687555878431473062017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1294667858739871425323029 60687555878431473062017)
                ·
                  rfl

theorem cell21_797773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 6].length) (baseStart_797773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797773 prefixEnd_797773 := by exact prefixLift 797773
  have htrace : WordTrace (prefixWord ++ tailWord_797773) baseStart_797773 baseEnd_797773 := by
    simpa [prefixWord, tailWord_797773, baseEnd_797773] using wordTrace_append hprefix tailTrace_797773
  have hstable : (prefixWord ++ tailWord_797773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797773).length < 2 ^ (prefixWord ++ tailWord_797773).sum := by decide
  have hdescent : baseEnd_797773 < baseStart_797773 := by decide
  rcases family_descends (prefixWord ++ tailWord_797773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797790 : List Nat := [4, 4, 1, 1, 1, 1, 2, 7]
def baseStart_797790 : Nat := 118140960795 + 797790 * 2 ^ 59
def prefixEnd_797790 : Nat := 4983230072969 + 3 ^ 40 * 797790 * 2
def baseEnd_797790 : Nat := 60688849088968722467561

theorem tailTrace_797790 : CollatzResearch.WordTrace tailWord_797790 prefixEnd_797790 60688849088968722467561 := by
  unfold tailWord_797790
  simp only [CollatzResearch.WordTrace]
  refine ⟨3637223972468819566194853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 19398527853167037686372549 3637223972468819566194853)
  ·
    refine ⟨681979494837903668661535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3637223972468819566194853 681979494837903668661535)
    ·
      refine ⟨1022969242256855502992303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 681979494837903668661535 1022969242256855502992303)
      ·
        refine ⟨1534453863385283254488455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1022969242256855502992303 1534453863385283254488455)
        ·
          refine ⟨2301680795077924881732683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534453863385283254488455 2301680795077924881732683)
          ·
            refine ⟨3452521192616887322599025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301680795077924881732683 3452521192616887322599025)
            ·
              refine ⟨2589390894462665491949269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3452521192616887322599025 2589390894462665491949269)
              ·
                refine ⟨60688849088968722467561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2589390894462665491949269 60688849088968722467561)
                ·
                  rfl

theorem cell21_797790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_797790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797790 prefixEnd_797790 := by exact prefixLift 797790
  have htrace : WordTrace (prefixWord ++ tailWord_797790) baseStart_797790 baseEnd_797790 := by
    simpa [prefixWord, tailWord_797790, baseEnd_797790] using wordTrace_append hprefix tailTrace_797790
  have hstable : (prefixWord ++ tailWord_797790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797790).length < 2 ^ (prefixWord ++ tailWord_797790).sum := by decide
  have hdescent : baseEnd_797790 < baseStart_797790 := by decide
  rcases family_descends (prefixWord ++ tailWord_797790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797925 : List Nat := [1, 3, 1, 4, 4, 1, 7]
def baseStart_797925 : Nat := 118140960795 + 797925 * 2 ^ 59
def prefixEnd_797925 : Nat := 4983230072969 + 3 ^ 40 * 797925 * 2
def baseEnd_797925 : Nat := 20233039567352881405823

theorem tailTrace_797925 : CollatzResearch.WordTrace tailWord_797925 prefixEnd_797925 20233039567352881405823 := by
  unfold tailWord_797925
  simp only [CollatzResearch.WordTrace]
  refine ⟨29102715634261474585723229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19401810422840983057148819 29102715634261474585723229)
  ·
    refine ⟨10913518362848052969646211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29102715634261474585723229 10913518362848052969646211)
    ·
      refine ⟨16370277544272079454469317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10913518362848052969646211 16370277544272079454469317)
      ·
        refine ⟨3069427039551014897712997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16370277544272079454469317 3069427039551014897712997)
        ·
          refine ⟨575517569915815293321187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3069427039551014897712997 575517569915815293321187)
          ·
            refine ⟨863276354873722939981781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575517569915815293321187 863276354873722939981781)
            ·
              refine ⟨20233039567352881405823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 863276354873722939981781 20233039567352881405823)
              ·
                rfl

theorem cell21_797925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 7].length) (baseStart_797925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797925 prefixEnd_797925 := by exact prefixLift 797925
  have htrace : WordTrace (prefixWord ++ tailWord_797925) baseStart_797925 baseEnd_797925 := by
    simpa [prefixWord, tailWord_797925, baseEnd_797925] using wordTrace_append hprefix tailTrace_797925
  have hstable : (prefixWord ++ tailWord_797925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797925).length < 2 ^ (prefixWord ++ tailWord_797925).sum := by decide
  have hdescent : baseEnd_797925 < baseStart_797925 := by decide
  rcases family_descends (prefixWord ++ tailWord_797925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797939 : List Nat := [1, 1, 1, 2, 2, 7, 1, 1, 5]
def baseStart_797939 : Nat := 118140960795 + 797939 * 2 ^ 59
def prefixEnd_797939 : Nat := 4983230072969 + 3 ^ 40 * 797939 * 2
def baseEnd_797939 : Nat := 182100551096915019419045

theorem tailTrace_797939 : CollatzResearch.WordTrace tailWord_797939 prefixEnd_797939 182100551096915019419045 := by
  unfold tailWord_797939
  simp only [CollatzResearch.WordTrace]
  refine ⟨29103226256210754976732871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 19402150837473836651155247 29103226256210754976732871)
  ·
    refine ⟨43654839384316132465099307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29103226256210754976732871 43654839384316132465099307)
    ·
      refine ⟨65482259076474198697648961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43654839384316132465099307 65482259076474198697648961)
      ·
        refine ⟨49111694307355649023236721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65482259076474198697648961 49111694307355649023236721)
        ·
          refine ⟨36833770730516736767427541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49111694307355649023236721 36833770730516736767427541)
          ·
            refine ⟨863291501496486017986583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 36833770730516736767427541 863291501496486017986583)
            ·
              refine ⟨1294937252244729026979875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863291501496486017986583 1294937252244729026979875)
              ·
                refine ⟨1942405878367093540469813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1294937252244729026979875 1942405878367093540469813)
                ·
                  refine ⟨182100551096915019419045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1942405878367093540469813 182100551096915019419045)
                  ·
                    rfl

theorem cell21_797939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 5].length) (baseStart_797939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797939 prefixEnd_797939 := by exact prefixLift 797939
  have htrace : WordTrace (prefixWord ++ tailWord_797939) baseStart_797939 baseEnd_797939 := by
    simpa [prefixWord, tailWord_797939, baseEnd_797939] using wordTrace_append hprefix tailTrace_797939
  have hstable : (prefixWord ++ tailWord_797939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797939).length < 2 ^ (prefixWord ++ tailWord_797939).sum := by decide
  have hdescent : baseEnd_797939 < baseStart_797939 := by decide
  rcases family_descends (prefixWord ++ tailWord_797939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_797984 : List Nat := [2, 1, 1, 5, 4, 8]
def baseStart_797984 : Nat := 118140960795 + 797984 * 2 ^ 59
def prefixEnd_797984 : Nat := 4983230072969 + 3 ^ 40 * 797984 * 2
def baseEnd_797984 : Nat := 6744845211481664487739

theorem tailTrace_797984 : CollatzResearch.WordTrace tailWord_797984 prefixEnd_797984 6744845211481664487739 := by
  unfold tailWord_797984
  simp only [CollatzResearch.WordTrace]
  refine ⟨14552433770523863831060503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 19403245027365151774747337 14552433770523863831060503)
  ·
    refine ⟨21828650655785795746590755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14552433770523863831060503 21828650655785795746590755)
    ·
      refine ⟨32742975983678693619886133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21828650655785795746590755 32742975983678693619886133)
      ·
        refine ⟨3069653998469877526864325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32742975983678693619886133 3069653998469877526864325)
        ·
          refine ⟨575560124713102036287061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3069653998469877526864325 575560124713102036287061)
          ·
            refine ⟨6744845211481664487739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 575560124713102036287061 6744845211481664487739)
            ·
              rfl

theorem cell21_797984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 8].length) (baseStart_797984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_797984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_797984 prefixEnd_797984 := by exact prefixLift 797984
  have htrace : WordTrace (prefixWord ++ tailWord_797984) baseStart_797984 baseEnd_797984 := by
    simpa [prefixWord, tailWord_797984, baseEnd_797984] using wordTrace_append hprefix tailTrace_797984
  have hstable : (prefixWord ++ tailWord_797984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_797984).length < 2 ^ (prefixWord ++ tailWord_797984).sum := by decide
  have hdescent : baseEnd_797984 < baseStart_797984 := by decide
  rcases family_descends (prefixWord ++ tailWord_797984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
