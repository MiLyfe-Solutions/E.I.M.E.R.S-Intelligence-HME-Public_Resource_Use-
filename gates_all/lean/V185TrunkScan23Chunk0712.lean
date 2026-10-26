import V185TrunkScan23Chunk0711

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4209749 : List Nat := [1, 3, 2, 2, 1, 2, 2, 4, 2, 2, 2]
def baseStart_4209749 : Nat := 118140960795 + 4209749 * 2 ^ 59
def prefixEnd_4209749 : Nat := 4983230072969 + 3 ^ 40 * 4209749 * 2
def baseEnd_4209749 : Nat := 2161624671784355071377223

theorem tailTrace_4209749 : CollatzResearch.WordTrace tailWord_4209749 prefixEnd_4209749 2161624671784355071377223 := by
  unfold tailWord_4209749
  simp only [CollatzResearch.WordTrace]
  refine ⟨153542160025805815734352301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102361440017203877156234867 153542160025805815734352301)
  ·
    refine ⟨57578310009677180900382113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153542160025805815734352301 57578310009677180900382113)
    ·
      refine ⟨43183732507257885675286585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57578310009677180900382113 43183732507257885675286585)
      ·
        refine ⟨32387799380443414256464939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43183732507257885675286585 32387799380443414256464939)
        ·
          refine ⟨48581699070665121384697409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32387799380443414256464939 48581699070665121384697409)
          ·
            refine ⟨36436274302998841038523057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48581699070665121384697409 36436274302998841038523057)
            ·
              refine ⟨27327205727249130778892293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36436274302998841038523057 27327205727249130778892293)
              ·
                refine ⟨5123851073859212021042305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27327205727249130778892293 5123851073859212021042305)
                ·
                  refine ⟨3842888305394409015781729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5123851073859212021042305 3842888305394409015781729)
                  ·
                    refine ⟨2882166229045806761836297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3842888305394409015781729 2882166229045806761836297)
                    ·
                      refine ⟨2161624671784355071377223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2882166229045806761836297 2161624671784355071377223)
                      ·
                        rfl

theorem cell23_4209749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_4209749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209749 prefixEnd_4209749 := by exact prefixLift 4209749
  have htrace : WordTrace (prefixWord ++ tailWord_4209749) baseStart_4209749 baseEnd_4209749 := by
    simpa [prefixWord, tailWord_4209749, baseEnd_4209749] using wordTrace_append hprefix tailTrace_4209749
  have hstable : (prefixWord ++ tailWord_4209749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209749).length < 2 ^ (prefixWord ++ tailWord_4209749).sum := by decide
  have hdescent : baseEnd_4209749 < baseStart_4209749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209765 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 1, 5, 3]
def baseStart_4209765 : Nat := 118140960795 + 4209765 * 2 ^ 59
def prefixEnd_4209765 : Nat := 4983230072969 + 3 ^ 40 * 4209765 * 2
def baseEnd_4209765 : Nat := 2161632887474827008777149

theorem tailTrace_4209765 : CollatzResearch.WordTrace tailWord_4209765 prefixEnd_4209765 2161632887474827008777149 := by
  unfold tailWord_4209765
  simp only [CollatzResearch.WordTrace]
  refine ⟨153542743593747850466934749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102361829062498566977956499 153542743593747850466934749)
  ·
    refine ⟨57578528847655443925100531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153542743593747850466934749 57578528847655443925100531)
    ·
      refine ⟨86367793271483165887650797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57578528847655443925100531 86367793271483165887650797)
      ·
        refine ⟨32387922476806187207869049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86367793271483165887650797 32387922476806187207869049)
        ·
          refine ⟨24290941857604640405901787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32387922476806187207869049 24290941857604640405901787)
          ·
            refine ⟨36436412786406960608852681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24290941857604640405901787 36436412786406960608852681)
            ·
              refine ⟨27327309589805220456639511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36436412786406960608852681 27327309589805220456639511)
              ·
                refine ⟨40990964384707830684959267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27327309589805220456639511 40990964384707830684959267)
                ·
                  refine ⟨61486446577061746027438901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40990964384707830684959267 61486446577061746027438901)
                  ·
                    refine ⟨5764354366599538690072397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61486446577061746027438901 5764354366599538690072397)
                    ·
                      refine ⟨2161632887474827008777149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5764354366599538690072397 2161632887474827008777149)
                      ·
                        rfl

theorem cell23_4209765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_4209765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209765 prefixEnd_4209765 := by exact prefixLift 4209765
  have htrace : WordTrace (prefixWord ++ tailWord_4209765) baseStart_4209765 baseEnd_4209765 := by
    simpa [prefixWord, tailWord_4209765, baseEnd_4209765] using wordTrace_append hprefix tailTrace_4209765
  have hstable : (prefixWord ++ tailWord_4209765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209765).length < 2 ^ (prefixWord ++ tailWord_4209765).sum := by decide
  have hdescent : baseEnd_4209765 < baseStart_4209765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209806 : List Nat := [4, 1, 1, 3, 2, 3, 2, 2, 5]
def baseStart_4209806 : Nat := 118140960795 + 4209806 * 2 ^ 59
def prefixEnd_4209806 : Nat := 4983230072969 + 3 ^ 40 * 4209806 * 2
def baseEnd_4209806 : Nat := 240183771131295705373829

theorem tailTrace_4209806 : CollatzResearch.WordTrace tailWord_4209806 prefixEnd_4209806 240183771131295705373829 := by
  unfold tailWord_4209806
  simp only [CollatzResearch.WordTrace]
  refine ⟨19193029873324914308647159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102362825991066209646118181 19193029873324914308647159)
  ·
    refine ⟨28789544809987371462970739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19193029873324914308647159 28789544809987371462970739)
    ·
      refine ⟨43184317214981057194456109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28789544809987371462970739 43184317214981057194456109)
      ·
        refine ⟨16194118955617896447921041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43184317214981057194456109 16194118955617896447921041)
        ·
          refine ⟨12145589216713422335940781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16194118955617896447921041 12145589216713422335940781)
          ·
            refine ⟨4554595956267533375977793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12145589216713422335940781 4554595956267533375977793)
            ·
              refine ⟨3415946967200650031983345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4554595956267533375977793 3415946967200650031983345)
              ·
                refine ⟨2561960225400487523987509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3415946967200650031983345 2561960225400487523987509)
                ·
                  refine ⟨240183771131295705373829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2561960225400487523987509 240183771131295705373829)
                  ·
                    rfl

theorem cell23_4209806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_4209806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209806 prefixEnd_4209806 := by exact prefixLift 4209806
  have htrace : WordTrace (prefixWord ++ tailWord_4209806) baseStart_4209806 baseEnd_4209806 := by
    simpa [prefixWord, tailWord_4209806, baseEnd_4209806] using wordTrace_append hprefix tailTrace_4209806
  have hstable : (prefixWord ++ tailWord_4209806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209806).length < 2 ^ (prefixWord ++ tailWord_4209806).sum := by decide
  have hdescent : baseEnd_4209806 < baseStart_4209806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209842 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3]
def baseStart_4209842 : Nat := 118140960795 + 4209842 * 2 ^ 59
def prefixEnd_4209842 : Nat := 4983230072969 + 3 ^ 40 * 4209842 * 2
def baseEnd_4209842 : Nat := 2161672425485223207514295

theorem tailTrace_4209842 : CollatzResearch.WordTrace tailWord_4209842 prefixEnd_4209842 2161672425485223207514295 := by
  unfold tailWord_4209842
  simp only [CollatzResearch.WordTrace]
  refine ⟨38386388003617223154371945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102363701342979261744991853 38386388003617223154371945)
  ·
    refine ⟨28789791002712917365778959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38386388003617223154371945 28789791002712917365778959)
    ·
      refine ⟨43184686504069376048668439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28789791002712917365778959 43184686504069376048668439)
      ·
        refine ⟨64777029756104064073002659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43184686504069376048668439 64777029756104064073002659)
        ·
          refine ⟨97165544634156096109503989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64777029756104064073002659 97165544634156096109503989)
          ·
            refine ⟨9109269809452134010265999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97165544634156096109503989 9109269809452134010265999)
            ·
              refine ⟨13663904714178201015398999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9109269809452134010265999 13663904714178201015398999)
              ·
                refine ⟨20495857071267301523098499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13663904714178201015398999 20495857071267301523098499)
                ·
                  refine ⟨30743785606900952284647749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20495857071267301523098499 30743785606900952284647749)
                  ·
                    refine ⟨5764459801293928553371453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30743785606900952284647749 5764459801293928553371453)
                    ·
                      refine ⟨2161672425485223207514295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5764459801293928553371453 2161672425485223207514295)
                      ·
                        rfl

theorem cell23_4209842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_4209842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209842 prefixEnd_4209842 := by exact prefixLift 4209842
  have htrace : WordTrace (prefixWord ++ tailWord_4209842) baseStart_4209842 baseEnd_4209842 := by
    simpa [prefixWord, tailWord_4209842, baseEnd_4209842] using wordTrace_append hprefix tailTrace_4209842
  have hstable : (prefixWord ++ tailWord_4209842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209842).length < 2 ^ (prefixWord ++ tailWord_4209842).sum := by decide
  have hdescent : baseEnd_4209842 < baseStart_4209842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209849 : List Nat := [1, 2, 1, 4, 1, 3, 1, 5, 1, 4]
def baseStart_4209849 : Nat := 118140960795 + 4209849 * 2 ^ 59
def prefixEnd_4209849 : Nat := 4983230072969 + 3 ^ 40 * 4209849 * 2
def baseEnd_4209849 : Nat := 720558673283268226708921

theorem tailTrace_4209849 : CollatzResearch.WordTrace tailWord_4209849 prefixEnd_4209849 720558673283268226708921 := by
  unfold tailWord_4209849
  simp only [CollatzResearch.WordTrace]
  refine ⟨153545807325443532812992601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102363871550295688541995067 153545807325443532812992601)
  ·
    refine ⟨115159355494082649609744451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153545807325443532812992601 115159355494082649609744451)
    ·
      refine ⟨172739033241123974414616677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115159355494082649609744451 172739033241123974414616677)
      ·
        refine ⟨32388568732710745202740627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172739033241123974414616677 32388568732710745202740627)
        ·
          refine ⟨48582853099066117804110941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32388568732710745202740627 48582853099066117804110941)
          ·
            refine ⟨18218569912149794176541603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48582853099066117804110941 18218569912149794176541603)
            ·
              refine ⟨27327854868224691264812405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18218569912149794176541603 27327854868224691264812405)
              ·
                refine ⟨2561986393896064806076163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27327854868224691264812405 2561986393896064806076163)
                ·
                  refine ⟨3842979590844097209114245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2561986393896064806076163 3842979590844097209114245)
                  ·
                    refine ⟨720558673283268226708921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3842979590844097209114245 720558673283268226708921)
                    ·
                      rfl

theorem cell23_4209849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 1, 4].length) (baseStart_4209849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209849 prefixEnd_4209849 := by exact prefixLift 4209849
  have htrace : WordTrace (prefixWord ++ tailWord_4209849) baseStart_4209849 baseEnd_4209849 := by
    simpa [prefixWord, tailWord_4209849, baseEnd_4209849] using wordTrace_append hprefix tailTrace_4209849
  have hstable : (prefixWord ++ tailWord_4209849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209849).length < 2 ^ (prefixWord ++ tailWord_4209849).sum := by decide
  have hdescent : baseEnd_4209849 < baseStart_4209849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209889 : List Nat := [1, 2, 3, 1, 3, 2, 2, 2, 3, 1, 3]
def baseStart_4209889 : Nat := 118140960795 + 4209889 * 2 ^ 59
def prefixEnd_4209889 : Nat := 4983230072969 + 3 ^ 40 * 4209889 * 2
def baseEnd_4209889 : Nat := 2161696559075984523626579

theorem tailTrace_4209889 : CollatzResearch.WordTrace tailWord_4209889 prefixEnd_4209889 2161696559075984523626579 := by
  unfold tailWord_4209889
  simp only [CollatzResearch.WordTrace]
  refine ⟨153547266245298619644448721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102364844163532413096299147 153547266245298619644448721)
  ·
    refine ⟨115160449683973964733336541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153547266245298619644448721 115160449683973964733336541)
    ·
      refine ⟨43185168631490236775001203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115160449683973964733336541 43185168631490236775001203)
      ·
        refine ⟨64777752947235355162501805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43185168631490236775001203 64777752947235355162501805)
        ·
          refine ⟨24291657355213258185938177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64777752947235355162501805 24291657355213258185938177)
          ·
            refine ⟨18218743016409943639453633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24291657355213258185938177 18218743016409943639453633)
            ·
              refine ⟨13664057262307457729590225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18218743016409943639453633 13664057262307457729590225)
              ·
                refine ⟨10248042946730593297192669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13664057262307457729590225 10248042946730593297192669)
                ·
                  refine ⟨3843016105023972486447251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10248042946730593297192669 3843016105023972486447251)
                  ·
                    refine ⟨5764524157535958729670877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3843016105023972486447251 5764524157535958729670877)
                    ·
                      refine ⟨2161696559075984523626579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5764524157535958729670877 2161696559075984523626579)
                      ·
                        rfl

theorem cell23_4209889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_4209889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209889 prefixEnd_4209889 := by exact prefixLift 4209889
  have htrace : WordTrace (prefixWord ++ tailWord_4209889) baseStart_4209889 baseEnd_4209889 := by
    simpa [prefixWord, tailWord_4209889, baseEnd_4209889] using wordTrace_append hprefix tailTrace_4209889
  have hstable : (prefixWord ++ tailWord_4209889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209889).length < 2 ^ (prefixWord ++ tailWord_4209889).sum := by decide
  have hdescent : baseEnd_4209889 < baseStart_4209889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209892 : List Nat := [2, 3, 1, 1, 1, 2, 3, 4, 1, 5]
def baseStart_4209892 : Nat := 118140960795 + 4209892 * 2 ^ 59
def prefixEnd_4209892 : Nat := 4983230072969 + 3 ^ 40 * 4209892 * 2
def baseEnd_4209892 : Nat := 720566033172649337296355

theorem tailTrace_4209892 : CollatzResearch.WordTrace tailWord_4209892 prefixEnd_4209892 720566033172649337296355 := by
  unfold tailWord_4209892
  simp only [CollatzResearch.WordTrace]
  refine ⟨76773687832143875578403965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102364917109525167437871953 76773687832143875578403965)
  ·
    refine ⟨28790132937053953341901487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76773687832143875578403965 28790132937053953341901487)
    ·
      refine ⟨43185199405580930012852231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28790132937053953341901487 43185199405580930012852231)
      ·
        refine ⟨64777799108371395019278347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43185199405580930012852231 64777799108371395019278347)
        ·
          refine ⟨97166698662557092528917521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64777799108371395019278347 97166698662557092528917521)
          ·
            refine ⟨72875023996917819396688141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97166698662557092528917521 72875023996917819396688141)
            ·
              refine ⟨27328133998844182273758053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72875023996917819396688141 27328133998844182273758053)
              ·
                refine ⟨5124025124783284176329635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27328133998844182273758053 5124025124783284176329635)
                ·
                  refine ⟨7686037687174926264494453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5124025124783284176329635 7686037687174926264494453)
                  ·
                    refine ⟨720566033172649337296355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7686037687174926264494453 720566033172649337296355)
                    ·
                      rfl

theorem cell23_4209892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_4209892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209892 prefixEnd_4209892 := by exact prefixLift 4209892
  have htrace : WordTrace (prefixWord ++ tailWord_4209892) baseStart_4209892 baseEnd_4209892 := by
    simpa [prefixWord, tailWord_4209892, baseEnd_4209892] using wordTrace_append hprefix tailTrace_4209892
  have hstable : (prefixWord ++ tailWord_4209892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209892).length < 2 ^ (prefixWord ++ tailWord_4209892).sum := by decide
  have hdescent : baseEnd_4209892 < baseStart_4209892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209905 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 3, 6]
def baseStart_4209905 : Nat := 118140960795 + 4209905 * 2 ^ 59
def prefixEnd_4209905 : Nat := 4983230072969 + 3 ^ 40 * 4209905 * 2
def baseEnd_4209905 : Nat := 720568258255485487008835

theorem tailTrace_4209905 : CollatzResearch.WordTrace tailWord_4209905 prefixEnd_4209905 720568258255485487008835 := by
  unfold tailWord_4209905
  simp only [CollatzResearch.WordTrace]
  refine ⟨153547849813240654377031169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102365233208827102918020779 153547849813240654377031169)
  ·
    refine ⟨115160887359930490782773377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153547849813240654377031169 115160887359930490782773377)
    ·
      refine ⟨86370665519947868087080033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115160887359930490782773377 86370665519947868087080033)
      ·
        refine ⟨64777999139960901065310025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86370665519947868087080033 64777999139960901065310025)
        ·
          refine ⟨48583499354970675798982519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64777999139960901065310025 48583499354970675798982519)
          ·
            refine ⟨72875249032456013698473779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48583499354970675798982519 72875249032456013698473779)
            ·
              refine ⟨109312873548684020547710669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72875249032456013698473779 109312873548684020547710669)
              ·
                refine ⟨40992327580756507705391501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109312873548684020547710669 40992327580756507705391501)
                ·
                  refine ⟨15372122842783690389521813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40992327580756507705391501 15372122842783690389521813)
                  ·
                    refine ⟨720568258255485487008835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15372122842783690389521813 720568258255485487008835)
                    ·
                      rfl

theorem cell23_4209905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_4209905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209905 prefixEnd_4209905 := by exact prefixLift 4209905
  have htrace : WordTrace (prefixWord ++ tailWord_4209905) baseStart_4209905 baseEnd_4209905 := by
    simpa [prefixWord, tailWord_4209905, baseEnd_4209905] using wordTrace_append hprefix tailTrace_4209905
  have hstable : (prefixWord ++ tailWord_4209905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209905).length < 2 ^ (prefixWord ++ tailWord_4209905).sum := by decide
  have hdescent : baseEnd_4209905 < baseStart_4209905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209916 : List Nat := [2, 2, 2, 1, 5, 1, 1, 2, 2, 3, 2]
def baseStart_4209916 : Nat := 118140960795 + 4209916 * 2 ^ 59
def prefixEnd_4209916 : Nat := 4983230072969 + 3 ^ 40 * 4209916 * 2
def baseEnd_4209916 : Nat := 2161710423053655917988955

theorem tailTrace_4209916 : CollatzResearch.WordTrace tailWord_4209916 prefixEnd_4209916 2161710423053655917988955 := by
  unfold tailWord_4209916
  simp only [CollatzResearch.WordTrace]
  refine ⟨76774125508100401627840801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102365500677467202170454401 76774125508100401627840801)
  ·
    refine ⟨57580594131075301220880601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76774125508100401627840801 57580594131075301220880601)
    ·
      refine ⟨43185445598306475915660451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57580594131075301220880601 43185445598306475915660451)
      ·
        refine ⟨64778168397459713873490677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43185445598306475915660451 64778168397459713873490677)
        ·
          refine ⟨6072953287261848175639751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64778168397459713873490677 6072953287261848175639751)
          ·
            refine ⟨9109429930892772263459627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6072953287261848175639751 9109429930892772263459627)
            ·
              refine ⟨13664144896339158395189441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9109429930892772263459627 13664144896339158395189441)
              ·
                refine ⟨10248108672254368796392081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13664144896339158395189441 10248108672254368796392081)
                ·
                  refine ⟨7686081504190776597294061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10248108672254368796392081 7686081504190776597294061)
                  ·
                    refine ⟨2882280564071541223985273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7686081504190776597294061 2882280564071541223985273)
                    ·
                      refine ⟨2161710423053655917988955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2882280564071541223985273 2161710423053655917988955)
                      ·
                        rfl

theorem cell23_4209916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_4209916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209916 prefixEnd_4209916 := by exact prefixLift 4209916
  have htrace : WordTrace (prefixWord ++ tailWord_4209916) baseStart_4209916 baseEnd_4209916 := by
    simpa [prefixWord, tailWord_4209916, baseEnd_4209916] using wordTrace_append hprefix tailTrace_4209916
  have hstable : (prefixWord ++ tailWord_4209916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209916).length < 2 ^ (prefixWord ++ tailWord_4209916).sum := by decide
  have hdescent : baseEnd_4209916 < baseStart_4209916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209923 : List Nat := [1, 1, 1, 3, 2, 5, 3, 2, 1, 1, 3]
def baseStart_4209923 : Nat := 118140960795 + 4209923 * 2 ^ 59
def prefixEnd_4209923 : Nat := 4983230072969 + 3 ^ 40 * 4209923 * 2
def baseEnd_4209923 : Nat := 2161714017418237390601423

theorem tailTrace_4209923 : CollatzResearch.WordTrace tailWord_4209923 prefixEnd_4209923 2161714017418237390601423 := by
  unfold tailWord_4209923
  simp only [CollatzResearch.WordTrace]
  refine ⟨153548506327175443451186423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102365670884783628967457615 153548506327175443451186423)
  ·
    refine ⟨230322759490763165176779635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153548506327175443451186423 230322759490763165176779635)
    ·
      refine ⟨345484139236144747765169453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230322759490763165176779635 345484139236144747765169453)
      ·
        refine ⟨129556552213554280411938545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 345484139236144747765169453 129556552213554280411938545)
        ·
          refine ⟨97167414160165710308953909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129556552213554280411938545 97167414160165710308953909)
          ·
            refine ⟨9109445077515535341464429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97167414160165710308953909 9109445077515535341464429)
            ·
              refine ⟨3416041904068325753049161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9109445077515535341464429 3416041904068325753049161)
              ·
                refine ⟨2562031428051244314786871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3416041904068325753049161 2562031428051244314786871)
                ·
                  refine ⟨3843047142076866472180307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562031428051244314786871 3843047142076866472180307)
                  ·
                    refine ⟨5764570713115299708270461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3843047142076866472180307 5764570713115299708270461)
                    ·
                      refine ⟨2161714017418237390601423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5764570713115299708270461 2161714017418237390601423)
                      ·
                        rfl

theorem cell23_4209923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 1, 1, 3].length) (baseStart_4209923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209923 prefixEnd_4209923 := by exact prefixLift 4209923
  have htrace : WordTrace (prefixWord ++ tailWord_4209923) baseStart_4209923 baseEnd_4209923 := by
    simpa [prefixWord, tailWord_4209923, baseEnd_4209923] using wordTrace_append hprefix tailTrace_4209923
  have hstable : (prefixWord ++ tailWord_4209923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209923).length < 2 ^ (prefixWord ++ tailWord_4209923).sum := by decide
  have hdescent : baseEnd_4209923 < baseStart_4209923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209925 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 3, 1, 6]
def baseStart_4209925 : Nat := 118140960795 + 4209925 * 2 ^ 59
def prefixEnd_4209925 : Nat := 4983230072969 + 3 ^ 40 * 4209925 * 2
def baseEnd_4209925 : Nat := 2161715044379546382776413

theorem tailTrace_4209925 : CollatzResearch.WordTrace tailWord_4209925 prefixEnd_4209925 2161715044379546382776413 := by
  unfold tailWord_4209925
  simp only [CollatzResearch.WordTrace]
  refine ⟨153548579273168197792759229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102365719515445465195172819 153548579273168197792759229)
  ·
    refine ⟨57580717227438074172284711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153548579273168197792759229 57580717227438074172284711)
    ·
      refine ⟨86371075841157111258427067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57580717227438074172284711 86371075841157111258427067)
      ·
        refine ⟨129556613761735666887640601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86371075841157111258427067 129556613761735666887640601)
        ·
          refine ⟨97167460321301750165730451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129556613761735666887640601 97167460321301750165730451)
          ·
            refine ⟨145751190481952625248595677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97167460321301750165730451 145751190481952625248595677)
            ·
              refine ⟨54656696430732234468223379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145751190481952625248595677 54656696430732234468223379)
              ·
                refine ⟨81985044646098351702335069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54656696430732234468223379 81985044646098351702335069)
                ·
                  refine ⟨30744391742286881888375651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81985044646098351702335069 30744391742286881888375651)
                  ·
                    refine ⟨46116587613430322832563477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30744391742286881888375651 46116587613430322832563477)
                    ·
                      refine ⟨2161715044379546382776413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46116587613430322832563477 2161715044379546382776413)
                      ·
                        rfl

theorem cell23_4209925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_4209925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209925 prefixEnd_4209925 := by exact prefixLift 4209925
  have htrace : WordTrace (prefixWord ++ tailWord_4209925) baseStart_4209925 baseEnd_4209925 := by
    simpa [prefixWord, tailWord_4209925, baseEnd_4209925] using wordTrace_append hprefix tailTrace_4209925
  have hstable : (prefixWord ++ tailWord_4209925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209925).length < 2 ^ (prefixWord ++ tailWord_4209925).sum := by decide
  have hdescent : baseEnd_4209925 < baseStart_4209925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209932 : List Nat := [2, 2, 1, 2, 2, 3, 2, 2, 1, 1, 5]
def baseStart_4209932 : Nat := 118140960795 + 4209932 * 2 ^ 59
def prefixEnd_4209932 : Nat := 4983230072969 + 3 ^ 40 * 4209932 * 2
def baseEnd_4209932 : Nat := 2161718638744127855388881

theorem tailTrace_4209932 : CollatzResearch.WordTrace tailWord_4209932 prefixEnd_4209932 2161718638744127855388881 := by
  unfold tailWord_4209932
  simp only [CollatzResearch.WordTrace]
  refine ⟨76774417292071418994132025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102365889722761891992176033 76774417292071418994132025)
  ·
    refine ⟨57580812969053564245599019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76774417292071418994132025 57580812969053564245599019)
    ·
      refine ⟨86371219453580346368398529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57580812969053564245599019 86371219453580346368398529)
      ·
        refine ⟨64778414590185259776298897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86371219453580346368398529 64778414590185259776298897)
        ·
          refine ⟨48583810942638944832224173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64778414590185259776298897 48583810942638944832224173)
          ·
            refine ⟨18218929103489604312084065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48583810942638944832224173 18218929103489604312084065)
            ·
              refine ⟨13664196827617203234063049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18218929103489604312084065 13664196827617203234063049)
              ·
                refine ⟨10248147620712902425547287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13664196827617203234063049 10248147620712902425547287)
                ·
                  refine ⟨15372221431069353638320931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10248147620712902425547287 15372221431069353638320931)
                  ·
                    refine ⟨23058332146604030457481397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15372221431069353638320931 23058332146604030457481397)
                    ·
                      refine ⟨2161718638744127855388881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23058332146604030457481397 2161718638744127855388881)
                      ·
                        rfl

theorem cell23_4209932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_4209932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209932 prefixEnd_4209932 := by exact prefixLift 4209932
  have htrace : WordTrace (prefixWord ++ tailWord_4209932) baseStart_4209932 baseEnd_4209932 := by
    simpa [prefixWord, tailWord_4209932, baseEnd_4209932] using wordTrace_append hprefix tailTrace_4209932
  have hstable : (prefixWord ++ tailWord_4209932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209932).length < 2 ^ (prefixWord ++ tailWord_4209932).sum := by decide
  have hdescent : baseEnd_4209932 < baseStart_4209932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209946 : List Nat := [3, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4]
def baseStart_4209946 : Nat := 118140960795 + 4209946 * 2 ^ 59
def prefixEnd_4209946 : Nat := 4983230072969 + 3 ^ 40 * 4209946 * 2
def baseEnd_4209946 : Nat := 2161725827473290800613817

theorem tailTrace_4209946 : CollatzResearch.WordTrace tailWord_4209946 prefixEnd_4209946 2161725827473290800613817 := by
  unfold tailWord_4209946
  simp only [CollatzResearch.WordTrace]
  refine ⟨38387336301523029594818423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102366230137394745586182461 38387336301523029594818423)
  ·
    refine ⟨57581004452284544392227635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38387336301523029594818423 57581004452284544392227635)
    ·
      refine ⟨86371506678426816588341453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57581004452284544392227635 86371506678426816588341453)
      ·
        refine ⟨32389315004410056220628045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86371506678426816588341453 32389315004410056220628045)
        ·
          refine ⟨12145993126653771082735517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32389315004410056220628045 12145993126653771082735517)
          ·
            refine ⟨4554747422495164156025819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12145993126653771082735517 4554747422495164156025819)
            ·
              refine ⟨6832121133742746234038729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4554747422495164156025819 6832121133742746234038729)
              ·
                refine ⟨5124090850307059675529047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6832121133742746234038729 5124090850307059675529047)
                ·
                  refine ⟨7686136275460589513293571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5124090850307059675529047 7686136275460589513293571)
                  ·
                    refine ⟨11529204413190884269940357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7686136275460589513293571 11529204413190884269940357)
                    ·
                      refine ⟨2161725827473290800613817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11529204413190884269940357 2161725827473290800613817)
                      ·
                        rfl

theorem cell23_4209946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_4209946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209946 prefixEnd_4209946 := by exact prefixLift 4209946
  have htrace : WordTrace (prefixWord ++ tailWord_4209946) baseStart_4209946 baseEnd_4209946 := by
    simpa [prefixWord, tailWord_4209946, baseEnd_4209946] using wordTrace_append hprefix tailTrace_4209946
  have hstable : (prefixWord ++ tailWord_4209946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209946).length < 2 ^ (prefixWord ++ tailWord_4209946).sum := by decide
  have hdescent : baseEnd_4209946 < baseStart_4209946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209950 : List Nat := [4, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_4209950 : Nat := 118140960795 + 4209950 * 2 ^ 59
def prefixEnd_4209950 : Nat := 4983230072969 + 3 ^ 40 * 4209950 * 2
def baseEnd_4209950 : Nat := 2161727881395908784963799

theorem tailTrace_4209950 : CollatzResearch.WordTrace tailWord_4209950 prefixEnd_4209950 2161727881395908784963799 := by
  unfold tailWord_4209950
  simp only [CollatzResearch.WordTrace]
  refine ⟨19193686387259703382802413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102366327398718418041612869 19193686387259703382802413)
  ·
    refine ⟨7197632395222388768550905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19193686387259703382802413 7197632395222388768550905)
    ·
      refine ⟨5398224296416791576413179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7197632395222388768550905 5398224296416791576413179)
      ·
        refine ⟨8097336444625187364619769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5398224296416791576413179 8097336444625187364619769)
        ·
          refine ⟨6073002333468890523464827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8097336444625187364619769 6073002333468890523464827)
          ·
            refine ⟨9109503500203335785197241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6073002333468890523464827 9109503500203335785197241)
            ·
              refine ⟨6832127625152501838897931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9109503500203335785197241 6832127625152501838897931)
              ·
                refine ⟨10248191437728752758346897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6832127625152501838897931 10248191437728752758346897)
                ·
                  refine ⟨7686143578296564568760173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10248191437728752758346897 7686143578296564568760173)
                  ·
                    refine ⟨2882303841861211713285065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7686143578296564568760173 2882303841861211713285065)
                    ·
                      refine ⟨2161727881395908784963799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2882303841861211713285065 2161727881395908784963799)
                      ·
                        rfl

theorem cell23_4209950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_4209950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209950 prefixEnd_4209950 := by exact prefixLift 4209950
  have htrace : WordTrace (prefixWord ++ tailWord_4209950) baseStart_4209950 baseEnd_4209950 := by
    simpa [prefixWord, tailWord_4209950, baseEnd_4209950] using wordTrace_append hprefix tailTrace_4209950
  have hstable : (prefixWord ++ tailWord_4209950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209950).length < 2 ^ (prefixWord ++ tailWord_4209950).sum := by decide
  have hdescent : baseEnd_4209950 < baseStart_4209950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209974 : List Nat := [5, 1, 2, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_4209974 : Nat := 118140960795 + 4209974 * 2 ^ 59
def prefixEnd_4209974 : Nat := 4983230072969 + 3 ^ 40 * 4209974 * 2
def baseEnd_4209974 : Nat := 2161740204931616691063689

theorem tailTrace_4209974 : CollatzResearch.WordTrace tailWord_4209974 prefixEnd_4209974 2161740204931616691063689 := by
  unfold tailWord_4209974
  simp only [CollatzResearch.WordTrace]
  refine ⟨9596897903124417447580811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102366910966660452774195317 9596897903124417447580811)
  ·
    refine ⟨14395346854686626171371217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9596897903124417447580811 14395346854686626171371217)
    ·
      refine ⟨10796510141014969628528413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14395346854686626171371217 10796510141014969628528413)
      ·
        refine ⟨4048691302880613610698155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10796510141014969628528413 4048691302880613610698155)
        ·
          refine ⟨6073036954320920416047233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4048691302880613610698155 6073036954320920416047233)
          ·
            refine ⟨4554777715740690312035425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6073036954320920416047233 4554777715740690312035425)
            ·
              refine ⟨3416083286805517734026569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4554777715740690312035425 3416083286805517734026569)
              ·
                refine ⟨2562062465104138300519927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3416083286805517734026569 2562062465104138300519927)
                ·
                  refine ⟨3843093697656207450779891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562062465104138300519927 3843093697656207450779891)
                  ·
                    refine ⟨5764640546484311176169837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3843093697656207450779891 5764640546484311176169837)
                    ·
                      refine ⟨2161740204931616691063689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5764640546484311176169837 2161740204931616691063689)
                      ·
                        rfl

theorem cell23_4209974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_4209974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209974 prefixEnd_4209974 := by exact prefixLift 4209974
  have htrace : WordTrace (prefixWord ++ tailWord_4209974) baseStart_4209974 baseEnd_4209974 := by
    simpa [prefixWord, tailWord_4209974, baseEnd_4209974] using wordTrace_append hprefix tailTrace_4209974
  have hstable : (prefixWord ++ tailWord_4209974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209974).length < 2 ^ (prefixWord ++ tailWord_4209974).sum := by decide
  have hdescent : baseEnd_4209974 < baseStart_4209974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209975 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 7]
def baseStart_4209975 : Nat := 118140960795 + 4209975 * 2 ^ 59
def prefixEnd_4209975 : Nat := 4983230072969 + 3 ^ 40 * 4209975 * 2
def baseEnd_4209975 : Nat := 2161740718412271187151183

theorem tailTrace_4209975 : CollatzResearch.WordTrace tailWord_4209975 prefixEnd_4209975 2161740718412271187151183 := by
  unfold tailWord_4209975
  simp only [CollatzResearch.WordTrace]
  refine ⟨153550402922987056332079379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102366935281991370888052919 153550402922987056332079379)
  ·
    refine ⟨230325604384480584498119069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153550402922987056332079379 230325604384480584498119069)
    ·
      refine ⟨86372101644180219186794651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230325604384480584498119069 86372101644180219186794651)
      ·
        refine ⟨129558152466270328780191977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86372101644180219186794651 129558152466270328780191977)
        ·
          refine ⟨97168614349702746585143983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129558152466270328780191977 97168614349702746585143983)
          ·
            refine ⟨145752921524554119877715975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97168614349702746585143983 145752921524554119877715975)
            ·
              refine ⟨218629382286831179816573963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145752921524554119877715975 218629382286831179816573963)
              ·
                refine ⟨327944073430246769724860945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218629382286831179816573963 327944073430246769724860945)
                ·
                  refine ⟨245958055072685077293645709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 327944073430246769724860945 245958055072685077293645709)
                  ·
                    refine ⟨92234270652256903985117141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 245958055072685077293645709 92234270652256903985117141)
                    ·
                      refine ⟨2161740718412271187151183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92234270652256903985117141 2161740718412271187151183)
                      ·
                        rfl

theorem cell23_4209975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_4209975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209975 prefixEnd_4209975 := by exact prefixLift 4209975
  have htrace : WordTrace (prefixWord ++ tailWord_4209975) baseStart_4209975 baseEnd_4209975 := by
    simpa [prefixWord, tailWord_4209975, baseEnd_4209975] using wordTrace_append hprefix tailTrace_4209975
  have hstable : (prefixWord ++ tailWord_4209975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209975).length < 2 ^ (prefixWord ++ tailWord_4209975).sum := by decide
  have hdescent : baseEnd_4209975 < baseStart_4209975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209980 : List Nat := [2, 2, 2, 2, 1, 3, 4, 2, 1, 2, 2]
def baseStart_4209980 : Nat := 118140960795 + 4209980 * 2 ^ 59
def prefixEnd_4209980 : Nat := 4983230072969 + 3 ^ 40 * 4209980 * 2
def baseEnd_4209980 : Nat := 2161743285815543667588661

theorem tailTrace_4209980 : CollatzResearch.WordTrace tailWord_4209980 prefixEnd_4209980 2161743285815543667588661 := by
  unfold tailWord_4209980
  simp only [CollatzResearch.WordTrace]
  refine ⟨76775292643984471093005697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102367056858645961457340929 76775292643984471093005697)
  ·
    refine ⟨57581469482988353319754273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76775292643984471093005697 57581469482988353319754273)
    ·
      refine ⟨43186102112241264989815705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57581469482988353319754273 43186102112241264989815705)
      ·
        refine ⟨32389576584180948742361779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43186102112241264989815705 32389576584180948742361779)
        ·
          refine ⟨48584364876271423113542669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32389576584180948742361779 48584364876271423113542669)
          ·
            refine ⟨18219136828601783667578501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48584364876271423113542669 18219136828601783667578501)
            ·
              refine ⟨3416088155362834437670969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18219136828601783667578501 3416088155362834437670969)
              ·
                refine ⟨2562066116522125828253227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3416088155362834437670969 2562066116522125828253227)
                ·
                  refine ⟨3843099174783188742379841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562066116522125828253227 3843099174783188742379841)
                  ·
                    refine ⟨2882324381087391556784881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3843099174783188742379841 2882324381087391556784881)
                    ·
                      refine ⟨2161743285815543667588661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2882324381087391556784881 2161743285815543667588661)
                      ·
                        rfl

theorem cell23_4209980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_4209980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209980 prefixEnd_4209980 := by exact prefixLift 4209980
  have htrace : WordTrace (prefixWord ++ tailWord_4209980) baseStart_4209980 baseEnd_4209980 := by
    simpa [prefixWord, tailWord_4209980, baseEnd_4209980] using wordTrace_append hprefix tailTrace_4209980
  have hstable : (prefixWord ++ tailWord_4209980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209980).length < 2 ^ (prefixWord ++ tailWord_4209980).sum := by decide
  have hdescent : baseEnd_4209980 < baseStart_4209980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209982 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_4209982 : Nat := 118140960795 + 4209982 * 2 ^ 59
def prefixEnd_4209982 : Nat := 4983230072969 + 3 ^ 40 * 4209982 * 2
def baseEnd_4209982 : Nat := 720581437592284219921217

theorem tailTrace_4209982 : CollatzResearch.WordTrace tailWord_4209982 prefixEnd_4209982 720581437592284219921217 := by
  unfold tailWord_4209982
  simp only [CollatzResearch.WordTrace]
  refine ⟨19193832279245212065948025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102367105489307797685056133 19193832279245212065948025)
  ·
    refine ⟨14395374209433909049461019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19193832279245212065948025 14395374209433909049461019)
    ·
      refine ⟨21593061314150863574191529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14395374209433909049461019 21593061314150863574191529)
      ·
        refine ⟨16194795985613147680643647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21593061314150863574191529 16194795985613147680643647)
        ·
          refine ⟨24292193978419721520965471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16194795985613147680643647 24292193978419721520965471)
          ·
            refine ⟨36438290967629582281448207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24292193978419721520965471 36438290967629582281448207)
            ·
              refine ⟨54657436451444373422172311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36438290967629582281448207 54657436451444373422172311)
              ·
                refine ⟨81986154677166560133258467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54657436451444373422172311 81986154677166560133258467)
                ·
                  refine ⟨122979232015749840199887701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81986154677166560133258467 122979232015749840199887701)
                  ·
                    refine ⟨720581437592284219921217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 122979232015749840199887701 720581437592284219921217)
                    ·
                      rfl

theorem cell23_4209982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_4209982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209982 prefixEnd_4209982 := by exact prefixLift 4209982
  have htrace : WordTrace (prefixWord ++ tailWord_4209982) baseStart_4209982 baseEnd_4209982 := by
    simpa [prefixWord, tailWord_4209982, baseEnd_4209982] using wordTrace_append hprefix tailTrace_4209982
  have hstable : (prefixWord ++ tailWord_4209982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209982).length < 2 ^ (prefixWord ++ tailWord_4209982).sum := by decide
  have hdescent : baseEnd_4209982 < baseStart_4209982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4209996 : List Nat := [2, 2, 1, 3, 2, 2, 2, 3, 2, 1, 3]
def baseStart_4209996 : Nat := 118140960795 + 4209996 * 2 ^ 59
def prefixEnd_4209996 : Nat := 4983230072969 + 3 ^ 40 * 4209996 * 2
def baseEnd_4209996 : Nat := 2161751501506015604988587

theorem tailTrace_4209996 : CollatzResearch.WordTrace tailWord_4209996 prefixEnd_4209996 2161751501506015604988587 := by
  unfold tailWord_4209996
  simp only [CollatzResearch.WordTrace]
  refine ⟨76775584427955488459296921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102367445903940651279062561 76775584427955488459296921)
  ·
    refine ⟨57581688320966616344472691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76775584427955488459296921 57581688320966616344472691)
    ·
      refine ⟨86372532481449924516709037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57581688320966616344472691 86372532481449924516709037)
      ·
        refine ⟨32389699680543721693765889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86372532481449924516709037 32389699680543721693765889)
        ·
          refine ⟨24292274760407791270324417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32389699680543721693765889 24292274760407791270324417)
          ·
            refine ⟨18219206070305843452743313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24292274760407791270324417 18219206070305843452743313)
            ·
              refine ⟨13664404552729382589557485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18219206070305843452743313 13664404552729382589557485)
              ·
                refine ⟨5124151707273518471084057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13664404552729382589557485 5124151707273518471084057)
                ·
                  refine ⟨3843113780455138853313043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5124151707273518471084057 3843113780455138853313043)
                  ·
                    refine ⟨5764670670682708279969565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3843113780455138853313043 5764670670682708279969565)
                    ·
                      refine ⟨2161751501506015604988587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5764670670682708279969565 2161751501506015604988587)
                      ·
                        rfl

theorem cell23_4209996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_4209996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4209996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4209996 prefixEnd_4209996 := by exact prefixLift 4209996
  have htrace : WordTrace (prefixWord ++ tailWord_4209996) baseStart_4209996 baseEnd_4209996 := by
    simpa [prefixWord, tailWord_4209996, baseEnd_4209996] using wordTrace_append hprefix tailTrace_4209996
  have hstable : (prefixWord ++ tailWord_4209996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4209996).length < 2 ^ (prefixWord ++ tailWord_4209996).sum := by decide
  have hdescent : baseEnd_4209996 < baseStart_4209996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4209996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210002 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_4210002 : Nat := 118140960795 + 4210002 * 2 ^ 59
def prefixEnd_4210002 : Nat := 4983230072969 + 3 ^ 40 * 4210002 * 2
def baseEnd_4210002 : Nat := 2161754582389942581513559

theorem tailTrace_4210002 : CollatzResearch.WordTrace tailWord_4210002 prefixEnd_4210002 2161754582389942581513559 := by
  unfold tailWord_4210002
  simp only [CollatzResearch.WordTrace]
  refine ⟨38387846923472309985828065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102367591795926159962208173 38387846923472309985828065)
  ·
    refine ⟨28790885192604232489371049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38387846923472309985828065 28790885192604232489371049)
    ·
      refine ⟨21593163894453174367028287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28790885192604232489371049 21593163894453174367028287)
      ·
        refine ⟨32389745841679761550542431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21593163894453174367028287 32389745841679761550542431)
        ·
          refine ⟨48584618762519642325813647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32389745841679761550542431 48584618762519642325813647)
          ·
            refine ⟨72876928143779463488720471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48584618762519642325813647 72876928143779463488720471)
            ·
              refine ⟨109315392215669195233080707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72876928143779463488720471 109315392215669195233080707)
              ·
                refine ⟨163973088323503792849621061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109315392215669195233080707 163973088323503792849621061)
                ·
                  refine ⟨30744954060656961159303949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163973088323503792849621061 30744954060656961159303949)
                  ·
                    refine ⟨11529357772746360434738981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30744954060656961159303949 11529357772746360434738981)
                    ·
                      refine ⟨2161754582389942581513559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11529357772746360434738981 2161754582389942581513559)
                      ·
                        rfl

theorem cell23_4210002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_4210002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210002 prefixEnd_4210002 := by exact prefixLift 4210002
  have htrace : WordTrace (prefixWord ++ tailWord_4210002) baseStart_4210002 baseEnd_4210002 := by
    simpa [prefixWord, tailWord_4210002, baseEnd_4210002] using wordTrace_append hprefix tailTrace_4210002
  have hstable : (prefixWord ++ tailWord_4210002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210002).length < 2 ^ (prefixWord ++ tailWord_4210002).sum := by decide
  have hdescent : baseEnd_4210002 < baseStart_4210002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210023 : List Nat := [1, 1, 5, 1, 4, 1, 1, 3, 1, 3, 2]
def baseStart_4210023 : Nat := 118140960795 + 4210023 * 2 ^ 59
def prefixEnd_4210023 : Nat := 4983230072969 + 3 ^ 40 * 4210023 * 2
def baseEnd_4210023 : Nat := 2161765365483686999350963

theorem tailTrace_4210023 : CollatzResearch.WordTrace tailWord_4210023 prefixEnd_4210023 2161765365483686999350963 := by
  unfold tailWord_4210023
  simp only [CollatzResearch.WordTrace]
  refine ⟨153552153626813160529826723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102368102417875440353217815 153552153626813160529826723)
  ·
    refine ⟨230328230440219740794740085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153552153626813160529826723 230328230440219740794740085)
    ·
      refine ⟨21593271603770600699506883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 230328230440219740794740085 21593271603770600699506883)
      ·
        refine ⟨32389907405655901049260325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21593271603770600699506883 32389907405655901049260325)
        ·
          refine ⟨6073107638560481446736311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32389907405655901049260325 6073107638560481446736311)
          ·
            refine ⟨9109661457840722170104467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6073107638560481446736311 9109661457840722170104467)
            ·
              refine ⟨13664492186761083255156701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9109661457840722170104467 13664492186761083255156701)
              ·
                refine ⟨5124184570035406220683763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13664492186761083255156701 5124184570035406220683763)
                ·
                  refine ⟨7686276855053109331025645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5124184570035406220683763 7686276855053109331025645)
                  ·
                    refine ⟨2882353820644915999134617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7686276855053109331025645 2882353820644915999134617)
                    ·
                      refine ⟨2161765365483686999350963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2882353820644915999134617 2161765365483686999350963)
                      ·
                        rfl

theorem cell23_4210023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_4210023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210023 prefixEnd_4210023 := by exact prefixLift 4210023
  have htrace : WordTrace (prefixWord ++ tailWord_4210023) baseStart_4210023 baseEnd_4210023 := by
    simpa [prefixWord, tailWord_4210023, baseEnd_4210023] using wordTrace_append hprefix tailTrace_4210023
  have hstable : (prefixWord ++ tailWord_4210023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210023).length < 2 ^ (prefixWord ++ tailWord_4210023).sum := by decide
  have hdescent : baseEnd_4210023 < baseStart_4210023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210032 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 4]
def baseStart_4210032 : Nat := 118140960795 + 4210032 * 2 ^ 59
def prefixEnd_4210032 : Nat := 4983230072969 + 3 ^ 40 * 4210032 * 2
def baseEnd_4210032 : Nat := 2161769986809577464138421

theorem tailTrace_4210032 : CollatzResearch.WordTrace tailWord_4210032 prefixEnd_4210032 2161769986809577464138421 := by
  unfold tailWord_4210032
  simp only [CollatzResearch.WordTrace]
  refine ⟨76776240941890277533452175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102368321255853703377936233 76776240941890277533452175)
  ·
    refine ⟨115164361412835416300178263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76776240941890277533452175 115164361412835416300178263)
    ·
      refine ⟨172746542119253124450267395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115164361412835416300178263 172746542119253124450267395)
      ·
        refine ⟨259119813178879686675401093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172746542119253124450267395 259119813178879686675401093)
        ·
          refine ⟨48584964971039941251637705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 259119813178879686675401093 48584964971039941251637705)
          ·
            refine ⟨36438723728279955938728279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48584964971039941251637705 36438723728279955938728279)
            ·
              refine ⟨54658085592419933908092419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36438723728279955938728279 54658085592419933908092419)
              ·
                refine ⟨81987128388629900862138629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54658085592419933908092419 81987128388629900862138629)
                ·
                  refine ⟨15372586572868106411650993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81987128388629900862138629 15372586572868106411650993)
                  ·
                    refine ⟨11529439929651079808738245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15372586572868106411650993 11529439929651079808738245)
                    ·
                      refine ⟨2161769986809577464138421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11529439929651079808738245 2161769986809577464138421)
                      ·
                        rfl

theorem cell23_4210032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 4].length) (baseStart_4210032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210032 prefixEnd_4210032 := by exact prefixLift 4210032
  have htrace : WordTrace (prefixWord ++ tailWord_4210032) baseStart_4210032 baseEnd_4210032 := by
    simpa [prefixWord, tailWord_4210032, baseEnd_4210032] using wordTrace_append hprefix tailTrace_4210032
  have hstable : (prefixWord ++ tailWord_4210032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210032).length < 2 ^ (prefixWord ++ tailWord_4210032).sum := by decide
  have hdescent : baseEnd_4210032 < baseStart_4210032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210109 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 4, 1, 4]
def baseStart_4210109 : Nat := 118140960795 + 4210109 * 2 ^ 59
def prefixEnd_4210109 : Nat := 4983230072969 + 3 ^ 40 * 4210109 * 2
def baseEnd_4210109 : Nat := 2161809524819973662875567

theorem tailTrace_4210109 : CollatzResearch.WordTrace tailWord_4210109 prefixEnd_4210109 2161809524819973662875567 := by
  unfold tailWord_4210109
  simp only [CollatzResearch.WordTrace]
  refine ⟨153555290304501597217457381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102370193536334398144971587 153555290304501597217457381)
  ·
    refine ⟨28791616932094049478273259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153555290304501597217457381 28791616932094049478273259)
    ·
      refine ⟨43187425398141074217409889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28791616932094049478273259 43187425398141074217409889)
      ·
        refine ⟨32390569048605805663057417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43187425398141074217409889 32390569048605805663057417)
        ·
          refine ⟨24292926786454354247293063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32390569048605805663057417 24292926786454354247293063)
          ·
            refine ⟨36439390179681531370939595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24292926786454354247293063 36439390179681531370939595)
            ·
              refine ⟨54659085269522297056409393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36439390179681531370939595 54659085269522297056409393)
              ·
                refine ⟨40994313952141722792307045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54659085269522297056409393 40994313952141722792307045)
                ·
                  refine ⟨7686433866026573023557571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40994313952141722792307045 7686433866026573023557571)
                  ·
                    refine ⟨11529650799039859535336357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7686433866026573023557571 11529650799039859535336357)
                    ·
                      refine ⟨2161809524819973662875567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11529650799039859535336357 2161809524819973662875567)
                      ·
                        rfl

theorem cell23_4210109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_4210109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210109 prefixEnd_4210109 := by exact prefixLift 4210109
  have htrace : WordTrace (prefixWord ++ tailWord_4210109) baseStart_4210109 baseEnd_4210109 := by
    simpa [prefixWord, tailWord_4210109, baseEnd_4210109] using wordTrace_append hprefix tailTrace_4210109
  have hstable : (prefixWord ++ tailWord_4210109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210109).length < 2 ^ (prefixWord ++ tailWord_4210109).sum := by decide
  have hdescent : baseEnd_4210109 < baseStart_4210109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210119 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 5, 4]
def baseStart_4210119 : Nat := 118140960795 + 4210119 * 2 ^ 59
def prefixEnd_4210119 : Nat := 4983230072969 + 3 ^ 40 * 4210119 * 2
def baseEnd_4210119 : Nat := 720604886542172874583507

theorem tailTrace_4210119 : CollatzResearch.WordTrace tailWord_4210119 prefixEnd_4210119 720604886542172874583507 := by
  unfold tailWord_4210119
  simp only [CollatzResearch.WordTrace]
  refine ⟨153555655034465368925321411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102370436689643579283547607 153555655034465368925321411)
  ·
    refine ⟨230333482551698053387982117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153555655034465368925321411 230333482551698053387982117)
    ·
      refine ⟨43187527978443385010246647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230333482551698053387982117 43187527978443385010246647)
      ·
        refine ⟨64781291967665077515369971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43187527978443385010246647 64781291967665077515369971)
        ·
          refine ⟨97171937951497616273054957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64781291967665077515369971 97171937951497616273054957)
          ·
            refine ⟨36439476731811606102395609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97171937951497616273054957 36439476731811606102395609)
            ·
              refine ⟨27329607548858704576796707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36439476731811606102395609 27329607548858704576796707)
              ·
                refine ⟨40994411323288056865195061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27329607548858704576796707 40994411323288056865195061)
                ·
                  refine ⟨3843226061558255331112037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40994411323288056865195061 3843226061558255331112037)
                  ·
                    refine ⟨720604886542172874583507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3843226061558255331112037 720604886542172874583507)
                    ·
                      rfl

theorem cell23_4210119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_4210119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210119 prefixEnd_4210119 := by exact prefixLift 4210119
  have htrace : WordTrace (prefixWord ++ tailWord_4210119) baseStart_4210119 baseEnd_4210119 := by
    simpa [prefixWord, tailWord_4210119, baseEnd_4210119] using wordTrace_append hprefix tailTrace_4210119
  have hstable : (prefixWord ++ tailWord_4210119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210119).length < 2 ^ (prefixWord ++ tailWord_4210119).sum := by decide
  have hdescent : baseEnd_4210119 < baseStart_4210119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210166 : List Nat := [5, 1, 1, 1, 2, 2, 2, 3, 6]
def baseStart_4210166 : Nat := 118140960795 + 4210166 * 2 ^ 59
def prefixEnd_4210166 : Nat := 4983230072969 + 3 ^ 40 * 4210166 * 2
def baseEnd_4210166 : Nat := 240204310357475548873645

theorem tailTrace_4210166 : CollatzResearch.WordTrace tailWord_4210166 prefixEnd_4210166 240204310357475548873645 := by
  unfold tailWord_4210166
  simp only [CollatzResearch.WordTrace]
  refine ⟨9597335579080943497017647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102371579510196730634854901 9597335579080943497017647)
  ·
    refine ⟨14396003368621415245526471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9597335579080943497017647 14396003368621415245526471)
    ·
      refine ⟨21594005052932122868289707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14396003368621415245526471 21594005052932122868289707)
      ·
        refine ⟨32391007579398184302434561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21594005052932122868289707 32391007579398184302434561)
        ·
          refine ⟨24293255684548638226825921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32391007579398184302434561 24293255684548638226825921)
          ·
            refine ⟨18219941763411478670119441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24293255684548638226825921 18219941763411478670119441)
            ·
              refine ⟨13664956322558609002589581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18219941763411478670119441 13664956322558609002589581)
              ·
                refine ⟨5124358620959478375971093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13664956322558609002589581 5124358620959478375971093)
                ·
                  refine ⟨240204310357475548873645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5124358620959478375971093 240204310357475548873645)
                  ·
                    rfl

theorem cell23_4210166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_4210166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210166 prefixEnd_4210166 := by exact prefixLift 4210166
  have htrace : WordTrace (prefixWord ++ tailWord_4210166) baseStart_4210166 baseEnd_4210166 := by
    simpa [prefixWord, tailWord_4210166, baseEnd_4210166] using wordTrace_append hprefix tailTrace_4210166
  have hstable : (prefixWord ++ tailWord_4210166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210166).length < 2 ^ (prefixWord ++ tailWord_4210166).sum := by decide
  have hdescent : baseEnd_4210166 < baseStart_4210166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210180 : List Nat := [2, 3, 2, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_4210180 : Nat := 118140960795 + 4210180 * 2 ^ 59
def prefixEnd_4210180 : Nat := 4983230072969 + 3 ^ 40 * 4210180 * 2
def baseEnd_4210180 : Nat := 2161845981946442885087741

theorem tailTrace_4210180 : CollatzResearch.WordTrace tailWord_4210180 prefixEnd_4210180 2161845981946442885087741 := by
  unfold tailWord_4210180
  simp only [CollatzResearch.WordTrace]
  refine ⟨76778939943622188171645997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102371919924829584228861329 76778939943622188171645997)
  ·
    refine ⟨28792102478858320564367249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76778939943622188171645997 28792102478858320564367249)
    ·
      refine ⟨21594076859143740423275437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28792102478858320564367249 21594076859143740423275437)
      ·
        refine ⟨8097778822178902658728289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21594076859143740423275437 8097778822178902658728289)
        ·
          refine ⟨6073334116634176994046217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8097778822178902658728289 6073334116634176994046217)
          ·
            refine ⟨4555000587475632745534663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6073334116634176994046217 4555000587475632745534663)
            ·
              refine ⟨6832500881213449118301995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4555000587475632745534663 6832500881213449118301995)
              ·
                refine ⟨10248751321820173677452993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6832500881213449118301995 10248751321820173677452993)
                ·
                  refine ⟨7686563491365130258089745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10248751321820173677452993 7686563491365130258089745)
                  ·
                    refine ⟨5764922618523847693567309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7686563491365130258089745 5764922618523847693567309)
                    ·
                      refine ⟨2161845981946442885087741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5764922618523847693567309 2161845981946442885087741)
                      ·
                        rfl

theorem cell23_4210180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_4210180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210180 prefixEnd_4210180 := by exact prefixLift 4210180
  have htrace : WordTrace (prefixWord ++ tailWord_4210180) baseStart_4210180 baseEnd_4210180 := by
    simpa [prefixWord, tailWord_4210180, baseEnd_4210180] using wordTrace_append hprefix tailTrace_4210180
  have hstable : (prefixWord ++ tailWord_4210180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210180).length < 2 ^ (prefixWord ++ tailWord_4210180).sum := by decide
  have hdescent : baseEnd_4210180 < baseStart_4210180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210210 : List Nat := [3, 3, 1, 1, 1, 1, 4, 4, 1, 1, 3]
def baseStart_4210210 : Nat := 118140960795 + 4210210 * 2 ^ 59
def prefixEnd_4210210 : Nat := 4983230072969 + 3 ^ 40 * 4210210 * 2
def baseEnd_4210210 : Nat := 2161861386366077767712603

theorem tailTrace_4210210 : CollatzResearch.WordTrace tailWord_4210210 prefixEnd_4210210 2161861386366077767712603 := by
  unfold tailWord_4210210
  simp only [CollatzResearch.WordTrace]
  refine ⟨38389743519283922866721021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102372649384757127644589389 38389743519283922866721021)
  ·
    refine ⟨14396153819731471075020383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38389743519283922866721021 14396153819731471075020383)
    ·
      refine ⟨21594230729597206612530575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14396153819731471075020383 21594230729597206612530575)
      ·
        refine ⟨32391346094395809918795863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21594230729597206612530575 32391346094395809918795863)
        ·
          refine ⟨48587019141593714878193795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32391346094395809918795863 48587019141593714878193795)
          ·
            refine ⟨72880528712390572317290693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48587019141593714878193795 72880528712390572317290693)
            ·
              refine ⟨13665099133573232309492005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72880528712390572317290693 13665099133573232309492005)
              ·
                refine ⟨2562206087544981058029751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13665099133573232309492005 2562206087544981058029751)
                ·
                  refine ⟨3843309131317471587044627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562206087544981058029751 3843309131317471587044627)
                  ·
                    refine ⟨5764963696976207380566941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3843309131317471587044627 5764963696976207380566941)
                    ·
                      refine ⟨2161861386366077767712603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5764963696976207380566941 2161861386366077767712603)
                      ·
                        rfl

theorem cell23_4210210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_4210210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210210 prefixEnd_4210210 := by exact prefixLift 4210210
  have htrace : WordTrace (prefixWord ++ tailWord_4210210) baseStart_4210210 baseEnd_4210210 := by
    simpa [prefixWord, tailWord_4210210, baseEnd_4210210] using wordTrace_append hprefix tailTrace_4210210
  have hstable : (prefixWord ++ tailWord_4210210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210210).length < 2 ^ (prefixWord ++ tailWord_4210210).sum := by decide
  have hdescent : baseEnd_4210210 < baseStart_4210210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210230 : List Nat := [5, 1, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_4210230 : Nat := 118140960795 + 4210230 * 2 ^ 59
def prefixEnd_4210230 : Nat := 4983230072969 + 3 ^ 40 * 4210230 * 2
def baseEnd_4210230 : Nat := 720623885326389229820837

theorem tailTrace_4210230 : CollatzResearch.WordTrace tailWord_4210230 prefixEnd_4210230 720623885326389229820837 := by
  unfold tailWord_4210230
  simp only [CollatzResearch.WordTrace]
  refine ⟨9597481471066452180163259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102373135691375489921741429 9597481471066452180163259)
  ·
    refine ⟨14396222206599678270244889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9597481471066452180163259 14396222206599678270244889)
    ·
      refine ⟨10797166654949758702683667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14396222206599678270244889 10797166654949758702683667)
      ·
        refine ⟨16195749982424638054025501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10797166654949758702683667 16195749982424638054025501)
        ·
          refine ⟨6073406243409239270259563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16195749982424638054025501 6073406243409239270259563)
          ·
            refine ⟨9110109365113858905389345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6073406243409239270259563 9110109365113858905389345)
            ·
              refine ⟨6832582023835394179042009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9110109365113858905389345 6832582023835394179042009)
              ·
                refine ⟨5124436517876545634281507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6832582023835394179042009 5124436517876545634281507)
                ·
                  refine ⟨7686654776814818451422261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5124436517876545634281507 7686654776814818451422261)
                  ·
                    refine ⟨720623885326389229820837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7686654776814818451422261 720623885326389229820837)
                    ·
                      rfl

theorem cell23_4210230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_4210230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210230 prefixEnd_4210230 := by exact prefixLift 4210230
  have htrace : WordTrace (prefixWord ++ tailWord_4210230) baseStart_4210230 baseEnd_4210230 := by
    simpa [prefixWord, tailWord_4210230, baseEnd_4210230] using wordTrace_append hprefix tailTrace_4210230
  have hstable : (prefixWord ++ tailWord_4210230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210230).length < 2 ^ (prefixWord ++ tailWord_4210230).sum := by decide
  have hdescent : baseEnd_4210230 < baseStart_4210230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210233 : List Nat := [1, 2, 1, 5, 1, 3, 2, 2, 1, 1, 4]
def baseStart_4210233 : Nat := 118140960795 + 4210233 * 2 ^ 59
def prefixEnd_4210233 : Nat := 4983230072969 + 3 ^ 40 * 4210233 * 2
def baseEnd_4210233 : Nat := 2161873196421131177724997

theorem tailTrace_4210233 : CollatzResearch.WordTrace tailWord_4210233 prefixEnd_4210233 2161873196421131177724997 := by
  unfold tailWord_4210233
  simp only [CollatzResearch.WordTrace]
  refine ⟨153559812956052366394971353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102373208637368244263314235 153559812956052366394971353)
  ·
    refine ⟨115169859717039274796228515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153559812956052366394971353 115169859717039274796228515)
    ·
      refine ⟨172754789575558912194342773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115169859717039274796228515 172754789575558912194342773)
      ·
        refine ⟨16195761522708648018219635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 172754789575558912194342773 16195761522708648018219635)
        ·
          refine ⟨24293642284062972027329453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16195761522708648018219635 24293642284062972027329453)
          ·
            refine ⟨9110115856523614510248545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24293642284062972027329453 9110115856523614510248545)
            ·
              refine ⟨6832586892392710882686409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9110115856523614510248545 6832586892392710882686409)
              ·
                refine ⟨5124440169294533162014807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6832586892392710882686409 5124440169294533162014807)
                ·
                  refine ⟨7686660253941799743022211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5124440169294533162014807 7686660253941799743022211)
                  ·
                    refine ⟨11529990380912699614533317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7686660253941799743022211 11529990380912699614533317)
                    ·
                      refine ⟨2161873196421131177724997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11529990380912699614533317 2161873196421131177724997)
                      ·
                        rfl

theorem cell23_4210233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_4210233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210233 prefixEnd_4210233 := by exact prefixLift 4210233
  have htrace : WordTrace (prefixWord ++ tailWord_4210233) baseStart_4210233 baseEnd_4210233 := by
    simpa [prefixWord, tailWord_4210233, baseEnd_4210233] using wordTrace_append hprefix tailTrace_4210233
  have hstable : (prefixWord ++ tailWord_4210233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210233).length < 2 ^ (prefixWord ++ tailWord_4210233).sum := by decide
  have hdescent : baseEnd_4210233 < baseStart_4210233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210239 : List Nat := [1, 1, 2, 2, 3, 4, 1, 9]
def baseStart_4210239 : Nat := 118140960795 + 4210239 * 2 ^ 59
def prefixEnd_4210239 : Nat := 4983230072969 + 3 ^ 40 * 4210239 * 2
def baseEnd_4210239 : Nat := 80069491752039190898147

theorem tailTrace_4210239 : CollatzResearch.WordTrace tailWord_4210239 prefixEnd_4210239 80069491752039190898147 := by
  unfold tailWord_4210239
  simp only [CollatzResearch.WordTrace]
  refine ⟨153560031794030629419689771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102373354529353752946459847 153560031794030629419689771)
  ·
    refine ⟨230340047691045944129534657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153560031794030629419689771 230340047691045944129534657)
    ·
      refine ⟨172755035768284458097150993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230340047691045944129534657 172755035768284458097150993)
      ·
        refine ⟨129566276826213343572863245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172755035768284458097150993 129566276826213343572863245)
        ·
          refine ⟨48587353809830003839823717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129566276826213343572863245 48587353809830003839823717)
          ·
            refine ⟨9110128839343125719966947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48587353809830003839823717 9110128839343125719966947)
            ·
              refine ⟨13665193259014688579950421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9110128839343125719966947 13665193259014688579950421)
              ·
                refine ⟨80069491752039190898147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13665193259014688579950421 80069491752039190898147)
                ·
                  rfl

theorem cell23_4210239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 9].length) (baseStart_4210239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210239 prefixEnd_4210239 := by exact prefixLift 4210239
  have htrace : WordTrace (prefixWord ++ tailWord_4210239) baseStart_4210239 baseEnd_4210239 := by
    simpa [prefixWord, tailWord_4210239, baseEnd_4210239] using wordTrace_append hprefix tailTrace_4210239
  have hstable : (prefixWord ++ tailWord_4210239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210239).length < 2 ^ (prefixWord ++ tailWord_4210239).sum := by decide
  have hdescent : baseEnd_4210239 < baseStart_4210239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210336 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 4]
def baseStart_4210336 : Nat := 118140960795 + 4210336 * 2 ^ 59
def prefixEnd_4210336 : Nat := 4983230072969 + 3 ^ 40 * 4210336 * 2
def baseEnd_4210336 : Nat := 2161926084928544274737023

theorem tailTrace_4210336 : CollatzResearch.WordTrace tailWord_4210336 prefixEnd_4210336 2161926084928544274737023 := by
  unfold tailWord_4210336
  simp only [CollatzResearch.WordTrace]
  refine ⟨76781784837339607492985431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102375713116452809990647241 76781784837339607492985431)
  ·
    refine ⟨115172677256009411239478147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76781784837339607492985431 115172677256009411239478147)
    ·
      refine ⟨172759015884014116859217221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115172677256009411239478147 172759015884014116859217221)
      ·
        refine ⟨32392315478252646911103229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172759015884014116859217221 32392315478252646911103229)
        ·
          refine ⟨12147118304344742591663711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32392315478252646911103229 12147118304344742591663711)
          ·
            refine ⟨18220677456517113887495567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12147118304344742591663711 18220677456517113887495567)
            ·
              refine ⟨27331016184775670831243351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18220677456517113887495567 27331016184775670831243351)
              ·
                refine ⟨40996524277163506246865027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27331016184775670831243351 40996524277163506246865027)
                ·
                  refine ⟨61494786415745259370297541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40996524277163506246865027 61494786415745259370297541)
                  ·
                    refine ⟨11530272452952236131930789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61494786415745259370297541 11530272452952236131930789)
                    ·
                      refine ⟨2161926084928544274737023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11530272452952236131930789 2161926084928544274737023)
                      ·
                        rfl

theorem cell23_4210336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_4210336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210336 prefixEnd_4210336 := by exact prefixLift 4210336
  have htrace : WordTrace (prefixWord ++ tailWord_4210336) baseStart_4210336 baseEnd_4210336 := by
    simpa [prefixWord, tailWord_4210336, baseEnd_4210336] using wordTrace_append hprefix tailTrace_4210336
  have hstable : (prefixWord ++ tailWord_4210336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210336).length < 2 ^ (prefixWord ++ tailWord_4210336).sum := by decide
  have hdescent : baseEnd_4210336 < baseStart_4210336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210340 : List Nat := [2, 3, 1, 2, 2, 3, 2, 1, 1, 4, 2]
def baseStart_4210340 : Nat := 118140960795 + 4210340 * 2 ^ 59
def prefixEnd_4210340 : Nat := 4983230072969 + 3 ^ 40 * 4210340 * 2
def baseEnd_4210340 : Nat := 2161928138851162259087005

theorem tailTrace_4210340 : CollatzResearch.WordTrace tailWord_4210340 prefixEnd_4210340 2161928138851162259087005 := by
  unfold tailWord_4210340
  simp only [CollatzResearch.WordTrace]
  refine ⟨76781857783332361834558237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102375810377776482446077649 76781857783332361834558237)
  ·
    refine ⟨28793196668749635687959339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76781857783332361834558237 28793196668749635687959339)
    ·
      refine ⟨43189795003124453531939009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28793196668749635687959339 43189795003124453531939009)
      ·
        refine ⟨32392346252343340148954257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43189795003124453531939009 32392346252343340148954257)
        ·
          refine ⟨24294259689257505111715693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32392346252343340148954257 24294259689257505111715693)
          ·
            refine ⟨9110347383471564416893385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24294259689257505111715693 9110347383471564416893385)
            ·
              refine ⟨6832760537603673312670039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9110347383471564416893385 6832760537603673312670039)
              ·
                refine ⟨10249140806405509969005059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6832760537603673312670039 10249140806405509969005059)
                ·
                  refine ⟨15373711209608264953507589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10249140806405509969005059 15373711209608264953507589)
                  ·
                    refine ⟨2882570851801549678782673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15373711209608264953507589 2882570851801549678782673)
                    ·
                      refine ⟨2161928138851162259087005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2882570851801549678782673 2161928138851162259087005)
                      ·
                        rfl

theorem cell23_4210340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_4210340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210340 prefixEnd_4210340 := by exact prefixLift 4210340
  have htrace : WordTrace (prefixWord ++ tailWord_4210340) baseStart_4210340 baseEnd_4210340 := by
    simpa [prefixWord, tailWord_4210340, baseEnd_4210340] using wordTrace_append hprefix tailTrace_4210340
  have hstable : (prefixWord ++ tailWord_4210340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210340).length < 2 ^ (prefixWord ++ tailWord_4210340).sum := by decide
  have hdescent : baseEnd_4210340 < baseStart_4210340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210376 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 4, 5]
def baseStart_4210376 : Nat := 118140960795 + 4210376 * 2 ^ 59
def prefixEnd_4210376 : Nat := 4983230072969 + 3 ^ 40 * 4210376 * 2
def baseEnd_4210376 : Nat := 720648874718241372745613

theorem tailTrace_4210376 : CollatzResearch.WordTrace tailWord_4210376 prefixEnd_4210376 720648874718241372745613 := by
  unfold tailWord_4210376
  simp only [CollatzResearch.WordTrace]
  refine ⟨76782514297267150908713491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102376685729689534544951321 76782514297267150908713491)
  ·
    refine ⟨115173771445900726363070237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76782514297267150908713491 115173771445900726363070237)
    ·
      refine ⟨43190164292212772386151339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115173771445900726363070237 43190164292212772386151339)
      ·
        refine ⟨64785246438319158579227009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43190164292212772386151339 64785246438319158579227009)
        ·
          refine ⟨48588934828739368934420257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64785246438319158579227009 48588934828739368934420257)
          ·
            refine ⟨36441701121554526700815193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48588934828739368934420257 36441701121554526700815193)
            ·
              refine ⟨27331275841165895025611395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36441701121554526700815193 27331275841165895025611395)
              ·
                refine ⟨40996913761748842538417093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27331275841165895025611395 40996913761748842538417093)
                ·
                  refine ⟨7686921330327907975953205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40996913761748842538417093 7686921330327907975953205)
                  ·
                    refine ⟨720648874718241372745613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7686921330327907975953205 720648874718241372745613)
                    ·
                      rfl

theorem cell23_4210376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_4210376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210376 prefixEnd_4210376 := by exact prefixLift 4210376
  have htrace : WordTrace (prefixWord ++ tailWord_4210376) baseStart_4210376 baseEnd_4210376 := by
    simpa [prefixWord, tailWord_4210376, baseEnd_4210376] using wordTrace_append hprefix tailTrace_4210376
  have hstable : (prefixWord ++ tailWord_4210376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210376).length < 2 ^ (prefixWord ++ tailWord_4210376).sum := by decide
  have hdescent : baseEnd_4210376 < baseStart_4210376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210413 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_4210413 : Nat := 118140960795 + 4210413 * 2 ^ 59
def prefixEnd_4210413 : Nat := 4983230072969 + 3 ^ 40 * 4210413 * 2
def baseEnd_4210413 : Nat := 2161965622938940473474169

theorem tailTrace_4210413 : CollatzResearch.WordTrace tailWord_4210413 prefixEnd_4210413 2161965622938940473474169 := by
  unfold tailWord_4210413
  simp only [CollatzResearch.WordTrace]
  refine ⟨153566378095400257136523893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102377585396933504757682595 153566378095400257136523893)
  ·
    refine ⟨14396847946443774106549115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153566378095400257136523893 14396847946443774106549115)
    ·
      refine ⟨21595271919665661159823673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14396847946443774106549115 21595271919665661159823673)
      ·
        refine ⟨16196453939749245869867755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21595271919665661159823673 16196453939749245869867755)
        ·
          refine ⟨24294680909623868804801633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16196453939749245869867755 24294680909623868804801633)
          ·
            refine ⟨18221010682217901603601225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24294680909623868804801633 18221010682217901603601225)
            ·
              refine ⟨13665758011663426202700919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18221010682217901603601225 13665758011663426202700919)
              ·
                refine ⟨20498637017495139304051379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13665758011663426202700919 20498637017495139304051379)
                ·
                  refine ⟨30747955526242708956077069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20498637017495139304051379 30747955526242708956077069)
                  ·
                    refine ⟨11530483322341015858528901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30747955526242708956077069 11530483322341015858528901)
                    ·
                      refine ⟨2161965622938940473474169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11530483322341015858528901 2161965622938940473474169)
                      ·
                        rfl

theorem cell23_4210413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_4210413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210413 prefixEnd_4210413 := by exact prefixLift 4210413
  have htrace : WordTrace (prefixWord ++ tailWord_4210413) baseStart_4210413 baseEnd_4210413 := by
    simpa [prefixWord, tailWord_4210413, baseEnd_4210413] using wordTrace_append hprefix tailTrace_4210413
  have hstable : (prefixWord ++ tailWord_4210413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210413).length < 2 ^ (prefixWord ++ tailWord_4210413).sum := by decide
  have hdescent : baseEnd_4210413 < baseStart_4210413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210433 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_4210433 : Nat := 118140960795 + 4210433 * 2 ^ 59
def prefixEnd_4210433 : Nat := 4983230072969 + 3 ^ 40 * 4210433 * 2
def baseEnd_4210433 : Nat := 2161975892552030395224077

theorem tailTrace_4210433 : CollatzResearch.WordTrace tailWord_4210433 prefixEnd_4210433 2161975892552030395224077 := by
  unfold tailWord_4210433
  simp only [CollatzResearch.WordTrace]
  refine ⟨153567107555327800552251953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102378071703551867034834635 153567107555327800552251953)
  ·
    refine ⟨115175330666495850414188965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153567107555327800552251953 115175330666495850414188965)
    ·
      refine ⟨21595374499967971952660431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115175330666495850414188965 21595374499967971952660431)
      ·
        refine ⟨32393061749951957928990647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21595374499967971952660431 32393061749951957928990647)
        ·
          refine ⟨48589592624927936893485971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32393061749951957928990647 48589592624927936893485971)
          ·
            refine ⟨72884388937391905340228957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48589592624927936893485971 72884388937391905340228957)
            ·
              refine ⟨27331645851521964502585859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72884388937391905340228957 27331645851521964502585859)
              ·
                refine ⟨40997468777282946753878789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27331645851521964502585859 40997468777282946753878789)
                ·
                  refine ⟨7687025395740552516352273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40997468777282946753878789 7687025395740552516352273)
                  ·
                    refine ⟨5765269046805414387264205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7687025395740552516352273 5765269046805414387264205)
                    ·
                      refine ⟨2161975892552030395224077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5765269046805414387264205 2161975892552030395224077)
                      ·
                        rfl

theorem cell23_4210433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_4210433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210433 prefixEnd_4210433 := by exact prefixLift 4210433
  have htrace : WordTrace (prefixWord ++ tailWord_4210433) baseStart_4210433 baseEnd_4210433 := by
    simpa [prefixWord, tailWord_4210433, baseEnd_4210433] using wordTrace_append hprefix tailTrace_4210433
  have hstable : (prefixWord ++ tailWord_4210433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210433).length < 2 ^ (prefixWord ++ tailWord_4210433).sum := by decide
  have hdescent : baseEnd_4210433 < baseStart_4210433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210453 : List Nat := [1, 3, 2, 1, 2, 4, 1, 3, 6]
def baseStart_4210453 : Nat := 118140960795 + 4210453 * 2 ^ 59
def prefixEnd_4210453 : Nat := 4983230072969 + 3 ^ 40 * 4210453 * 2
def baseEnd_4210453 : Nat := 240220684685013368552665

theorem tailTrace_4210453 : CollatzResearch.WordTrace tailWord_4210453 prefixEnd_4210453 240220684685013368552665 := by
  unfold tailWord_4210453
  simp only [CollatzResearch.WordTrace]
  refine ⟨153567837015255343967980013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102378558010170229311986675 153567837015255343967980013)
  ·
    refine ⟨57587938880720753987992505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153567837015255343967980013 57587938880720753987992505)
    ·
      refine ⟨43190954160540565490994379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57587938880720753987992505 43190954160540565490994379)
      ·
        refine ⟨64786431240810848236491569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43190954160540565490994379 64786431240810848236491569)
        ·
          refine ⟨48589823430608136177368677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64786431240810848236491569 48589823430608136177368677)
          ·
            refine ⟨9110591893239025533256627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48589823430608136177368677 9110591893239025533256627)
            ·
              refine ⟨13665887839858538299884941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9110591893239025533256627 13665887839858538299884941)
              ·
                refine ⟨5124707939946951862456853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13665887839858538299884941 5124707939946951862456853)
                ·
                  refine ⟨240220684685013368552665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5124707939946951862456853 240220684685013368552665)
                  ·
                    rfl

theorem cell23_4210453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 6].length) (baseStart_4210453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210453 prefixEnd_4210453 := by exact prefixLift 4210453
  have htrace : WordTrace (prefixWord ++ tailWord_4210453) baseStart_4210453 baseEnd_4210453 := by
    simpa [prefixWord, tailWord_4210453, baseEnd_4210453] using wordTrace_append hprefix tailTrace_4210453
  have hstable : (prefixWord ++ tailWord_4210453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210453).length < 2 ^ (prefixWord ++ tailWord_4210453).sum := by decide
  have hdescent : baseEnd_4210453 < baseStart_4210453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210456 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 1, 2, 6]
def baseStart_4210456 : Nat := 118140960795 + 4210456 * 2 ^ 59
def prefixEnd_4210456 : Nat := 4983230072969 + 3 ^ 40 * 4210456 * 2
def baseEnd_4210456 : Nat := 2161987702607083805236471

theorem tailTrace_4210456 : CollatzResearch.WordTrace tailWord_4210456 prefixEnd_4210456 2161987702607083805236471 := by
  unfold tailWord_4210456
  simp only [CollatzResearch.WordTrace]
  refine ⟨76783973217122237740169611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102378630956162983653559481 76783973217122237740169611)
  ·
    refine ⟨115175959825683356610254417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76783973217122237740169611 115175959825683356610254417)
    ·
      refine ⟨86381969869262517457690813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115175959825683356610254417 86381969869262517457690813)
      ·
        refine ⟨32393238700973444046634055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86381969869262517457690813 32393238700973444046634055)
        ·
          refine ⟨48589858051460166069951083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32393238700973444046634055 48589858051460166069951083)
          ·
            refine ⟨72884787077190249104926625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48589858051460166069951083 72884787077190249104926625)
            ·
              refine ⟨54663590307892686828694969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72884787077190249104926625 54663590307892686828694969)
              ·
                refine ⟨40997692730919515121521227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54663590307892686828694969 40997692730919515121521227)
                ·
                  refine ⟨61496539096379272682281841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40997692730919515121521227 61496539096379272682281841)
                  ·
                    refine ⟨46122404322284454511711381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61496539096379272682281841 46122404322284454511711381)
                    ·
                      refine ⟨2161987702607083805236471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46122404322284454511711381 2161987702607083805236471)
                      ·
                        rfl

theorem cell23_4210456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_4210456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210456 prefixEnd_4210456 := by exact prefixLift 4210456
  have htrace : WordTrace (prefixWord ++ tailWord_4210456) baseStart_4210456 baseEnd_4210456 := by
    simpa [prefixWord, tailWord_4210456, baseEnd_4210456] using wordTrace_append hprefix tailTrace_4210456
  have hstable : (prefixWord ++ tailWord_4210456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210456).length < 2 ^ (prefixWord ++ tailWord_4210456).sum := by decide
  have hdescent : baseEnd_4210456 < baseStart_4210456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210503 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 4]
def baseStart_4210503 : Nat := 118140960795 + 4210503 * 2 ^ 59
def prefixEnd_4210503 : Nat := 4983230072969 + 3 ^ 40 * 4210503 * 2
def baseEnd_4210503 : Nat := 2162011836197845121348755

theorem tailTrace_4210503 : CollatzResearch.WordTrace tailWord_4210503 prefixEnd_4210503 2162011836197845121348755 := by
  unfold tailWord_4210503
  simp only [CollatzResearch.WordTrace]
  refine ⟨153569660665074202507300163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102379773776716135004866775 153569660665074202507300163)
  ·
    refine ⟨230354490997611303760950245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153569660665074202507300163 230354490997611303760950245)
    ·
      refine ⟨43191467062052119455178171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230354490997611303760950245 43191467062052119455178171)
      ·
        refine ⟨64787200593078179182767257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43191467062052119455178171 64787200593078179182767257)
        ·
          refine ⟨48590400444808634387075443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64787200593078179182767257 48590400444808634387075443)
          ·
            refine ⟨72885600667212951580613165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48590400444808634387075443 72885600667212951580613165)
            ·
              refine ⟨27332100250204856842729937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72885600667212951580613165 27332100250204856842729937)
              ·
                refine ⟨20499075187653642632047453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27332100250204856842729937 20499075187653642632047453)
                ·
                  refine ⟨7687153195370115987017795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20499075187653642632047453 7687153195370115987017795)
                  ·
                    refine ⟨11530729793055173980526693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7687153195370115987017795 11530729793055173980526693)
                    ·
                      refine ⟨2162011836197845121348755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11530729793055173980526693 2162011836197845121348755)
                      ·
                        rfl

theorem cell23_4210503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_4210503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210503 prefixEnd_4210503 := by exact prefixLift 4210503
  have htrace : WordTrace (prefixWord ++ tailWord_4210503) baseStart_4210503 baseEnd_4210503 := by
    simpa [prefixWord, tailWord_4210503, baseEnd_4210503] using wordTrace_append hprefix tailTrace_4210503
  have hstable : (prefixWord ++ tailWord_4210503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210503).length < 2 ^ (prefixWord ++ tailWord_4210503).sum := by decide
  have hdescent : baseEnd_4210503 < baseStart_4210503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210513 : List Nat := [1, 2, 2, 1, 5, 1, 1, 3, 1, 6]
def baseStart_4210513 : Nat := 118140960795 + 4210513 * 2 ^ 59
def prefixEnd_4210513 : Nat := 4983230072969 + 3 ^ 40 * 4210513 * 2
def baseEnd_4210513 : Nat := 720672323668130027407903

theorem tailTrace_4210513 : CollatzResearch.WordTrace tailWord_4210513 prefixEnd_4210513 720672323668130027407903 := by
  unfold tailWord_4210513
  simp only [CollatzResearch.WordTrace]
  refine ⟨153570025395037974215164193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102380016930025316143442795 153570025395037974215164193)
  ·
    refine ⟨115177519046278480661373145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153570025395037974215164193 115177519046278480661373145)
    ·
      refine ⟨86383139284708860496029859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115177519046278480661373145 86383139284708860496029859)
      ·
        refine ⟨129574708927063290744044789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86383139284708860496029859 129574708927063290744044789)
        ·
          refine ⟨12147628961912183507254199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 129574708927063290744044789 12147628961912183507254199)
          ·
            refine ⟨18221443442868275260881299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12147628961912183507254199 18221443442868275260881299)
            ·
              refine ⟨27332165164302412891321949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18221443442868275260881299 27332165164302412891321949)
              ·
                refine ⟨10249561936613404834245731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27332165164302412891321949 10249561936613404834245731)
                ·
                  refine ⟨15374342904920107251368597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10249561936613404834245731 15374342904920107251368597)
                  ·
                    refine ⟨720672323668130027407903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15374342904920107251368597 720672323668130027407903)
                    ·
                      rfl

theorem cell23_4210513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_4210513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210513 prefixEnd_4210513 := by exact prefixLift 4210513
  have htrace : WordTrace (prefixWord ++ tailWord_4210513) baseStart_4210513 baseEnd_4210513 := by
    simpa [prefixWord, tailWord_4210513, baseEnd_4210513] using wordTrace_append hprefix tailTrace_4210513
  have hstable : (prefixWord ++ tailWord_4210513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210513).length < 2 ^ (prefixWord ++ tailWord_4210513).sum := by decide
  have hdescent : baseEnd_4210513 < baseStart_4210513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210530 : List Nat := [3, 3, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_4210530 : Nat := 118140960795 + 4210530 * 2 ^ 59
def prefixEnd_4210530 : Nat := 4983230072969 + 3 ^ 40 * 4210530 * 2
def baseEnd_4210530 : Nat := 720675233391838838570377

theorem tailTrace_4210530 : CollatzResearch.WordTrace tailWord_4210530 prefixEnd_4210530 720675233391838838570377 := by
  unfold tailWord_4210530
  simp only [CollatzResearch.WordTrace]
  refine ⟨38392661358994096529633261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102380430290650924079022029 38392661358994096529633261)
  ·
    refine ⟨14397248009622786198612473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38392661358994096529633261 14397248009622786198612473)
    ·
      refine ⟨10797936007217089648959355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14397248009622786198612473 10797936007217089648959355)
      ·
        refine ⟨16196904010825634473439033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10797936007217089648959355 16196904010825634473439033)
        ·
          refine ⟨12147678008119225855079275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16196904010825634473439033 12147678008119225855079275)
          ·
            refine ⟨18221517012178838782618913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12147678008119225855079275 18221517012178838782618913)
            ·
              refine ⟨13666137759134129086964185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18221517012178838782618913 13666137759134129086964185)
              ·
                refine ⟨10249603319350596815223139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13666137759134129086964185 10249603319350596815223139)
                ·
                  refine ⟨15374404979025895222834709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10249603319350596815223139 15374404979025895222834709)
                  ·
                    refine ⟨720675233391838838570377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15374404979025895222834709 720675233391838838570377)
                    ·
                      rfl

theorem cell23_4210530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_4210530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210530 prefixEnd_4210530 := by exact prefixLift 4210530
  have htrace : WordTrace (prefixWord ++ tailWord_4210530) baseStart_4210530 baseEnd_4210530 := by
    simpa [prefixWord, tailWord_4210530, baseEnd_4210530] using wordTrace_append hprefix tailTrace_4210530
  have hstable : (prefixWord ++ tailWord_4210530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210530).length < 2 ^ (prefixWord ++ tailWord_4210530).sum := by decide
  have hdescent : baseEnd_4210530 < baseStart_4210530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210554 : List Nat := [3, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2]
def baseStart_4210554 : Nat := 118140960795 + 4210554 * 2 ^ 59
def prefixEnd_4210554 : Nat := 4983230072969 + 3 ^ 40 * 4210554 * 2
def baseEnd_4210554 : Nat := 2162038023711224421811021

theorem tailTrace_4210554 : CollatzResearch.WordTrace tailWord_4210554 prefixEnd_4210554 2162038023711224421811021 := by
  unfold tailWord_4210554
  simp only [CollatzResearch.WordTrace]
  refine ⟨38392880196972359554351679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102381013858592958811604477 38392880196972359554351679)
  ·
    refine ⟨57589320295458539331527519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38392880196972359554351679 57589320295458539331527519)
    ·
      refine ⟨86383980443187808997291279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57589320295458539331527519 86383980443187808997291279)
      ·
        refine ⟨129575970664781713495936919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86383980443187808997291279 129575970664781713495936919)
        ·
          refine ⟨194363955997172570243905379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129575970664781713495936919 194363955997172570243905379)
          ·
            refine ⟨291545933995758855365858069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194363955997172570243905379 291545933995758855365858069)
            ·
              refine ⟨13666215656051196345274597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 291545933995758855365858069 13666215656051196345274597)
              ·
                refine ⟨2562415435509599314738987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13666215656051196345274597 2562415435509599314738987)
                ·
                  refine ⟨3843623153264398972108481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562415435509599314738987 3843623153264398972108481)
                  ·
                    refine ⟨2882717364948299229081361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3843623153264398972108481 2882717364948299229081361)
                    ·
                      refine ⟨2162038023711224421811021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2882717364948299229081361 2162038023711224421811021)
                      ·
                        rfl

theorem cell23_4210554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2].length) (baseStart_4210554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210554 prefixEnd_4210554 := by exact prefixLift 4210554
  have htrace : WordTrace (prefixWord ++ tailWord_4210554) baseStart_4210554 baseEnd_4210554 := by
    simpa [prefixWord, tailWord_4210554, baseEnd_4210554] using wordTrace_append hprefix tailTrace_4210554
  have hstable : (prefixWord ++ tailWord_4210554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210554).length < 2 ^ (prefixWord ++ tailWord_4210554).sum := by decide
  have hdescent : baseEnd_4210554 < baseStart_4210554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210567 : List Nat := [1, 1, 4, 2, 4, 2, 1, 1, 1, 2, 4]
def baseStart_4210567 : Nat := 118140960795 + 4210567 * 2 ^ 59
def prefixEnd_4210567 : Nat := 4983230072969 + 3 ^ 40 * 4210567 * 2
def baseEnd_4210567 : Nat := 2162044698959732870948461

theorem tailTrace_4210567 : CollatzResearch.WordTrace tailWord_4210567 prefixEnd_4210567 2162044698959732870948461 := by
  unfold tailWord_4210567
  simp only [CollatzResearch.WordTrace]
  refine ⟨153571994936842341437629955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102381329957894894291753303 153571994936842341437629955)
  ·
    refine ⟨230357992405263512156444933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153571994936842341437629955 230357992405263512156444933)
    ·
      refine ⟨43192123575986908529333425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230357992405263512156444933 43192123575986908529333425)
      ·
        refine ⟨32394092681990181397000069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43192123575986908529333425 32394092681990181397000069)
        ·
          refine ⟨6073892377873159011937513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32394092681990181397000069 6073892377873159011937513)
          ·
            refine ⟨4555419283404869258953135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6073892377873159011937513 4555419283404869258953135)
            ·
              refine ⟨6833128925107303888429703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4555419283404869258953135 6833128925107303888429703)
              ·
                refine ⟨10249693387660955832644555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6833128925107303888429703 10249693387660955832644555)
                ·
                  refine ⟨15374540081491433748966833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10249693387660955832644555 15374540081491433748966833)
                  ·
                    refine ⟨11530905061118575311725125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15374540081491433748966833 11530905061118575311725125)
                    ·
                      refine ⟨2162044698959732870948461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11530905061118575311725125 2162044698959732870948461)
                      ·
                        rfl

theorem cell23_4210567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_4210567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210567 prefixEnd_4210567 := by exact prefixLift 4210567
  have htrace : WordTrace (prefixWord ++ tailWord_4210567) baseStart_4210567 baseEnd_4210567 := by
    simpa [prefixWord, tailWord_4210567, baseEnd_4210567] using wordTrace_append hprefix tailTrace_4210567
  have hstable : (prefixWord ++ tailWord_4210567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210567).length < 2 ^ (prefixWord ++ tailWord_4210567).sum := by decide
  have hdescent : baseEnd_4210567 < baseStart_4210567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210582 : List Nat := [5, 3, 1, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_4210582 : Nat := 118140960795 + 4210582 * 2 ^ 59
def prefixEnd_4210582 : Nat := 4983230072969 + 3 ^ 40 * 4210582 * 2
def baseEnd_4210582 : Nat := 2162052401169550312260893

theorem tailTrace_4210582 : CollatzResearch.WordTrace tailWord_4210582 prefixEnd_4210582 2162052401169550312260893 := by
  unfold tailWord_4210582
  simp only [CollatzResearch.WordTrace]
  refine ⟨9598283876986749937464125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102381694687858665999617333 9598283876986749937464125)
  ·
    refine ⟨3599356453870031226549047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9598283876986749937464125 3599356453870031226549047)
    ·
      refine ⟨5399034680805046839823571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3599356453870031226549047 5399034680805046839823571)
      ·
        refine ⟨8098552021207570259735357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5399034680805046839823571 8098552021207570259735357)
        ·
          refine ⟨3036957007952838847400759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8098552021207570259735357 3036957007952838847400759)
          ·
            refine ⟨4555435511929258271101139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3036957007952838847400759 4555435511929258271101139)
            ·
              refine ⟨6833153267893887406651709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4555435511929258271101139 6833153267893887406651709)
              ·
                refine ⟨2562432475460207777494391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6833153267893887406651709 2562432475460207777494391)
                ·
                  refine ⟨3843648713190311666241587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562432475460207777494391 3843648713190311666241587)
                  ·
                    refine ⟨5765473069785467499362381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3843648713190311666241587 5765473069785467499362381)
                    ·
                      refine ⟨2162052401169550312260893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5765473069785467499362381 2162052401169550312260893)
                      ·
                        rfl

theorem cell23_4210582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_4210582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210582 prefixEnd_4210582 := by exact prefixLift 4210582
  have htrace : WordTrace (prefixWord ++ tailWord_4210582) baseStart_4210582 baseEnd_4210582 := by
    simpa [prefixWord, tailWord_4210582, baseEnd_4210582] using wordTrace_append hprefix tailTrace_4210582
  have hstable : (prefixWord ++ tailWord_4210582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210582).length < 2 ^ (prefixWord ++ tailWord_4210582).sum := by decide
  have hdescent : baseEnd_4210582 < baseStart_4210582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210583 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 5]
def baseStart_4210583 : Nat := 118140960795 + 4210583 * 2 ^ 59
def prefixEnd_4210583 : Nat := 4983230072969 + 3 ^ 40 * 4210583 * 2
def baseEnd_4210583 : Nat := 2162052914650204808348387

theorem tailTrace_4210583 : CollatzResearch.WordTrace tailWord_4210583 prefixEnd_4210583 2162052914650204808348387 := by
  unfold tailWord_4210583
  simp only [CollatzResearch.WordTrace]
  refine ⟨153572578504784376170212403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102381719003189584113474935 153572578504784376170212403)
  ·
    refine ⟨230358867757176564255318605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153572578504784376170212403 230358867757176564255318605)
    ·
      refine ⟨86384575408941211595744477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230358867757176564255318605 86384575408941211595744477)
      ·
        refine ⟨32394215778352954348404179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86384575408941211595744477 32394215778352954348404179)
        ·
          refine ⟨48591323667529431522606269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32394215778352954348404179 48591323667529431522606269)
          ·
            refine ⟨18221746375323536820977351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48591323667529431522606269 18221746375323536820977351)
            ·
              refine ⟨27332619562985305231466027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18221746375323536820977351 27332619562985305231466027)
              ·
                refine ⟨40998929344477957847199041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27332619562985305231466027 40998929344477957847199041)
                ·
                  refine ⟨30749197008358468385399281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40998929344477957847199041 30749197008358468385399281)
                  ·
                    refine ⟨23061897756268851289049461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30749197008358468385399281 23061897756268851289049461)
                    ·
                      refine ⟨2162052914650204808348387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23061897756268851289049461 2162052914650204808348387)
                      ·
                        rfl

theorem cell23_4210583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_4210583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210583 prefixEnd_4210583 := by exact prefixLift 4210583
  have htrace : WordTrace (prefixWord ++ tailWord_4210583) baseStart_4210583 baseEnd_4210583 := by
    simpa [prefixWord, tailWord_4210583, baseEnd_4210583] using wordTrace_append hprefix tailTrace_4210583
  have hstable : (prefixWord ++ tailWord_4210583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210583).length < 2 ^ (prefixWord ++ tailWord_4210583).sum := by decide
  have hdescent : baseEnd_4210583 < baseStart_4210583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210588 : List Nat := [2, 2, 3, 3, 1, 3, 1, 3, 1, 2, 2]
def baseStart_4210588 : Nat := 118140960795 + 4210588 * 2 ^ 59
def prefixEnd_4210588 : Nat := 4983230072969 + 3 ^ 40 * 4210588 * 2
def baseEnd_4210588 : Nat := 2162055482053477288785865

theorem tailTrace_4210588 : CollatzResearch.WordTrace tailWord_4210588 prefixEnd_4210588 2162055482053477288785865 := by
  unfold tailWord_4210588
  simp only [CollatzResearch.WordTrace]
  refine ⟨76786380434883131012072209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102381840579844174682762945 76786380434883131012072209)
  ·
    refine ⟨57589785326162348259054157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76786380434883131012072209 57589785326162348259054157)
    ·
      refine ⟨21596169497310880597145309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57589785326162348259054157 21596169497310880597145309)
      ·
        refine ⟨8098563561491580223929491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21596169497310880597145309 8098563561491580223929491)
        ·
          refine ⟨12147845342237370335894237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8098563561491580223929491 12147845342237370335894237)
          ·
            refine ⟨4555442003339013875960339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12147845342237370335894237 4555442003339013875960339)
            ·
              refine ⟨6833163005008520813940509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4555442003339013875960339 6833163005008520813940509)
              ·
                refine ⟨2562436126878195305227691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6833163005008520813940509 2562436126878195305227691)
                ·
                  refine ⟨3843654190317292957841537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562436126878195305227691 3843654190317292957841537)
                  ·
                    refine ⟨2882740642737969718381153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3843654190317292957841537 2882740642737969718381153)
                    ·
                      refine ⟨2162055482053477288785865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2882740642737969718381153 2162055482053477288785865)
                      ·
                        rfl

theorem cell23_4210588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_4210588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210588 prefixEnd_4210588 := by exact prefixLift 4210588
  have htrace : WordTrace (prefixWord ++ tailWord_4210588) baseStart_4210588 baseEnd_4210588 := by
    simpa [prefixWord, tailWord_4210588, baseEnd_4210588] using wordTrace_append hprefix tailTrace_4210588
  have hstable : (prefixWord ++ tailWord_4210588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210588).length < 2 ^ (prefixWord ++ tailWord_4210588).sum := by decide
  have hdescent : baseEnd_4210588 < baseStart_4210588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210621 : List Nat := [1, 4, 1, 2, 3, 3, 2, 1, 2, 1, 3]
def baseStart_4210621 : Nat := 118140960795 + 4210621 * 2 ^ 59
def prefixEnd_4210621 : Nat := 4983230072969 + 3 ^ 40 * 4210621 * 2
def baseEnd_4210621 : Nat := 2162072426915075659673213

theorem tailTrace_4210621 : CollatzResearch.WordTrace tailWord_4210621 prefixEnd_4210621 2162072426915075659673213 := by
  unfold tailWord_4210621
  simp only [CollatzResearch.WordTrace]
  refine ⟨153573964478646708660095717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102382642985764472440063811 153573964478646708660095717)
  ·
    refine ⟨28795118339746257873767947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153573964478646708660095717 28795118339746257873767947)
    ·
      refine ⟨43192677509619386810651921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28795118339746257873767947 43192677509619386810651921)
      ·
        refine ⟨32394508132214540107988941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43192677509619386810651921 32394508132214540107988941)
        ·
          refine ⟨12147940549580452540495853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32394508132214540107988941 12147940549580452540495853)
          ·
            refine ⟨4555477706092669702685945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12147940549580452540495853 4555477706092669702685945)
            ·
              refine ⟨3416608279569502277014459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4555477706092669702685945 3416608279569502277014459)
              ·
                refine ⟨5124912419354253415521689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3416608279569502277014459 5124912419354253415521689)
                ·
                  refine ⟨3843684314515690061641267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5124912419354253415521689 3843684314515690061641267)
                  ·
                    refine ⟨5765526471773535092461901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3843684314515690061641267 5765526471773535092461901)
                    ·
                      refine ⟨2162072426915075659673213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5765526471773535092461901 2162072426915075659673213)
                      ·
                        rfl

theorem cell23_4210621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_4210621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210621 prefixEnd_4210621 := by exact prefixLift 4210621
  have htrace : WordTrace (prefixWord ++ tailWord_4210621) baseStart_4210621 baseEnd_4210621 := by
    simpa [prefixWord, tailWord_4210621, baseEnd_4210621] using wordTrace_append hprefix tailTrace_4210621
  have hstable : (prefixWord ++ tailWord_4210621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210621).length < 2 ^ (prefixWord ++ tailWord_4210621).sum := by decide
  have hdescent : baseEnd_4210621 < baseStart_4210621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210623 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 4]
def baseStart_4210623 : Nat := 118140960795 + 4210623 * 2 ^ 59
def prefixEnd_4210623 : Nat := 4983230072969 + 3 ^ 40 * 4210623 * 2
def baseEnd_4210623 : Nat := 2162073453876384651848203

theorem tailTrace_4210623 : CollatzResearch.WordTrace tailWord_4210623 prefixEnd_4210623 2162073453876384651848203 := by
  unfold tailWord_4210623
  simp only [CollatzResearch.WordTrace]
  refine ⟨153574037424639463001668523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102382691616426308667779015 153574037424639463001668523)
  ·
    refine ⟨230361056136959194502502785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153574037424639463001668523 230361056136959194502502785)
    ·
      refine ⟨172770792102719395876877089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230361056136959194502502785 172770792102719395876877089)
      ·
        refine ⟨129578094077039546907657817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172770792102719395876877089 129578094077039546907657817)
        ·
          refine ⟨97183570557779660180743363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129578094077039546907657817 97183570557779660180743363)
          ·
            refine ⟨145775355836669490271115045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97183570557779660180743363 145775355836669490271115045)
            ·
              refine ⟨27332879219375529425834071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145775355836669490271115045 27332879219375529425834071)
              ·
                refine ⟨40999318829063294138751107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27332879219375529425834071 40999318829063294138751107)
                ·
                  refine ⟨61498978243594941208126661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40999318829063294138751107 61498978243594941208126661)
                  ·
                    refine ⟨11531058420674051476523749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61498978243594941208126661 11531058420674051476523749)
                    ·
                      refine ⟨2162073453876384651848203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11531058420674051476523749 2162073453876384651848203)
                      ·
                        rfl

theorem cell23_4210623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_4210623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210623 prefixEnd_4210623 := by exact prefixLift 4210623
  have htrace : WordTrace (prefixWord ++ tailWord_4210623) baseStart_4210623 baseEnd_4210623 := by
    simpa [prefixWord, tailWord_4210623, baseEnd_4210623] using wordTrace_append hprefix tailTrace_4210623
  have hstable : (prefixWord ++ tailWord_4210623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210623).length < 2 ^ (prefixWord ++ tailWord_4210623).sum := by decide
  have hdescent : baseEnd_4210623 < baseStart_4210623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210660 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 2, 3, 3]
def baseStart_4210660 : Nat := 118140960795 + 4210660 * 2 ^ 59
def prefixEnd_4210660 : Nat := 4983230072969 + 3 ^ 40 * 4210660 * 2
def baseEnd_4210660 : Nat := 2162092452660601007085533

theorem tailTrace_4210660 : CollatzResearch.WordTrace tailWord_4210660 prefixEnd_4210660 2162092452660601007085533 := by
  unfold tailWord_4210660
  simp only [CollatzResearch.WordTrace]
  refine ⟨76787693462752709160382717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102383591283670278880510289 76787693462752709160382717)
  ·
    refine ⟨28795385048532265935143519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76787693462752709160382717 28795385048532265935143519)
    ·
      refine ⟨43193077572798398902715279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28795385048532265935143519 43193077572798398902715279)
      ·
        refine ⟨64789616359197598354072919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43193077572798398902715279 64789616359197598354072919)
        ·
          refine ⟨97184424538796397531109379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64789616359197598354072919 97184424538796397531109379)
          ·
            refine ⟨145776636808194596296664069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97184424538796397531109379 145776636808194596296664069)
            ·
              refine ⟨27333119401536486805624513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145776636808194596296664069 27333119401536486805624513)
              ·
                refine ⟨20499839551152365104218385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27333119401536486805624513 20499839551152365104218385)
                ·
                  refine ⟨15374879663364273828163789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20499839551152365104218385 15374879663364273828163789)
                  ·
                    refine ⟨5765579873761602685561421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15374879663364273828163789 5765579873761602685561421)
                    ·
                      refine ⟨2162092452660601007085533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5765579873761602685561421 2162092452660601007085533)
                      ·
                        rfl

theorem cell23_4210660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_4210660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210660 prefixEnd_4210660 := by exact prefixLift 4210660
  have htrace : WordTrace (prefixWord ++ tailWord_4210660) baseStart_4210660 baseEnd_4210660 := by
    simpa [prefixWord, tailWord_4210660, baseEnd_4210660] using wordTrace_append hprefix tailTrace_4210660
  have hstable : (prefixWord ++ tailWord_4210660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210660).length < 2 ^ (prefixWord ++ tailWord_4210660).sum := by decide
  have hdescent : baseEnd_4210660 < baseStart_4210660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210700 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 1, 3, 4]
def baseStart_4210700 : Nat := 118140960795 + 4210700 * 2 ^ 59
def prefixEnd_4210700 : Nat := 4983230072969 + 3 ^ 40 * 4210700 * 2
def baseEnd_4210700 : Nat := 2162112991886780850585349

theorem tailTrace_4210700 : CollatzResearch.WordTrace tailWord_4210700 prefixEnd_4210700 2162112991886780850585349 := by
  unfold tailWord_4210700
  simp only [CollatzResearch.WordTrace]
  refine ⟨76788422922680252576110777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102384563896907003434814369 76788422922680252576110777)
  ·
    refine ⟨57591317192010189432083083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76788422922680252576110777 57591317192010189432083083)
    ·
      refine ⟨86386975788015284148124625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57591317192010189432083083 86386975788015284148124625)
      ·
        refine ⟨64790231841011463111093469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86386975788015284148124625 64790231841011463111093469)
        ·
          refine ⟨24296336940379298666660051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64790231841011463111093469 24296336940379298666660051)
          ·
            refine ⟨36444505410568947999990077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24296336940379298666660051 36444505410568947999990077)
            ·
              refine ⟨13666689528963355499996279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36444505410568947999990077 13666689528963355499996279)
              ·
                refine ⟨20500034293445033249994419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13666689528963355499996279 20500034293445033249994419)
                ·
                  refine ⟨30750051440167549874991629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20500034293445033249994419 30750051440167549874991629)
                  ·
                    refine ⟨11531269290062831203121861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30750051440167549874991629 11531269290062831203121861)
                    ·
                      refine ⟨2162112991886780850585349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11531269290062831203121861 2162112991886780850585349)
                      ·
                        rfl

theorem cell23_4210700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_4210700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210700 prefixEnd_4210700 := by exact prefixLift 4210700
  have htrace : WordTrace (prefixWord ++ tailWord_4210700) baseStart_4210700 baseEnd_4210700 := by
    simpa [prefixWord, tailWord_4210700, baseEnd_4210700] using wordTrace_append hprefix tailTrace_4210700
  have hstable : (prefixWord ++ tailWord_4210700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210700).length < 2 ^ (prefixWord ++ tailWord_4210700).sum := by decide
  have hdescent : baseEnd_4210700 < baseStart_4210700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210734 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_4210734 : Nat := 118140960795 + 4210734 * 2 ^ 59
def prefixEnd_4210734 : Nat := 4983230072969 + 3 ^ 40 * 4210734 * 2
def baseEnd_4210734 : Nat := 2162130450229033717560193

theorem tailTrace_4210734 : CollatzResearch.WordTrace tailWord_4210734 prefixEnd_4210734 2162130450229033717560193 := by
  unfold tailWord_4210734
  simp only [CollatzResearch.WordTrace]
  refine ⟨19197260740904666119869907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102385390618158219305972837 19197260740904666119869907)
  ·
    refine ⟨28795891111356999179804861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19197260740904666119869907 28795891111356999179804861)
    ·
      refine ⟨10798459166758874692426823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28795891111356999179804861 10798459166758874692426823)
      ·
        refine ⟨16197688750138312038640235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10798459166758874692426823 16197688750138312038640235)
        ·
          refine ⟨24296533125207468057960353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16197688750138312038640235 24296533125207468057960353)
          ·
            refine ⟨18222399843905601043470265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24296533125207468057960353 18222399843905601043470265)
            ·
              refine ⟨13666799882929200782602699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18222399843905601043470265 13666799882929200782602699)
              ·
                refine ⟨20500199824393801173904049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13666799882929200782602699 20500199824393801173904049)
                ·
                  refine ⟨15375149868295350880428037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20500199824393801173904049 15375149868295350880428037)
                  ·
                    refine ⟨2882840600305378290080257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15375149868295350880428037 2882840600305378290080257)
                    ·
                      refine ⟨2162130450229033717560193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2882840600305378290080257 2162130450229033717560193)
                      ·
                        rfl

theorem cell23_4210734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_4210734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210734 prefixEnd_4210734 := by exact prefixLift 4210734
  have htrace : WordTrace (prefixWord ++ tailWord_4210734) baseStart_4210734 baseEnd_4210734 := by
    simpa [prefixWord, tailWord_4210734, baseEnd_4210734] using wordTrace_append hprefix tailTrace_4210734
  have hstable : (prefixWord ++ tailWord_4210734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210734).length < 2 ^ (prefixWord ++ tailWord_4210734).sum := by decide
  have hdescent : baseEnd_4210734 < baseStart_4210734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210774 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 8]
def baseStart_4210774 : Nat := 118140960795 + 4210774 * 2 ^ 59
def prefixEnd_4210774 : Nat := 4983230072969 + 3 ^ 40 * 4210774 * 2
def baseEnd_4210774 : Nat := 240238998828357062340001

theorem tailTrace_4210774 : CollatzResearch.WordTrace tailWord_4210774 prefixEnd_4210774 240238998828357062340001 := by
  unfold tailWord_4210774
  simp only [CollatzResearch.WordTrace]
  refine ⟨9598721552943275986900961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102386363231394943860276917 9598721552943275986900961)
  ·
    refine ⟨7199041164707456990175721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9598721552943275986900961 7199041164707456990175721)
    ·
      refine ⟨5399280873530592742631791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7199041164707456990175721 5399280873530592742631791)
      ·
        refine ⟨8098921310295889113947687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5399280873530592742631791 8098921310295889113947687)
        ·
          refine ⟨12148381965443833670921531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8098921310295889113947687 12148381965443833670921531)
          ·
            refine ⟨18222572948165750506382297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12148381965443833670921531 18222572948165750506382297)
            ·
              refine ⟨13666929711124312879786723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18222572948165750506382297 13666929711124312879786723)
              ·
                refine ⟨20500394566686469319680085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13666929711124312879786723 20500394566686469319680085)
                ·
                  refine ⟨240238998828357062340001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 20500394566686469319680085 240238998828357062340001)
                  ·
                    rfl

theorem cell23_4210774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_4210774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210774 prefixEnd_4210774 := by exact prefixLift 4210774
  have htrace : WordTrace (prefixWord ++ tailWord_4210774) baseStart_4210774 baseEnd_4210774 := by
    simpa [prefixWord, tailWord_4210774, baseEnd_4210774] using wordTrace_append hprefix tailTrace_4210774
  have hstable : (prefixWord ++ tailWord_4210774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210774).length < 2 ^ (prefixWord ++ tailWord_4210774).sum := by decide
  have hdescent : baseEnd_4210774 < baseStart_4210774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210784 : List Nat := [2, 1, 1, 3, 2, 3, 3, 1, 3, 1, 3]
def baseStart_4210784 : Nat := 118140960795 + 4210784 * 2 ^ 59
def prefixEnd_4210784 : Nat := 4983230072969 + 3 ^ 40 * 4210784 * 2
def baseEnd_4210784 : Nat := 2162156124261758521934963

theorem tailTrace_4210784 : CollatzResearch.WordTrace tailWord_4210784 prefixEnd_4210784 2162156124261758521934963 := by
  unfold tailWord_4210784
  simp only [CollatzResearch.WordTrace]
  refine ⟨76789954788528093749139703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102386606384704124998852937 76789954788528093749139703)
  ·
    refine ⟨115184932182792140623709555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76789954788528093749139703 115184932182792140623709555)
    ·
      refine ⟨172777398274188210935564333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115184932182792140623709555 172777398274188210935564333)
      ·
        refine ⟨64791524352820579100836625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172777398274188210935564333 64791524352820579100836625)
        ·
          refine ⟨48593643264615434325627469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64791524352820579100836625 48593643264615434325627469)
          ·
            refine ⟨18222616224230787872110301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48593643264615434325627469 18222616224230787872110301)
            ·
              refine ⟨6833481084086545452041363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18222616224230787872110301 6833481084086545452041363)
              ·
                refine ⟨10250221626129818178062045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6833481084086545452041363 10250221626129818178062045)
                ·
                  refine ⟨3843833109798681816773267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10250221626129818178062045 3843833109798681816773267)
                  ·
                    refine ⟨5765749664698022725159901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3843833109798681816773267 5765749664698022725159901)
                    ·
                      refine ⟨2162156124261758521934963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5765749664698022725159901 2162156124261758521934963)
                      ·
                        rfl

theorem cell23_4210784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 3, 1, 3].length) (baseStart_4210784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210784 prefixEnd_4210784 := by exact prefixLift 4210784
  have htrace : WordTrace (prefixWord ++ tailWord_4210784) baseStart_4210784 baseEnd_4210784 := by
    simpa [prefixWord, tailWord_4210784, baseEnd_4210784] using wordTrace_append hprefix tailTrace_4210784
  have hstable : (prefixWord ++ tailWord_4210784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210784).length < 2 ^ (prefixWord ++ tailWord_4210784).sum := by decide
  have hdescent : baseEnd_4210784 < baseStart_4210784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210807 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 4]
def baseStart_4210807 : Nat := 118140960795 + 4210807 * 2 ^ 59
def prefixEnd_4210807 : Nat := 4983230072969 + 3 ^ 40 * 4210807 * 2
def baseEnd_4210807 : Nat := 2162167934316811931947357

theorem tailTrace_4210807 : CollatzResearch.WordTrace tailWord_4210807 prefixEnd_4210807 2162167934316811931947357 := by
  unfold tailWord_4210807
  simp only [CollatzResearch.WordTrace]
  refine ⟨153580748455972862426366675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102387165637315241617577783 153580748455972862426366675)
  ·
    refine ⟨230371122683959293639550013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153580748455972862426366675 230371122683959293639550013)
    ·
      refine ⟨86389171006484735114831255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230371122683959293639550013 86389171006484735114831255)
      ·
        refine ⟨129583756509727102672246883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86389171006484735114831255 129583756509727102672246883)
        ·
          refine ⟨194375634764590654008370325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129583756509727102672246883 194375634764590654008370325)
          ·
            refine ⟨9111357879590186906642359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 194375634764590654008370325 9111357879590186906642359)
            ·
              refine ⟨13667036819385280359963539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9111357879590186906642359 13667036819385280359963539)
              ·
                refine ⟨20500555229077920539945309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13667036819385280359963539 20500555229077920539945309)
                ·
                  refine ⟨7687708210904220202479491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20500555229077920539945309 7687708210904220202479491)
                  ·
                    refine ⟨11531562316356330303719237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7687708210904220202479491 11531562316356330303719237)
                    ·
                      refine ⟨2162167934316811931947357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11531562316356330303719237 2162167934316811931947357)
                      ·
                        rfl

theorem cell23_4210807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_4210807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210807 prefixEnd_4210807 := by exact prefixLift 4210807
  have htrace : WordTrace (prefixWord ++ tailWord_4210807) baseStart_4210807 baseEnd_4210807 := by
    simpa [prefixWord, tailWord_4210807, baseEnd_4210807] using wordTrace_append hprefix tailTrace_4210807
  have hstable : (prefixWord ++ tailWord_4210807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210807).length < 2 ^ (prefixWord ++ tailWord_4210807).sum := by decide
  have hdescent : baseEnd_4210807 < baseStart_4210807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210830 : List Nat := [4, 1, 1, 3, 14]
def baseStart_4210830 : Nat := 118140960795 + 4210830 * 2 ^ 59
def prefixEnd_4210830 : Nat := 4983230072969 + 3 ^ 40 * 4210830 * 2
def baseEnd_4210830 : Nat := 2965953010112298137119

theorem tailTrace_4210830 : CollatzResearch.WordTrace tailWord_4210830 prefixEnd_4210830 2965953010112298137119 := by
  unfold tailWord_4210830
  simp only [CollatzResearch.WordTrace]
  refine ⟨19197698416861192169306743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102387724889926358236302629 19197698416861192169306743)
  ·
    refine ⟨28796547625291788253960115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19197698416861192169306743 28796547625291788253960115)
    ·
      refine ⟨43194821437937682380940173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28796547625291788253960115 43194821437937682380940173)
      ·
        refine ⟨16198058039226630892852565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43194821437937682380940173 16198058039226630892852565)
        ·
          refine ⟨2965953010112298137119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 16198058039226630892852565 2965953010112298137119)
          ·
            rfl

theorem cell23_4210830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 14].length) (baseStart_4210830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210830 prefixEnd_4210830 := by exact prefixLift 4210830
  have htrace : WordTrace (prefixWord ++ tailWord_4210830) baseStart_4210830 baseEnd_4210830 := by
    simpa [prefixWord, tailWord_4210830, baseEnd_4210830] using wordTrace_append hprefix tailTrace_4210830
  have hstable : (prefixWord ++ tailWord_4210830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210830).length < 2 ^ (prefixWord ++ tailWord_4210830).sum := by decide
  have hdescent : baseEnd_4210830 < baseStart_4210830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210847 : List Nat := [1, 1, 2, 6, 1, 1, 3, 8]
def baseStart_4210847 : Nat := 118140960795 + 4210847 * 2 ^ 59
def prefixEnd_4210847 : Nat := 4983230072969 + 3 ^ 40 * 4210847 * 2
def baseEnd_4210847 : Nat := 80081054575666362053599

theorem tailTrace_4210847 : CollatzResearch.WordTrace tailWord_4210847 prefixEnd_4210847 80081054575666362053599 := by
  unfold tailWord_4210847
  simp only [CollatzResearch.WordTrace]
  refine ⟨153582207375827949257822795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102388138250551966171881863 153582207375827949257822795)
  ·
    refine ⟨230373311063741923886734193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153582207375827949257822795 230373311063741923886734193)
    ·
      refine ⟨172779983297806442915050645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230373311063741923886734193 172779983297806442915050645)
      ·
        refine ⟨8099061717084677011642999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 172779983297806442915050645 8099061717084677011642999)
        ·
          refine ⟨12148592575627015517464499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8099061717084677011642999 12148592575627015517464499)
          ·
            refine ⟨18222888863440523276196749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12148592575627015517464499 18222888863440523276196749)
            ·
              refine ⟨6833583323790196228573781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18222888863440523276196749 6833583323790196228573781)
              ·
                refine ⟨80081054575666362053599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6833583323790196228573781 80081054575666362053599)
                ·
                  rfl

theorem cell23_4210847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 8].length) (baseStart_4210847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210847 prefixEnd_4210847 := by exact prefixLift 4210847
  have htrace : WordTrace (prefixWord ++ tailWord_4210847) baseStart_4210847 baseEnd_4210847 := by
    simpa [prefixWord, tailWord_4210847, baseEnd_4210847] using wordTrace_append hprefix tailTrace_4210847
  have hstable : (prefixWord ++ tailWord_4210847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210847).length < 2 ^ (prefixWord ++ tailWord_4210847).sum := by decide
  have hdescent : baseEnd_4210847 < baseStart_4210847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210862 : List Nat := [4, 1, 4, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_4210862 : Nat := 118140960795 + 4210862 * 2 ^ 59
def prefixEnd_4210862 : Nat := 4983230072969 + 3 ^ 40 * 4210862 * 2
def baseEnd_4210862 : Nat := 2162196175752809216759605

theorem tailTrace_4210862 : CollatzResearch.WordTrace tailWord_4210862 prefixEnd_4210862 2162196175752809216759605 := by
  unfold tailWord_4210862
  simp only [CollatzResearch.WordTrace]
  refine ⟨19197844308846700852452355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102388502980515737879745893 19197844308846700852452355)
  ·
    refine ⟨28796766463270051278678533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19197844308846700852452355 28796766463270051278678533)
    ·
      refine ⟨5399393711863134614752225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28796766463270051278678533 5399393711863134614752225)
      ·
        refine ⟨4049545283897350961064169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5399393711863134614752225 4049545283897350961064169)
        ·
          refine ⟨3037158962923013220798127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4049545283897350961064169 3037158962923013220798127)
          ·
            refine ⟨4555738444384519831197191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3037158962923013220798127 4555738444384519831197191)
            ·
              refine ⟨6833607666576779746795787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4555738444384519831197191 6833607666576779746795787)
              ·
                refine ⟨10250411499865169620193681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6833607666576779746795787 10250411499865169620193681)
                ·
                  refine ⟨7687808624898877215145261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10250411499865169620193681 7687808624898877215145261)
                  ·
                    refine ⟨2882928234337078955679473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7687808624898877215145261 2882928234337078955679473)
                    ·
                      refine ⟨2162196175752809216759605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2882928234337078955679473 2162196175752809216759605)
                      ·
                        rfl

theorem cell23_4210862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_4210862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210862 prefixEnd_4210862 := by exact prefixLift 4210862
  have htrace : WordTrace (prefixWord ++ tailWord_4210862) baseStart_4210862 baseEnd_4210862 := by
    simpa [prefixWord, tailWord_4210862, baseEnd_4210862] using wordTrace_append hprefix tailTrace_4210862
  have hstable : (prefixWord ++ tailWord_4210862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210862).length < 2 ^ (prefixWord ++ tailWord_4210862).sum := by decide
  have hdescent : baseEnd_4210862 < baseStart_4210862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4210954 : List Nat := [3, 1, 2, 2, 1, 1, 2, 6, 5]
def baseStart_4210954 : Nat := 118140960795 + 4210954 * 2 ^ 59
def prefixEnd_4210954 : Nat := 4983230072969 + 3 ^ 40 * 4210954 * 2
def baseEnd_4210954 : Nat := 240249268441446984089909

theorem tailTrace_4210954 : CollatzResearch.WordTrace tailWord_4210954 prefixEnd_4210954 240249268441446984089909 := by
  unfold tailWord_4210954
  simp only [CollatzResearch.WordTrace]
  refine ⟨38396527496610076632991979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102390739990960204354645277 38396527496610076632991979)
  ·
    refine ⟨57594791244915114949487969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38396527496610076632991979 57594791244915114949487969)
    ·
      refine ⟨43196093433686336212115977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57594791244915114949487969 43196093433686336212115977)
      ·
        refine ⟨32397070075264752159086983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43196093433686336212115977 32397070075264752159086983)
        ·
          refine ⟨48595605112897128238630475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32397070075264752159086983 48595605112897128238630475)
          ·
            refine ⟨72893407669345692357945713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48595605112897128238630475 72893407669345692357945713)
            ·
              refine ⟨54670055752009269268459285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72893407669345692357945713 54670055752009269268459285)
              ·
                refine ⟨2562658863375434496959029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54670055752009269268459285 2562658863375434496959029)
                ·
                  refine ⟨240249268441446984089909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2562658863375434496959029 240249268441446984089909)
                  ·
                    rfl

theorem cell23_4210954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 5].length) (baseStart_4210954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4210954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4210954 prefixEnd_4210954 := by exact prefixLift 4210954
  have htrace : WordTrace (prefixWord ++ tailWord_4210954) baseStart_4210954 baseEnd_4210954 := by
    simpa [prefixWord, tailWord_4210954, baseEnd_4210954] using wordTrace_append hprefix tailTrace_4210954
  have hstable : (prefixWord ++ tailWord_4210954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4210954).length < 2 ^ (prefixWord ++ tailWord_4210954).sum := by decide
  have hdescent : baseEnd_4210954 < baseStart_4210954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4210954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211004 : List Nat := [2, 2, 2, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_4211004 : Nat := 118140960795 + 4211004 * 2 ^ 59
def prefixEnd_4211004 : Nat := 4983230072969 + 3 ^ 40 * 4211004 * 2
def baseEnd_4211004 : Nat := 2162269090005747661183951

theorem tailTrace_4211004 : CollatzResearch.WordTrace tailWord_4211004 prefixEnd_4211004 2162269090005747661183951 := by
  unfold tailWord_4211004
  simp only [CollatzResearch.WordTrace]
  refine ⟨76793966818129582535644033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102391955757506110047525377 76793966818129582535644033)
  ·
    refine ⟨57595475113597186901733025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76793966818129582535644033 57595475113597186901733025)
    ·
      refine ⟨43196606335197890176299769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57595475113597186901733025 43196606335197890176299769)
      ·
        refine ⟨32397454751398417632224827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43196606335197890176299769 32397454751398417632224827)
        ·
          refine ⟨48596182127097626448337241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32397454751398417632224827 48596182127097626448337241)
          ·
            refine ⟨36447136595323219836252931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48596182127097626448337241 36447136595323219836252931)
            ·
              refine ⟨54670704892984829754379397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36447136595323219836252931 54670704892984829754379397)
              ·
                refine ⟨10250757167434655578946137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54670704892984829754379397 10250757167434655578946137)
                ·
                  refine ⟨7688067875575991684209603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10250757167434655578946137 7688067875575991684209603)
                  ·
                    refine ⟨11532101813363987526314405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7688067875575991684209603 11532101813363987526314405)
                    ·
                      refine ⟨2162269090005747661183951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11532101813363987526314405 2162269090005747661183951)
                      ·
                        rfl

theorem cell23_4211004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_4211004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211004 prefixEnd_4211004 := by exact prefixLift 4211004
  have htrace : WordTrace (prefixWord ++ tailWord_4211004) baseStart_4211004 baseEnd_4211004 := by
    simpa [prefixWord, tailWord_4211004, baseEnd_4211004] using wordTrace_append hprefix tailTrace_4211004
  have hstable : (prefixWord ++ tailWord_4211004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211004).length < 2 ^ (prefixWord ++ tailWord_4211004).sum := by decide
  have hdescent : baseEnd_4211004 < baseStart_4211004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211007 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 5]
def baseStart_4211007 : Nat := 118140960795 + 4211007 * 2 ^ 59
def prefixEnd_4211007 : Nat := 4983230072969 + 3 ^ 40 * 4211007 * 2
def baseEnd_4211007 : Nat := 2162270630447711149446437

theorem tailTrace_4211007 : CollatzResearch.WordTrace tailWord_4211007 prefixEnd_4211007 2162270630447711149446437 := by
  unfold tailWord_4211007
  simp only [CollatzResearch.WordTrace]
  refine ⟨153588043055248296583647275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102392028703498864389098183 153588043055248296583647275)
  ·
    refine ⟨230382064582872444875470913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153588043055248296583647275 230382064582872444875470913)
    ·
      refine ⟨172786548437154333656603185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230382064582872444875470913 172786548437154333656603185)
      ·
        refine ⟨129589911327865750242452389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172786548437154333656603185 129589911327865750242452389)
        ·
          refine ⟨24298108373974828170459823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129589911327865750242452389 24298108373974828170459823)
          ·
            refine ⟨36447162560962242255689735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24298108373974828170459823 36447162560962242255689735)
            ·
              refine ⟨54670743841443363383534603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36447162560962242255689735 54670743841443363383534603)
              ·
                refine ⟨82006115762165045075301905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54670743841443363383534603 82006115762165045075301905)
                ·
                  refine ⟨61504586821623783806476429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82006115762165045075301905 61504586821623783806476429)
                  ·
                    refine ⟨23064220058108918927428661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61504586821623783806476429 23064220058108918927428661)
                    ·
                      refine ⟨2162270630447711149446437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23064220058108918927428661 2162270630447711149446437)
                      ·
                        rfl

theorem cell23_4211007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_4211007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211007 prefixEnd_4211007 := by exact prefixLift 4211007
  have htrace : WordTrace (prefixWord ++ tailWord_4211007) baseStart_4211007 baseEnd_4211007 := by
    simpa [prefixWord, tailWord_4211007, baseEnd_4211007] using wordTrace_append hprefix tailTrace_4211007
  have hstable : (prefixWord ++ tailWord_4211007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211007).length < 2 ^ (prefixWord ++ tailWord_4211007).sum := by decide
  have hdescent : baseEnd_4211007 < baseStart_4211007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211017 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 2, 4, 4]
def baseStart_4211017 : Nat := 118140960795 + 4211017 * 2 ^ 59
def prefixEnd_4211017 : Nat := 4983230072969 + 3 ^ 40 * 4211017 * 2
def baseEnd_4211017 : Nat := 2162275765254256110321391

theorem tailTrace_4211017 : CollatzResearch.WordTrace tailWord_4211017 prefixEnd_4211017 2162275765254256110321391 := by
  unfold tailWord_4211017
  simp only [CollatzResearch.WordTrace]
  refine ⟨153588407785212068291511305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102392271856808045527674203 153588407785212068291511305)
  ·
    refine ⟨115191305838909051218633479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153588407785212068291511305 115191305838909051218633479)
    ·
      refine ⟨172786958758363576827950219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115191305838909051218633479 172786958758363576827950219)
      ·
        refine ⟨259180438137545365241925329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172786958758363576827950219 259180438137545365241925329)
        ·
          refine ⟨194385328603159023931443997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259180438137545365241925329 194385328603159023931443997)
          ·
            refine ⟨72894498226184633974291499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 194385328603159023931443997 72894498226184633974291499)
            ·
              refine ⟨109341747339276950961437249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72894498226184633974291499 109341747339276950961437249)
              ·
                refine ⟨82006310504457713221077937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109341747339276950961437249 82006310504457713221077937)
                ·
                  refine ⟨61504732878343284915808453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82006310504457713221077937 61504732878343284915808453)
                  ·
                    refine ⟨11532137414689365921714085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61504732878343284915808453 11532137414689365921714085)
                    ·
                      refine ⟨2162275765254256110321391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11532137414689365921714085 2162275765254256110321391)
                      ·
                        rfl

theorem cell23_4211017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_4211017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211017 prefixEnd_4211017 := by exact prefixLift 4211017
  have htrace : WordTrace (prefixWord ++ tailWord_4211017) baseStart_4211017 baseEnd_4211017 := by
    simpa [prefixWord, tailWord_4211017, baseEnd_4211017] using wordTrace_append hprefix tailTrace_4211017
  have hstable : (prefixWord ++ tailWord_4211017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211017).length < 2 ^ (prefixWord ++ tailWord_4211017).sum := by decide
  have hdescent : baseEnd_4211017 < baseStart_4211017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211048 : List Nat := [2, 1, 4, 2, 2, 1, 1, 5, 1, 4]
def baseStart_4211048 : Nat := 118140960795 + 4211048 * 2 ^ 59
def prefixEnd_4211048 : Nat := 4983230072969 + 3 ^ 40 * 4211048 * 2
def baseEnd_4211048 : Nat := 720763894384848496344583

theorem tailTrace_4211048 : CollatzResearch.WordTrace tailWord_4211048 prefixEnd_4211048 720763894384848496344583 := by
  unfold tailWord_4211048
  simp only [CollatzResearch.WordTrace]
  refine ⟨76794769224049880292944899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102393025632066507057259865 76794769224049880292944899)
  ·
    refine ⟨115192153836074820439417349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76794769224049880292944899 115192153836074820439417349)
    ·
      refine ⟨21598528844264028832390753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115192153836074820439417349 21598528844264028832390753)
      ·
        refine ⟨16198896633198021624293065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21598528844264028832390753 16198896633198021624293065)
        ·
          refine ⟨12149172474898516218219799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16198896633198021624293065 12149172474898516218219799)
          ·
            refine ⟨18223758712347774327329699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12149172474898516218219799 18223758712347774327329699)
            ·
              refine ⟨27335638068521661490994549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18223758712347774327329699 27335638068521661490994549)
              ·
                refine ⟨2562716068923905764780739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27335638068521661490994549 2562716068923905764780739)
                ·
                  refine ⟨3844074103385858647171109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562716068923905764780739 3844074103385858647171109)
                  ·
                    refine ⟨720763894384848496344583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3844074103385858647171109 720763894384848496344583)
                    ·
                      rfl

theorem cell23_4211048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_4211048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211048 prefixEnd_4211048 := by exact prefixLift 4211048
  have htrace : WordTrace (prefixWord ++ tailWord_4211048) baseStart_4211048 baseEnd_4211048 := by
    simpa [prefixWord, tailWord_4211048, baseEnd_4211048] using wordTrace_append hprefix tailTrace_4211048
  have hstable : (prefixWord ++ tailWord_4211048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211048).length < 2 ^ (prefixWord ++ tailWord_4211048).sum := by decide
  have hdescent : baseEnd_4211048 < baseStart_4211048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211061 : List Nat := [1, 3, 4, 1, 2, 1, 3, 2, 6]
def baseStart_4211061 : Nat := 118140960795 + 4211061 * 2 ^ 59
def prefixEnd_4211061 : Nat := 4983230072969 + 3 ^ 40 * 4211061 * 2
def baseEnd_4211061 : Nat := 240255373155894882019021

theorem tailTrace_4211061 : CollatzResearch.WordTrace tailWord_4211061 prefixEnd_4211061 240255373155894882019021 := by
  unfold tailWord_4211061
  simp only [CollatzResearch.WordTrace]
  refine ⟨153590012597052663806113037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102393341731368442537408691 153590012597052663806113037)
  ·
    refine ⟨57596254723894748927292389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153590012597052663806113037 57596254723894748927292389)
    ·
      refine ⟨10799297760730265423867323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57596254723894748927292389 10799297760730265423867323)
      ·
        refine ⟨16198946641095398135800985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10799297760730265423867323 16198946641095398135800985)
        ·
          refine ⟨12149209980821548601850739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16198946641095398135800985 12149209980821548601850739)
          ·
            refine ⟨18223814971232322902776109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12149209980821548601850739 18223814971232322902776109)
            ·
              refine ⟨6833930614212121088541041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18223814971232322902776109 6833930614212121088541041)
              ·
                refine ⟨5125447960659090816405781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6833930614212121088541041 5125447960659090816405781)
                ·
                  refine ⟨240255373155894882019021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5125447960659090816405781 240255373155894882019021)
                  ·
                    rfl

theorem cell23_4211061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 6].length) (baseStart_4211061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211061 prefixEnd_4211061 := by exact prefixLift 4211061
  have htrace : WordTrace (prefixWord ++ tailWord_4211061) baseStart_4211061 baseEnd_4211061 := by
    simpa [prefixWord, tailWord_4211061, baseEnd_4211061] using wordTrace_append hprefix tailTrace_4211061
  have hstable : (prefixWord ++ tailWord_4211061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211061).length < 2 ^ (prefixWord ++ tailWord_4211061).sum := by decide
  have hdescent : baseEnd_4211061 < baseStart_4211061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211081 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 1, 5, 2]
def baseStart_4211081 : Nat := 118140960795 + 4211081 * 2 ^ 59
def prefixEnd_4211081 : Nat := 4983230072969 + 3 ^ 40 * 4211081 * 2
def baseEnd_4211081 : Nat := 2162308628016143859921097

theorem tailTrace_4211081 : CollatzResearch.WordTrace tailWord_4211081 prefixEnd_4211081 2162308628016143859921097 := by
  unfold tailWord_4211081
  simp only [CollatzResearch.WordTrace]
  refine ⟨153590742056980207221841097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102393828037986804814560731 153590742056980207221841097)
  ·
    refine ⟨115193056542735155416380823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153590742056980207221841097 115193056542735155416380823)
    ·
      refine ⟨172789584814102733124571235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115193056542735155416380823 172789584814102733124571235)
      ·
        refine ⟨259184377221154099686856853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172789584814102733124571235 259184377221154099686856853)
        ·
          refine ⟨12149267682241598422821415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 259184377221154099686856853 12149267682241598422821415)
          ·
            refine ⟨18223901523362397634232123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12149267682241598422821415 18223901523362397634232123)
            ·
              refine ⟨27335852285043596451348185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18223901523362397634232123 27335852285043596451348185)
              ·
                refine ⟨20501889213782697338511139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27335852285043596451348185 20501889213782697338511139)
                ·
                  refine ⟨30752833820674046007766709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20501889213782697338511139 30752833820674046007766709)
                  ·
                    refine ⟨2883078170688191813228129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30752833820674046007766709 2883078170688191813228129)
                    ·
                      refine ⟨2162308628016143859921097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2883078170688191813228129 2162308628016143859921097)
                      ·
                        rfl

theorem cell23_4211081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 5, 2].length) (baseStart_4211081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211081 prefixEnd_4211081 := by exact prefixLift 4211081
  have htrace : WordTrace (prefixWord ++ tailWord_4211081) baseStart_4211081 baseEnd_4211081 := by
    simpa [prefixWord, tailWord_4211081, baseEnd_4211081] using wordTrace_append hprefix tailTrace_4211081
  have hstable : (prefixWord ++ tailWord_4211081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211081).length < 2 ^ (prefixWord ++ tailWord_4211081).sum := by decide
  have hdescent : baseEnd_4211081 < baseStart_4211081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211121 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 4, 4]
def baseStart_4211121 : Nat := 118140960795 + 4211121 * 2 ^ 59
def prefixEnd_4211121 : Nat := 4983230072969 + 3 ^ 40 * 4211121 * 2
def baseEnd_4211121 : Nat := 720776389080774567806971

theorem tailTrace_4211121 : CollatzResearch.WordTrace tailWord_4211121 prefixEnd_4211121 720776389080774567806971 := by
  unfold tailWord_4211121
  simp only [CollatzResearch.WordTrace]
  refine ⟨153592200976835294053297217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102394800651223529368864811 153592200976835294053297217)
  ·
    refine ⟨115194150732626470539972913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153592200976835294053297217 115194150732626470539972913)
    ·
      refine ⟨86395613049469852904979685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115194150732626470539972913 86395613049469852904979685)
      ·
        refine ⟨16199177446775597419683691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86395613049469852904979685 16199177446775597419683691)
        ·
          refine ⟨24298766170163396129525537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16199177446775597419683691 24298766170163396129525537)
          ·
            refine ⟨18224074627622547097144153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24298766170163396129525537 18224074627622547097144153)
            ·
              refine ⟨13668055970716910322858115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18224074627622547097144153 13668055970716910322858115)
              ·
                refine ⟨20502083956075365484287173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13668055970716910322858115 20502083956075365484287173)
                ·
                  refine ⟨3844140741764131028303845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20502083956075365484287173 3844140741764131028303845)
                  ·
                    refine ⟨720776389080774567806971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3844140741764131028303845 720776389080774567806971)
                    ·
                      rfl

theorem cell23_4211121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_4211121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211121 prefixEnd_4211121 := by exact prefixLift 4211121
  have htrace : WordTrace (prefixWord ++ tailWord_4211121) baseStart_4211121 baseEnd_4211121 := by
    simpa [prefixWord, tailWord_4211121, baseEnd_4211121] using wordTrace_append hprefix tailTrace_4211121
  have hstable : (prefixWord ++ tailWord_4211121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211121).length < 2 ^ (prefixWord ++ tailWord_4211121).sum := by decide
  have hdescent : baseEnd_4211121 < baseStart_4211121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211134 : List Nat := [4, 2, 1, 1, 1, 1, 3, 10]
def baseStart_4211134 : Nat := 118140960795 + 4211134 * 2 ^ 59
def prefixEnd_4211134 : Nat := 4983230072969 + 3 ^ 40 * 4211134 * 2
def baseEnd_4211134 : Nat := 80086512684845635279939

theorem tailTrace_4211134 : CollatzResearch.WordTrace tailWord_4211134 prefixEnd_4211134 80086512684845635279939 := by
  unfold tailWord_4211134
  simp only [CollatzResearch.WordTrace]
  refine ⟨19199084390723524659190057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102395116750525464849013637 19199084390723524659190057)
  ·
    refine ⟨14399313293042643494392543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19199084390723524659190057 14399313293042643494392543)
    ·
      refine ⟨21598969939563965241588815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14399313293042643494392543 21598969939563965241588815)
      ·
        refine ⟨32398454909345947862383223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21598969939563965241588815 32398454909345947862383223)
        ·
          refine ⟨48597682364018921793574835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32398454909345947862383223 48597682364018921793574835)
          ·
            refine ⟨72896523546028382690362253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48597682364018921793574835 72896523546028382690362253)
            ·
              refine ⟨27336196329760643508885845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72896523546028382690362253 27336196329760643508885845)
              ·
                refine ⟨80086512684845635279939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 27336196329760643508885845 80086512684845635279939)
                ·
                  rfl

theorem cell23_4211134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 10].length) (baseStart_4211134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211134 prefixEnd_4211134 := by exact prefixLift 4211134
  have htrace : WordTrace (prefixWord ++ tailWord_4211134) baseStart_4211134 baseEnd_4211134 := by
    simpa [prefixWord, tailWord_4211134, baseEnd_4211134] using wordTrace_append hprefix tailTrace_4211134
  have hstable : (prefixWord ++ tailWord_4211134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211134).length < 2 ^ (prefixWord ++ tailWord_4211134).sum := by decide
  have hdescent : baseEnd_4211134 < baseStart_4211134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211148 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 3, 2, 3]
def baseStart_4211148 : Nat := 118140960795 + 4211148 * 2 ^ 59
def prefixEnd_4211148 : Nat := 4983230072969 + 3 ^ 40 * 4211148 * 2
def baseEnd_4211148 : Nat := 2162343031219995097783289

theorem tailTrace_4211148 : CollatzResearch.WordTrace tailWord_4211148 prefixEnd_4211148 2162343031219995097783289 := by
  unfold tailWord_4211148
  simp only [CollatzResearch.WordTrace]
  refine ⟨76796592873868738832265049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102395457165158318443020065 76796592873868738832265049)
  ·
    refine ⟨57597444655401554124198787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76796592873868738832265049 57597444655401554124198787)
    ·
      refine ⟨86396166983102331186298181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57597444655401554124198787 86396166983102331186298181)
      ·
        refine ⟨16199281309331687097430909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86396166983102331186298181 16199281309331687097430909)
        ·
          refine ⟨6074730490999382661536591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16199281309331687097430909 6074730490999382661536591)
          ·
            refine ⟨9112095736499073992304887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6074730490999382661536591 9112095736499073992304887)
            ·
              refine ⟨13668143604748610988457331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9112095736499073992304887 13668143604748610988457331)
              ·
                refine ⟨20502215407122916482685997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13668143604748610988457331 20502215407122916482685997)
                ·
                  refine ⟨7688330777671093681007249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20502215407122916482685997 7688330777671093681007249)
                  ·
                    refine ⟨5766248083253320260755437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7688330777671093681007249 5766248083253320260755437)
                    ·
                      refine ⟨2162343031219995097783289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5766248083253320260755437 2162343031219995097783289)
                      ·
                        rfl

theorem cell23_4211148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_4211148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211148 prefixEnd_4211148 := by exact prefixLift 4211148
  have htrace : WordTrace (prefixWord ++ tailWord_4211148) baseStart_4211148 baseEnd_4211148 := by
    simpa [prefixWord, tailWord_4211148, baseEnd_4211148] using wordTrace_append hprefix tailTrace_4211148
  have hstable : (prefixWord ++ tailWord_4211148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211148).length < 2 ^ (prefixWord ++ tailWord_4211148).sum := by decide
  have hdescent : baseEnd_4211148 < baseStart_4211148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211158 : List Nat := [5, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_4211158 : Nat := 118140960795 + 4211158 * 2 ^ 59
def prefixEnd_4211158 : Nat := 4983230072969 + 3 ^ 40 * 4211158 * 2
def baseEnd_4211158 : Nat := 2162348166026540058658243

theorem tailTrace_4211158 : CollatzResearch.WordTrace tailWord_4211158 prefixEnd_4211158 2162348166026540058658243 := by
  unfold tailWord_4211158
  simp only [CollatzResearch.WordTrace]
  refine ⟨9599596904856328085774633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102395700318467499581596085 9599596904856328085774633)
  ·
    refine ⟨7199697678642246064330975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9599596904856328085774633 7199697678642246064330975)
    ·
      refine ⟨10799546517963369096496463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7199697678642246064330975 10799546517963369096496463)
      ·
        refine ⟨16199319776945053644744695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10799546517963369096496463 16199319776945053644744695)
        ·
          refine ⟨24298979665417580467117043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16199319776945053644744695 24298979665417580467117043)
          ·
            refine ⟨36448469498126370700675565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24298979665417580467117043 36448469498126370700675565)
            ·
              refine ⟨13668176061797389012753337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36448469498126370700675565 13668176061797389012753337)
              ·
                refine ⟨10251132046348041759565003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13668176061797389012753337 10251132046348041759565003)
                ·
                  refine ⟨15376698069522062639347505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10251132046348041759565003 15376698069522062639347505)
                  ·
                    refine ⟨11532523552141546979510629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15376698069522062639347505 11532523552141546979510629)
                    ·
                      refine ⟨2162348166026540058658243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11532523552141546979510629 2162348166026540058658243)
                      ·
                        rfl

theorem cell23_4211158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_4211158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211158 prefixEnd_4211158 := by exact prefixLift 4211158
  have htrace : WordTrace (prefixWord ++ tailWord_4211158) baseStart_4211158 baseEnd_4211158 := by
    simpa [prefixWord, tailWord_4211158, baseEnd_4211158] using wordTrace_append hprefix tailTrace_4211158
  have hstable : (prefixWord ++ tailWord_4211158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211158).length < 2 ^ (prefixWord ++ tailWord_4211158).sum := by decide
  have hdescent : baseEnd_4211158 < baseStart_4211158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211161 : List Nat := [1, 2, 1, 2, 4, 1, 3, 2, 1, 3, 3]
def baseStart_4211161 : Nat := 118140960795 + 4211161 * 2 ^ 59
def prefixEnd_4211161 : Nat := 4983230072969 + 3 ^ 40 * 4211161 * 2
def baseEnd_4211161 : Nat := 2162349706468503546920729

theorem tailTrace_4211161 : CollatzResearch.WordTrace tailWord_4211161 prefixEnd_4211161 2162349706468503546920729 := by
  unfold tailWord_4211161
  simp only [CollatzResearch.WordTrace]
  refine ⟨153593659896690380884753337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102395773264460253923168891 153593659896690380884753337)
  ·
    refine ⟨115195244922517785663565003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153593659896690380884753337 115195244922517785663565003)
    ·
      refine ⟨172792867383776678495347505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115195244922517785663565003 172792867383776678495347505)
      ·
        refine ⟨129594650537832508871510629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172792867383776678495347505 129594650537832508871510629)
        ·
          refine ⟨24298996975843595413408243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129594650537832508871510629 24298996975843595413408243)
          ·
            refine ⟨36448495463765393120112365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24298996975843595413408243 36448495463765393120112365)
            ·
              refine ⟨13668185798912022420042137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36448495463765393120112365 13668185798912022420042137)
              ·
                refine ⟨10251139349184016815031603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13668185798912022420042137 10251139349184016815031603)
                ·
                  refine ⟨15376709023776025222547405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10251139349184016815031603 15376709023776025222547405)
                  ·
                    refine ⟨5766265883916009458455277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15376709023776025222547405 5766265883916009458455277)
                    ·
                      refine ⟨2162349706468503546920729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5766265883916009458455277 2162349706468503546920729)
                      ·
                        rfl

theorem cell23_4211161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_4211161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211161 prefixEnd_4211161 := by exact prefixLift 4211161
  have htrace : WordTrace (prefixWord ++ tailWord_4211161) baseStart_4211161 baseEnd_4211161 := by
    simpa [prefixWord, tailWord_4211161, baseEnd_4211161] using wordTrace_append hprefix tailTrace_4211161
  have hstable : (prefixWord ++ tailWord_4211161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211161).length < 2 ^ (prefixWord ++ tailWord_4211161).sum := by decide
  have hdescent : baseEnd_4211161 < baseStart_4211161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211165 : List Nat := [1, 4, 3, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_4211165 : Nat := 118140960795 + 4211165 * 2 ^ 59
def prefixEnd_4211165 : Nat := 4983230072969 + 3 ^ 40 * 4211165 * 2
def baseEnd_4211165 : Nat := 2162351760391121531270711

theorem tailTrace_4211165 : CollatzResearch.WordTrace tailWord_4211165 prefixEnd_4211165 2162351760391121531270711 := by
  unfold tailWord_4211165
  simp only [CollatzResearch.WordTrace]
  refine ⟨153593805788675889567898949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102395870525783926378599299 153593805788675889567898949)
  ·
    refine ⟨28798838585376729293981053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153593805788675889567898949 28798838585376729293981053)
    ·
      refine ⟨10799564469516273485242895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28798838585376729293981053 10799564469516273485242895)
      ·
        refine ⟨16199346704274410227864343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10799564469516273485242895 16199346704274410227864343)
        ·
          refine ⟨24299020056411615341796515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16199346704274410227864343 24299020056411615341796515)
          ·
            refine ⟨36448530084617423012694773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24299020056411615341796515 36448530084617423012694773)
            ·
              refine ⟨3417049695432883407440135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36448530084617423012694773 3417049695432883407440135)
              ·
                refine ⟨5125574543149325111160203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3417049695432883407440135 5125574543149325111160203)
                ·
                  refine ⟨7688361814723987666740305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5125574543149325111160203 7688361814723987666740305)
                  ·
                    refine ⟨5766271361042990750055229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7688361814723987666740305 5766271361042990750055229)
                    ·
                      refine ⟨2162351760391121531270711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5766271361042990750055229 2162351760391121531270711)
                      ·
                        rfl

theorem cell23_4211165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_4211165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211165 prefixEnd_4211165 := by exact prefixLift 4211165
  have htrace : WordTrace (prefixWord ++ tailWord_4211165) baseStart_4211165 baseEnd_4211165 := by
    simpa [prefixWord, tailWord_4211165, baseEnd_4211165] using wordTrace_append hprefix tailTrace_4211165
  have hstable : (prefixWord ++ tailWord_4211165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211165).length < 2 ^ (prefixWord ++ tailWord_4211165).sum := by decide
  have hdescent : baseEnd_4211165 < baseStart_4211165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211181 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_4211181 : Nat := 118140960795 + 4211181 * 2 ^ 59
def prefixEnd_4211181 : Nat := 4983230072969 + 3 ^ 40 * 4211181 * 2
def baseEnd_4211181 : Nat := 720786658693864489556879

theorem tailTrace_4211181 : CollatzResearch.WordTrace tailWord_4211181 prefixEnd_4211181 720786658693864489556879 := by
  unfold tailWord_4211181
  simp only [CollatzResearch.WordTrace]
  refine ⟨153594389356617924300481397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102396259571078616200320931 153594389356617924300481397)
  ·
    refine ⟨14399474002182930403170131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153594389356617924300481397 14399474002182930403170131)
    ·
      refine ⟨21599211003274395604755197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14399474002182930403170131 21599211003274395604755197)
      ·
        refine ⟨8099704126227898351783199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21599211003274395604755197 8099704126227898351783199)
        ·
          refine ⟨12149556189341847527674799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8099704126227898351783199 12149556189341847527674799)
          ·
            refine ⟨18224334284012771291512199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12149556189341847527674799 18224334284012771291512199)
            ·
              refine ⟨27336501426019156937268299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18224334284012771291512199 27336501426019156937268299)
              ·
                refine ⟨41004752139028735405902449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27336501426019156937268299 41004752139028735405902449)
                ·
                  refine ⟨30753564104271551554426837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41004752139028735405902449 30753564104271551554426837)
                  ·
                    refine ⟨720786658693864489556879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30753564104271551554426837 720786658693864489556879)
                    ·
                      rfl

theorem cell23_4211181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_4211181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211181 prefixEnd_4211181 := by exact prefixLift 4211181
  have htrace : WordTrace (prefixWord ++ tailWord_4211181) baseStart_4211181 baseEnd_4211181 := by
    simpa [prefixWord, tailWord_4211181, baseEnd_4211181] using wordTrace_append hprefix tailTrace_4211181
  have hstable : (prefixWord ++ tailWord_4211181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211181).length < 2 ^ (prefixWord ++ tailWord_4211181).sum := by decide
  have hdescent : baseEnd_4211181 < baseStart_4211181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211184 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 4]
def baseStart_4211184 : Nat := 118140960795 + 4211184 * 2 ^ 59
def prefixEnd_4211184 : Nat := 4983230072969 + 3 ^ 40 * 4211184 * 2
def baseEnd_4211184 : Nat := 2162361516523556956933123

theorem tailTrace_4211184 : CollatzResearch.WordTrace tailWord_4211184 prefixEnd_4211184 2162361516523556956933123 := by
  unfold tailWord_4211184
  simp only [CollatzResearch.WordTrace]
  refine ⟨76797249387803527906420303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102396332517071370541893737 76797249387803527906420303)
  ·
    refine ⟨115195874081705291859630455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76797249387803527906420303 115195874081705291859630455)
    ·
      refine ⟨172793811122557937789445683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115195874081705291859630455 172793811122557937789445683)
      ·
        refine ⟨259190716683836906684168525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172793811122557937789445683 259190716683836906684168525)
        ·
          refine ⟨97196518756438840006563197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259190716683836906684168525 97196518756438840006563197)
          ·
            refine ⟨36448694533664565002461199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97196518756438840006563197 36448694533664565002461199)
            ·
              refine ⟨54673041800496847503691799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36448694533664565002461199 54673041800496847503691799)
              ·
                refine ⟨82009562700745271255537699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54673041800496847503691799 82009562700745271255537699)
                ·
                  refine ⟨123014344051117906883306549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82009562700745271255537699 123014344051117906883306549)
                  ·
                    refine ⟨11532594754792303770309989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 123014344051117906883306549 11532594754792303770309989)
                    ·
                      refine ⟨2162361516523556956933123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11532594754792303770309989 2162361516523556956933123)
                      ·
                        rfl

theorem cell23_4211184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_4211184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211184 prefixEnd_4211184 := by exact prefixLift 4211184
  have htrace : WordTrace (prefixWord ++ tailWord_4211184) baseStart_4211184 baseEnd_4211184 := by
    simpa [prefixWord, tailWord_4211184, baseEnd_4211184] using wordTrace_append hprefix tailTrace_4211184
  have hstable : (prefixWord ++ tailWord_4211184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211184).length < 2 ^ (prefixWord ++ tailWord_4211184).sum := by decide
  have hdescent : baseEnd_4211184 < baseStart_4211184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211235 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 4, 2, 2]
def baseStart_4211235 : Nat := 118140960795 + 4211235 * 2 ^ 59
def prefixEnd_4211235 : Nat := 4983230072969 + 3 ^ 40 * 4211235 * 2
def baseEnd_4211235 : Nat := 2162387704036936257395389

theorem tailTrace_4211235 : CollatzResearch.WordTrace tailWord_4211235 prefixEnd_4211235 2162387704036936257395389 := by
  unfold tailWord_4211235
  simp only [CollatzResearch.WordTrace]
  refine ⟨153596358898422291522947159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102397572598948194348631439 153596358898422291522947159)
  ·
    refine ⟨230394538347633437284420739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153596358898422291522947159 230394538347633437284420739)
    ·
      refine ⟨345591807521450155926631109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230394538347633437284420739 345591807521450155926631109)
      ·
        refine ⟨64798463910271904236243333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 345591807521450155926631109 64798463910271904236243333)
        ·
          refine ⟨12149711983175982044295625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64798463910271904236243333 12149711983175982044295625)
          ·
            refine ⟨9112283987381986533221719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12149711983175982044295625 9112283987381986533221719)
            ·
              refine ⟨13668425981072979799832579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9112283987381986533221719 13668425981072979799832579)
              ·
                refine ⟨20502638971609469699748869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13668425981072979799832579 20502638971609469699748869)
                ·
                  refine ⟨3844244807176775568702913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20502638971609469699748869 3844244807176775568702913)
                  ·
                    refine ⟨2883183605382581676527185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3844244807176775568702913 2883183605382581676527185)
                    ·
                      refine ⟨2162387704036936257395389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2883183605382581676527185 2162387704036936257395389)
                      ·
                        rfl

theorem cell23_4211235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_4211235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211235 prefixEnd_4211235 := by exact prefixLift 4211235
  have htrace : WordTrace (prefixWord ++ tailWord_4211235) baseStart_4211235 baseEnd_4211235 := by
    simpa [prefixWord, tailWord_4211235, baseEnd_4211235] using wordTrace_append hprefix tailTrace_4211235
  have hstable : (prefixWord ++ tailWord_4211235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211235).length < 2 ^ (prefixWord ++ tailWord_4211235).sum := by decide
  have hdescent : baseEnd_4211235 < baseStart_4211235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211251 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 3]
def baseStart_4211251 : Nat := 118140960795 + 4211251 * 2 ^ 59
def prefixEnd_4211251 : Nat := 4983230072969 + 3 ^ 40 * 4211251 * 2
def baseEnd_4211251 : Nat := 2162395919727408194795315

theorem tailTrace_4211251 : CollatzResearch.WordTrace tailWord_4211251 prefixEnd_4211251 2162395919727408194795315 := by
  unfold tailWord_4211251
  simp only [CollatzResearch.WordTrace]
  refine ⟨153596942466364326255529607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102397961644242884170353071 153596942466364326255529607)
  ·
    refine ⟨230395413699546489383294411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153596942466364326255529607 230395413699546489383294411)
    ·
      refine ⟨345593120549319734074941617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230395413699546489383294411 345593120549319734074941617)
      ·
        refine ⟨259194840411989800556206213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345593120549319734074941617 259194840411989800556206213)
        ·
          refine ⟨48599032577248087604288665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 259194840411989800556206213 48599032577248087604288665)
          ·
            refine ⟨36449274432936065703216499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48599032577248087604288665 36449274432936065703216499)
            ·
              refine ⟨54673911649404098554824749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36449274432936065703216499 54673911649404098554824749)
              ·
                refine ⟨20502716868526536958059281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54673911649404098554824749 20502716868526536958059281)
                ·
                  refine ⟨15377037651394902718544461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20502716868526536958059281 15377037651394902718544461)
                  ·
                    refine ⟨5766389119273088519454173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15377037651394902718544461 5766389119273088519454173)
                    ·
                      refine ⟨2162395919727408194795315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5766389119273088519454173 2162395919727408194795315)
                      ·
                        rfl

theorem cell23_4211251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 3].length) (baseStart_4211251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211251 prefixEnd_4211251 := by exact prefixLift 4211251
  have htrace : WordTrace (prefixWord ++ tailWord_4211251) baseStart_4211251 baseEnd_4211251 := by
    simpa [prefixWord, tailWord_4211251, baseEnd_4211251] using wordTrace_append hprefix tailTrace_4211251
  have hstable : (prefixWord ++ tailWord_4211251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211251).length < 2 ^ (prefixWord ++ tailWord_4211251).sum := by decide
  have hdescent : baseEnd_4211251 < baseStart_4211251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211271 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 1, 7]
def baseStart_4211271 : Nat := 118140960795 + 4211271 * 2 ^ 59
def prefixEnd_4211271 : Nat := 4983230072969 + 3 ^ 40 * 4211271 * 2
def baseEnd_4211271 : Nat := 720802063113499372181741

theorem tailTrace_4211271 : CollatzResearch.WordTrace tailWord_4211271 prefixEnd_4211271 720802063113499372181741 := by
  unfold tailWord_4211271
  simp only [CollatzResearch.WordTrace]
  refine ⟨153597671926291869671257667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102398447950861246447505111 153597671926291869671257667)
  ·
    refine ⟨230396507889437804506886501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153597671926291869671257667 230396507889437804506886501)
    ·
      refine ⟨43199345229269588345041219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230396507889437804506886501 43199345229269588345041219)
      ·
        refine ⟨64799017843904382517561829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43199345229269588345041219 64799017843904382517561829)
        ·
          refine ⟨12149815845732071722042843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64799017843904382517561829 12149815845732071722042843)
          ·
            refine ⟨18224723768598107583064265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12149815845732071722042843 18224723768598107583064265)
            ·
              refine ⟨13668542826448580687298199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18224723768598107583064265 13668542826448580687298199)
              ·
                refine ⟨20502814239672871030947299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13668542826448580687298199 20502814239672871030947299)
                ·
                  refine ⟨30754221359509306546420949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20502814239672871030947299 30754221359509306546420949)
                  ·
                    refine ⟨720802063113499372181741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30754221359509306546420949 720802063113499372181741)
                    ·
                      rfl

theorem cell23_4211271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_4211271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211271 prefixEnd_4211271 := by exact prefixLift 4211271
  have htrace : WordTrace (prefixWord ++ tailWord_4211271) baseStart_4211271 baseEnd_4211271 := by
    simpa [prefixWord, tailWord_4211271, baseEnd_4211271] using wordTrace_append hprefix tailTrace_4211271
  have hstable : (prefixWord ++ tailWord_4211271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211271).length < 2 ^ (prefixWord ++ tailWord_4211271).sum := by decide
  have hdescent : baseEnd_4211271 < baseStart_4211271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211292 : List Nat := [2, 2, 4, 1, 3, 1, 3, 2, 5]
def baseStart_4211292 : Nat := 118140960795 + 4211292 * 2 ^ 59
def prefixEnd_4211292 : Nat := 4983230072969 + 3 ^ 40 * 4211292 * 2
def baseEnd_4211292 : Nat := 240268552492693614931403

theorem tailTrace_4211292 : CollatzResearch.WordTrace tailWord_4211292 prefixEnd_4211292 240268552492693614931403 := by
  unfold tailWord_4211292
  simp only [CollatzResearch.WordTrace]
  refine ⟨76799218929607895128886065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102398958572810526838514753 76799218929607895128886065)
  ·
    refine ⟨57599414197205921346664549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76799218929607895128886065 57599414197205921346664549)
    ·
      refine ⟨10799890161976110252499603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57599414197205921346664549 10799890161976110252499603)
      ·
        refine ⟨16199835242964165378749405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10799890161976110252499603 16199835242964165378749405)
        ·
          refine ⟨6074938216111562017031027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16199835242964165378749405 6074938216111562017031027)
          ·
            refine ⟨9112407324167343025546541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6074938216111562017031027 9112407324167343025546541)
            ·
              refine ⟨3417152746562753634579953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9112407324167343025546541 3417152746562753634579953)
              ·
                refine ⟨2562864559922065225934965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3417152746562753634579953 2562864559922065225934965)
                ·
                  refine ⟨240268552492693614931403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2562864559922065225934965 240268552492693614931403)
                  ·
                    rfl

theorem cell23_4211292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 5].length) (baseStart_4211292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211292 prefixEnd_4211292 := by exact prefixLift 4211292
  have htrace : WordTrace (prefixWord ++ tailWord_4211292) baseStart_4211292 baseEnd_4211292 := by
    simpa [prefixWord, tailWord_4211292, baseEnd_4211292] using wordTrace_append hprefix tailTrace_4211292
  have hstable : (prefixWord ++ tailWord_4211292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211292).length < 2 ^ (prefixWord ++ tailWord_4211292).sum := by decide
  have hdescent : baseEnd_4211292 < baseStart_4211292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211308 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 2, 4, 2]
def baseStart_4211308 : Nat := 118140960795 + 4211308 * 2 ^ 59
def prefixEnd_4211308 : Nat := 4983230072969 + 3 ^ 40 * 4211308 * 2
def baseEnd_4211308 : Nat := 2162425188124714471782553

theorem tailTrace_4211308 : CollatzResearch.WordTrace tailWord_4211308 prefixEnd_4211308 2162425188124714471782553 := by
  unfold tailWord_4211308
  simp only [CollatzResearch.WordTrace]
  refine ⟨76799510713578912495177289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102399347618105216660236385 76799510713578912495177289)
  ·
    refine ⟨57599633035184184371382967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76799510713578912495177289 57599633035184184371382967)
    ·
      refine ⟨86399449552776276557074451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57599633035184184371382967 86399449552776276557074451)
      ·
        refine ⟨129599174329164414835611677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86399449552776276557074451 129599174329164414835611677)
        ·
          refine ⟨48599690373436655563354379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129599174329164414835611677 48599690373436655563354379)
          ·
            refine ⟨72899535560154983345031569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48599690373436655563354379 72899535560154983345031569)
            ·
              refine ⟨54674651670116237508773677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72899535560154983345031569 54674651670116237508773677)
              ·
                refine ⟨20502994376293589065790129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54674651670116237508773677 20502994376293589065790129)
                ·
                  refine ⟨15377245782220191799342597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20502994376293589065790129 15377245782220191799342597)
                  ·
                    refine ⟨2883233584166285962376737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15377245782220191799342597 2883233584166285962376737)
                    ·
                      refine ⟨2162425188124714471782553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2883233584166285962376737 2162425188124714471782553)
                      ·
                        rfl

theorem cell23_4211308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 4, 2].length) (baseStart_4211308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211308 prefixEnd_4211308 := by exact prefixLift 4211308
  have htrace : WordTrace (prefixWord ++ tailWord_4211308) baseStart_4211308 baseEnd_4211308 := by
    simpa [prefixWord, tailWord_4211308, baseEnd_4211308] using wordTrace_append hprefix tailTrace_4211308
  have hstable : (prefixWord ++ tailWord_4211308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211308).length < 2 ^ (prefixWord ++ tailWord_4211308).sum := by decide
  have hdescent : baseEnd_4211308 < baseStart_4211308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211311 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 3]
def baseStart_4211311 : Nat := 118140960795 + 4211311 * 2 ^ 59
def prefixEnd_4211311 : Nat := 4983230072969 + 3 ^ 40 * 4211311 * 2
def baseEnd_4211311 : Nat := 2162426728566677960045039

theorem tailTrace_4211311 : CollatzResearch.WordTrace tailWord_4211311 prefixEnd_4211311 2162426728566677960045039 := by
  unfold tailWord_4211311
  simp only [CollatzResearch.WordTrace]
  refine ⟨153599130846146956502713787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102399420564097971001809191 153599130846146956502713787)
  ·
    refine ⟨230398696269220434754070681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153599130846146956502713787 230398696269220434754070681)
    ·
      refine ⟨172799022201915326065553011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230398696269220434754070681 172799022201915326065553011)
      ·
        refine ⟨259198533302872989098329517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172799022201915326065553011 259198533302872989098329517)
        ·
          refine ⟨97199449988577370911873569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259198533302872989098329517 97199449988577370911873569)
          ·
            refine ⟨72899587491433028183905177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97199449988577370911873569 72899587491433028183905177)
            ·
              refine ⟨54674690618574771137928883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72899587491433028183905177 54674690618574771137928883)
              ·
                refine ⟨82012035927862156706893325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54674690618574771137928883 82012035927862156706893325)
                ·
                  refine ⟨30754513472948308765084997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82012035927862156706893325 30754513472948308765084997)
                  ·
                    refine ⟨5766471276177807893453437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30754513472948308765084997 5766471276177807893453437)
                    ·
                      refine ⟨2162426728566677960045039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5766471276177807893453437 2162426728566677960045039)
                      ·
                        rfl

theorem cell23_4211311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 4, 3].length) (baseStart_4211311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211311 prefixEnd_4211311 := by exact prefixLift 4211311
  have htrace : WordTrace (prefixWord ++ tailWord_4211311) baseStart_4211311 baseEnd_4211311 := by
    simpa [prefixWord, tailWord_4211311, baseEnd_4211311] using wordTrace_append hprefix tailTrace_4211311
  have hstable : (prefixWord ++ tailWord_4211311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211311).length < 2 ^ (prefixWord ++ tailWord_4211311).sum := by decide
  have hdescent : baseEnd_4211311 < baseStart_4211311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211325 : List Nat := [1, 4, 1, 1, 5, 1, 2, 1, 2, 1, 4]
def baseStart_4211325 : Nat := 118140960795 + 4211325 * 2 ^ 59
def prefixEnd_4211325 : Nat := 4983230072969 + 3 ^ 40 * 4211325 * 2
def baseEnd_4211325 : Nat := 2162433917295840905269975

theorem tailTrace_4211325 : CollatzResearch.WordTrace tailWord_4211325 prefixEnd_4211325 2162433917295840905269975 := by
  unfold tailWord_4211325
  simp only [CollatzResearch.WordTrace]
  refine ⟨153599641468096236893723429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102399760978730824595815619 153599641468096236893723429)
  ·
    refine ⟨28799932775268044417573143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153599641468096236893723429 28799932775268044417573143)
    ·
      refine ⟨43199899162902066626359715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28799932775268044417573143 43199899162902066626359715)
      ·
        refine ⟨64799848744353099939539573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43199899162902066626359715 64799848744353099939539573)
        ·
          refine ⟨6074985819783103119331835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64799848744353099939539573 6074985819783103119331835)
          ·
            refine ⟨9112478729674654678997753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6074985819783103119331835 9112478729674654678997753)
            ·
              refine ⟨6834359047255991009248315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9112478729674654678997753 6834359047255991009248315)
              ·
                refine ⟨10251538570883986513872473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6834359047255991009248315 10251538570883986513872473)
                ·
                  refine ⟨7688653928162989885404355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10251538570883986513872473 7688653928162989885404355)
                  ·
                    refine ⟨11532980892244484828106533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7688653928162989885404355 11532980892244484828106533)
                    ·
                      refine ⟨2162433917295840905269975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11532980892244484828106533 2162433917295840905269975)
                      ·
                        rfl

theorem cell23_4211325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_4211325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211325 prefixEnd_4211325 := by exact prefixLift 4211325
  have htrace : WordTrace (prefixWord ++ tailWord_4211325) baseStart_4211325 baseEnd_4211325 := by
    simpa [prefixWord, tailWord_4211325, baseEnd_4211325] using wordTrace_append hprefix tailTrace_4211325
  have hstable : (prefixWord ++ tailWord_4211325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211325).length < 2 ^ (prefixWord ++ tailWord_4211325).sum := by decide
  have hdescent : baseEnd_4211325 < baseStart_4211325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211328 : List Nat := [2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 3]
def baseStart_4211328 : Nat := 118140960795 + 4211328 * 2 ^ 59
def prefixEnd_4211328 : Nat := 4983230072969 + 3 ^ 40 * 4211328 * 2
def baseEnd_4211328 : Nat := 2162435457737804393532461

theorem tailTrace_4211328 : CollatzResearch.WordTrace tailWord_4211328 prefixEnd_4211328 2162435457737804393532461 := by
  unfold tailWord_4211328
  simp only [CollatzResearch.WordTrace]
  refine ⟨76799875443542684203041319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102399833924723578937388425 76799875443542684203041319)
  ·
    refine ⟨115199813165314026304561979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76799875443542684203041319 115199813165314026304561979)
    ·
      refine ⟨172799719747971039456842969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115199813165314026304561979 172799719747971039456842969)
      ·
        refine ⟨129599789810978279592632227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172799719747971039456842969 129599789810978279592632227)
        ·
          refine ⟨194399684716467419388948341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129599789810978279592632227 194399684716467419388948341)
          ·
            refine ⟨18224970442168820567713907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 194399684716467419388948341 18224970442168820567713907)
            ·
              refine ⟨27337455663253230851570861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18224970442168820567713907 27337455663253230851570861)
              ·
                refine ⟨10251545873719961569339073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27337455663253230851570861 10251545873719961569339073)
                ·
                  refine ⟨7688659405289971177004305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10251545873719961569339073 7688659405289971177004305)
                  ·
                    refine ⟨5766494553967478382753229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7688659405289971177004305 5766494553967478382753229)
                    ·
                      refine ⟨2162435457737804393532461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5766494553967478382753229 2162435457737804393532461)
                      ·
                        rfl

theorem cell23_4211328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 3].length) (baseStart_4211328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211328 prefixEnd_4211328 := by exact prefixLift 4211328
  have htrace : WordTrace (prefixWord ++ tailWord_4211328) baseStart_4211328 baseEnd_4211328 := by
    simpa [prefixWord, tailWord_4211328, baseEnd_4211328] using wordTrace_append hprefix tailTrace_4211328
  have hstable : (prefixWord ++ tailWord_4211328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211328).length < 2 ^ (prefixWord ++ tailWord_4211328).sum := by decide
  have hdescent : baseEnd_4211328 < baseStart_4211328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211335 : List Nat := [1, 1, 4, 2, 1, 2, 2, 5, 1, 4]
def baseStart_4211335 : Nat := 118140960795 + 4211335 * 2 ^ 59
def prefixEnd_4211335 : Nat := 4983230072969 + 3 ^ 40 * 4211335 * 2
def baseEnd_4211335 : Nat := 720813017367461955381643

theorem tailTrace_4211335 : CollatzResearch.WordTrace tailWord_4211335 prefixEnd_4211335 720813017367461955381643 := by
  unfold tailWord_4211335
  simp only [CollatzResearch.WordTrace]
  refine ⟨153600006198060008601587459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102400004132040005734391639 153600006198060008601587459)
  ·
    refine ⟨230400009297090012902381189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153600006198060008601587459 230400009297090012902381189)
    ·
      refine ⟨43200001743204377419196473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230400009297090012902381189 43200001743204377419196473)
      ·
        refine ⟨32400001307403283064397355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43200001743204377419196473 32400001307403283064397355)
        ·
          refine ⟨48600001961104924596596033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32400001307403283064397355 48600001961104924596596033)
          ·
            refine ⟨36450001470828693447447025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48600001961104924596596033 36450001470828693447447025)
            ·
              refine ⟨27337501103121520085585269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36450001470828693447447025 27337501103121520085585269)
              ·
                refine ⟨2562890728417642508023619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27337501103121520085585269 2562890728417642508023619)
                ·
                  refine ⟨3844336092626463762035429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562890728417642508023619 3844336092626463762035429)
                  ·
                    refine ⟨720813017367461955381643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3844336092626463762035429 720813017367461955381643)
                    ·
                      rfl

theorem cell23_4211335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_4211335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211335 prefixEnd_4211335 := by exact prefixLift 4211335
  have htrace : WordTrace (prefixWord ++ tailWord_4211335) baseStart_4211335 baseEnd_4211335 := by
    simpa [prefixWord, tailWord_4211335, baseEnd_4211335] using wordTrace_append hprefix tailTrace_4211335
  have hstable : (prefixWord ++ tailWord_4211335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211335).length < 2 ^ (prefixWord ++ tailWord_4211335).sum := by decide
  have hdescent : baseEnd_4211335 < baseStart_4211335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211351 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 6]
def baseStart_4211351 : Nat := 118140960795 + 4211351 * 2 ^ 59
def prefixEnd_4211351 : Nat := 4983230072969 + 3 ^ 40 * 4211351 * 2
def baseEnd_4211351 : Nat := 2162447267792857803544855

theorem tailTrace_4211351 : CollatzResearch.WordTrace tailWord_4211351 prefixEnd_4211351 2162447267792857803544855 := by
  unfold tailWord_4211351
  simp only [CollatzResearch.WordTrace]
  refine ⟨153600589766002043334169907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102400393177334695556113271 153600589766002043334169907)
  ·
    refine ⟨230400884649003065001254861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153600589766002043334169907 230400884649003065001254861)
    ·
      refine ⟨86400331743376149375470573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230400884649003065001254861 86400331743376149375470573)
      ·
        refine ⟨32400124403766056015801465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86400331743376149375470573 32400124403766056015801465)
        ·
          refine ⟨24300093302824542011851099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32400124403766056015801465 24300093302824542011851099)
          ·
            refine ⟨36450139954236813017776649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24300093302824542011851099 36450139954236813017776649)
            ·
              refine ⟨27337604965677609763332487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36450139954236813017776649 27337604965677609763332487)
              ·
                refine ⟨41006407448516414644998731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27337604965677609763332487 41006407448516414644998731)
                ·
                  refine ⟨61509611172774621967498097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41006407448516414644998731 61509611172774621967498097)
                  ·
                    refine ⟨46132208379580966475623573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61509611172774621967498097 46132208379580966475623573)
                    ·
                      refine ⟨2162447267792857803544855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46132208379580966475623573 2162447267792857803544855)
                      ·
                        rfl

theorem cell23_4211351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_4211351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211351 prefixEnd_4211351 := by exact prefixLift 4211351
  have htrace : WordTrace (prefixWord ++ tailWord_4211351) baseStart_4211351 baseEnd_4211351 := by
    simpa [prefixWord, tailWord_4211351, baseEnd_4211351] using wordTrace_append hprefix tailTrace_4211351
  have hstable : (prefixWord ++ tailWord_4211351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211351).length < 2 ^ (prefixWord ++ tailWord_4211351).sum := by decide
  have hdescent : baseEnd_4211351 < baseStart_4211351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211375 : List Nat := [1, 1, 2, 1, 2, 6, 1, 2, 3, 1, 3]
def baseStart_4211375 : Nat := 118140960795 + 4211375 * 2 ^ 59
def prefixEnd_4211375 : Nat := 4983230072969 + 3 ^ 40 * 4211375 * 2
def baseEnd_4211375 : Nat := 2162459591328565709644745

theorem tailTrace_4211375 : CollatzResearch.WordTrace tailWord_4211375 prefixEnd_4211375 2162459591328565709644745 := by
  unfold tailWord_4211375
  simp only [CollatzResearch.WordTrace]
  refine ⟨153601465117915095433043579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102400976745276730288695719 153601465117915095433043579)
  ·
    refine ⟨230402197676872643149565369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153601465117915095433043579 230402197676872643149565369)
    ·
      refine ⟨172801648257654482362174027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230402197676872643149565369 172801648257654482362174027)
      ·
        refine ⟨259202472386481723543261041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172801648257654482362174027 259202472386481723543261041)
        ·
          refine ⟨194401854289861292657445781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259202472386481723543261041 194401854289861292657445781)
          ·
            refine ⟨9112586919837248093317771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 194401854289861292657445781 9112586919837248093317771)
            ·
              refine ⟨13668880379755872139976657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9112586919837248093317771 13668880379755872139976657)
              ·
                refine ⟨10251660284816904104982493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13668880379755872139976657 10251660284816904104982493)
                ·
                  refine ⟨3844372606806339039368435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10251660284816904104982493 3844372606806339039368435)
                  ·
                    refine ⟨5766558910209508559052653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3844372606806339039368435 5766558910209508559052653)
                    ·
                      refine ⟨2162459591328565709644745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5766558910209508559052653 2162459591328565709644745)
                      ·
                        rfl

theorem cell23_4211375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 1, 3].length) (baseStart_4211375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211375 prefixEnd_4211375 := by exact prefixLift 4211375
  have htrace : WordTrace (prefixWord ++ tailWord_4211375) baseStart_4211375 baseEnd_4211375 := by
    simpa [prefixWord, tailWord_4211375, baseEnd_4211375] using wordTrace_append hprefix tailTrace_4211375
  have hstable : (prefixWord ++ tailWord_4211375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211375).length < 2 ^ (prefixWord ++ tailWord_4211375).sum := by decide
  have hdescent : baseEnd_4211375 < baseStart_4211375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211378 : List Nat := [3, 2, 1, 1, 1, 2, 1, 6, 1, 5]
def baseStart_4211378 : Nat := 118140960795 + 4211378 * 2 ^ 59
def prefixEnd_4211378 : Nat := 4983230072969 + 3 ^ 40 * 4211378 * 2
def baseEnd_4211378 : Nat := 720820377256843065969077

theorem tailTrace_4211378 : CollatzResearch.WordTrace tailWord_4211378 prefixEnd_4211378 720820377256843065969077 := by
  unfold tailWord_4211378
  simp only [CollatzResearch.WordTrace]
  refine ⟨38400393634226056736350697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102401049691269484630268525 38400393634226056736350697)
  ·
    refine ⟨28800295225669542552263023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38400393634226056736350697 28800295225669542552263023)
    ·
      refine ⟨43200442838504313828394535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28800295225669542552263023 43200442838504313828394535)
      ·
        refine ⟨64800664257756470742591803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43200442838504313828394535 64800664257756470742591803)
        ·
          refine ⟨97200996386634706113887705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64800664257756470742591803 97200996386634706113887705)
          ·
            refine ⟨72900747289976029585415779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97200996386634706113887705 72900747289976029585415779)
            ·
              refine ⟨109351120934964044378123669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72900747289976029585415779 109351120934964044378123669)
              ·
                refine ⟨5125833793826439580224547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 109351120934964044378123669 5125833793826439580224547)
                ·
                  refine ⟨7688750690739659370336821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5125833793826439580224547 7688750690739659370336821)
                  ·
                    refine ⟨720820377256843065969077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7688750690739659370336821 720820377256843065969077)
                    ·
                      rfl

theorem cell23_4211378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_4211378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211378 prefixEnd_4211378 := by exact prefixLift 4211378
  have htrace : WordTrace (prefixWord ++ tailWord_4211378) baseStart_4211378 baseEnd_4211378 := by
    simpa [prefixWord, tailWord_4211378, baseEnd_4211378] using wordTrace_append hprefix tailTrace_4211378
  have hstable : (prefixWord ++ tailWord_4211378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211378).length < 2 ^ (prefixWord ++ tailWord_4211378).sum := by decide
  have hdescent : baseEnd_4211378 < baseStart_4211378 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211392 : List Nat := [2, 1, 1, 2, 4, 2, 1, 5, 1, 1, 3]
def baseStart_4211392 : Nat := 118140960795 + 4211392 * 2 ^ 59
def prefixEnd_4211392 : Nat := 4983230072969 + 3 ^ 40 * 4211392 * 2
def baseEnd_4211392 : Nat := 2162468320499692143132167

theorem tailTrace_4211392 : CollatzResearch.WordTrace tailWord_4211392 prefixEnd_4211392 2162468320499692143132167 := by
  unfold tailWord_4211392
  simp only [CollatzResearch.WordTrace]
  refine ⟨76801042579426753668206215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102401390105902338224274953 76801042579426753668206215)
  ·
    refine ⟨115201563869140130502309323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76801042579426753668206215 115201563869140130502309323)
    ·
      refine ⟨172802345803710195753463985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115201563869140130502309323 172802345803710195753463985)
      ·
        refine ⟨129601759352782646815097989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172802345803710195753463985 129601759352782646815097989)
        ·
          refine ⟨24300329878646746277830873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129601759352782646815097989 24300329878646746277830873)
          ·
            refine ⟨18225247408985059708373155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24300329878646746277830873 18225247408985059708373155)
            ·
              refine ⟨27337871113477589562559733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18225247408985059708373155 27337871113477589562559733)
              ·
                refine ⟨2562925416888524021489975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27337871113477589562559733 2562925416888524021489975)
                ·
                  refine ⟨3844388125332786032234963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562925416888524021489975 3844388125332786032234963)
                  ·
                    refine ⟨5766582187999179048352445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3844388125332786032234963 5766582187999179048352445)
                    ·
                      refine ⟨2162468320499692143132167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5766582187999179048352445 2162468320499692143132167)
                      ·
                        rfl

theorem cell23_4211392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 1, 1, 3].length) (baseStart_4211392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211392 prefixEnd_4211392 := by exact prefixLift 4211392
  have htrace : WordTrace (prefixWord ++ tailWord_4211392) baseStart_4211392 baseEnd_4211392 := by
    simpa [prefixWord, tailWord_4211392, baseEnd_4211392] using wordTrace_append hprefix tailTrace_4211392
  have hstable : (prefixWord ++ tailWord_4211392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211392).length < 2 ^ (prefixWord ++ tailWord_4211392).sum := by decide
  have hdescent : baseEnd_4211392 < baseStart_4211392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211401 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 7, 1, 5]
def baseStart_4211401 : Nat := 118140960795 + 4211401 * 2 ^ 59
def prefixEnd_4211401 : Nat := 4983230072969 + 3 ^ 40 * 4211401 * 2
def baseEnd_4211401 : Nat := 2162472941825582607919625

theorem tailTrace_4211401 : CollatzResearch.WordTrace tailWord_4211401 prefixEnd_4211401 2162472941825582607919625 := by
  unfold tailWord_4211401
  simp only [CollatzResearch.WordTrace]
  refine ⟨153602413415820901873490057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102401608943880601248993371 153602413415820901873490057)
  ·
    refine ⟨115201810061865676405117543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153602413415820901873490057 115201810061865676405117543)
    ·
      refine ⟨172802715092798514607676315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115201810061865676405117543 172802715092798514607676315)
      ·
        refine ⟨259204072639197771911514473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172802715092798514607676315 259204072639197771911514473)
        ·
          refine ⟨194403054479398328933635855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259204072639197771911514473 194403054479398328933635855)
          ·
            refine ⟨291604581719097493400453783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194403054479398328933635855 291604581719097493400453783)
            ·
              refine ⟨437406872578646240100680675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291604581719097493400453783 437406872578646240100680675)
              ·
                refine ⟨656110308867969360151021013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 437406872578646240100680675 656110308867969360151021013)
                ·
                  refine ⟨15377585364093031878539555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 656110308867969360151021013 15377585364093031878539555)
                  ·
                    refine ⟨23066378046139547817809333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15377585364093031878539555 23066378046139547817809333)
                    ·
                      refine ⟨2162472941825582607919625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23066378046139547817809333 2162472941825582607919625)
                      ·
                        rfl

theorem cell23_4211401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_4211401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211401 prefixEnd_4211401 := by exact prefixLift 4211401
  have htrace : WordTrace (prefixWord ++ tailWord_4211401) baseStart_4211401 baseEnd_4211401 := by
    simpa [prefixWord, tailWord_4211401, baseEnd_4211401] using wordTrace_append hprefix tailTrace_4211401
  have hstable : (prefixWord ++ tailWord_4211401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211401).length < 2 ^ (prefixWord ++ tailWord_4211401).sum := by decide
  have hdescent : baseEnd_4211401 < baseStart_4211401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211418 : List Nat := [3, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5]
def baseStart_4211418 : Nat := 118140960795 + 4211418 * 2 ^ 59
def prefixEnd_4211418 : Nat := 4983230072969 + 3 ^ 40 * 4211418 * 2
def baseEnd_4211418 : Nat := 2162481670996709041407047

theorem tailTrace_4211418 : CollatzResearch.WordTrace tailWord_4211418 prefixEnd_4211418 2162481670996709041407047 := by
  unfold tailWord_4211418
  simp only [CollatzResearch.WordTrace]
  refine ⟨38400758364189828444214727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102402022304506209184572605 38400758364189828444214727)
  ·
    refine ⟨57601137546284742666322091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38400758364189828444214727 57601137546284742666322091)
    ·
      refine ⟨86401706319427113999483137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57601137546284742666322091 86401706319427113999483137)
      ·
        refine ⟨64801279739570335499612353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86401706319427113999483137 64801279739570335499612353)
        ·
          refine ⟨48600959804677751624709265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64801279739570335499612353 48600959804677751624709265)
          ·
            refine ⟨36450719853508313718531949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48600959804677751624709265 36450719853508313718531949)
            ·
              refine ⟨13669019945065617644449481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36450719853508313718531949 13669019945065617644449481)
              ·
                refine ⟨10251764958799213233337111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13669019945065617644449481 10251764958799213233337111)
                ·
                  refine ⟨15377647438198819850005667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10251764958799213233337111 15377647438198819850005667)
                  ·
                    refine ⟨23066471157298229775008501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15377647438198819850005667 23066471157298229775008501)
                    ·
                      refine ⟨2162481670996709041407047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23066471157298229775008501 2162481670996709041407047)
                      ·
                        rfl

theorem cell23_4211418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_4211418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211418 prefixEnd_4211418 := by exact prefixLift 4211418
  have htrace : WordTrace (prefixWord ++ tailWord_4211418) baseStart_4211418 baseEnd_4211418 := by
    simpa [prefixWord, tailWord_4211418, baseEnd_4211418] using wordTrace_append hprefix tailTrace_4211418
  have hstable : (prefixWord ++ tailWord_4211418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211418).length < 2 ^ (prefixWord ++ tailWord_4211418).sum := by decide
  have hdescent : baseEnd_4211418 < baseStart_4211418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211425 : List Nat := [1, 2, 3, 1, 4, 3, 1, 1, 1, 6]
def baseStart_4211425 : Nat := 118140960795 + 4211425 * 2 ^ 59
def prefixEnd_4211425 : Nat := 4983230072969 + 3 ^ 40 * 4211425 * 2
def baseEnd_4211425 : Nat := 720828421787096838006505

theorem tailTrace_4211425 : CollatzResearch.WordTrace tailWord_4211425 prefixEnd_4211425 720828421787096838006505 := by
  unfold tailWord_4211425
  simp only [CollatzResearch.WordTrace]
  refine ⟨153603288767733953972363729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102402192511822635981575819 153603288767733953972363729)
  ·
    refine ⟨115202466575800465479272797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153603288767733953972363729 115202466575800465479272797)
    ·
      refine ⟨43200924965925174554727299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115202466575800465479272797 43200924965925174554727299)
      ·
        refine ⟨64801387448887761832090949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43200924965925174554727299 64801387448887761832090949)
        ·
          refine ⟨12150260146666455343517053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64801387448887761832090949 12150260146666455343517053)
          ·
            refine ⟨4556347554999920753818895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12150260146666455343517053 4556347554999920753818895)
            ·
              refine ⟨6834521332499881130728343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4556347554999920753818895 6834521332499881130728343)
              ·
                refine ⟨10251781998749821696092515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6834521332499881130728343 10251781998749821696092515)
                ·
                  refine ⟨15377672998124732544138773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10251781998749821696092515 15377672998124732544138773)
                  ·
                    refine ⟨720828421787096838006505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15377672998124732544138773 720828421787096838006505)
                    ·
                      rfl

theorem cell23_4211425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_4211425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211425 prefixEnd_4211425 := by exact prefixLift 4211425
  have htrace : WordTrace (prefixWord ++ tailWord_4211425) baseStart_4211425 baseEnd_4211425 := by
    simpa [prefixWord, tailWord_4211425, baseEnd_4211425] using wordTrace_append hprefix tailTrace_4211425
  have hstable : (prefixWord ++ tailWord_4211425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211425).length < 2 ^ (prefixWord ++ tailWord_4211425).sum := by decide
  have hdescent : baseEnd_4211425 < baseStart_4211425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211428 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_4211428 : Nat := 118140960795 + 4211428 * 2 ^ 59
def prefixEnd_4211428 : Nat := 4983230072969 + 3 ^ 40 * 4211428 * 2
def baseEnd_4211428 : Nat := 2162486805803254002282001

theorem tailTrace_4211428 : CollatzResearch.WordTrace tailWord_4211428 prefixEnd_4211428 2162486805803254002282001 := by
  unfold tailWord_4211428
  simp only [CollatzResearch.WordTrace]
  refine ⟨76801699093361542742361469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102402265457815390323148625 76801699093361542742361469)
  ·
    refine ⟨28800637160010578528385551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76801699093361542742361469 28800637160010578528385551)
    ·
      refine ⟨43200955740015867792578327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28800637160010578528385551 43200955740015867792578327)
      ·
        refine ⟨64801433610023801688867491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43200955740015867792578327 64801433610023801688867491)
        ·
          refine ⟨97202150415035702533301237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64801433610023801688867491 97202150415035702533301237)
          ·
            refine ⟨9112701601409597112496991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 97202150415035702533301237 9112701601409597112496991)
            ·
              refine ⟨13669052402114395668745487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9112701601409597112496991 13669052402114395668745487)
              ·
                refine ⟨20503578603171593503118231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13669052402114395668745487 20503578603171593503118231)
                ·
                  refine ⟨30755367904757390254677347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20503578603171593503118231 30755367904757390254677347)
                  ·
                    refine ⟨46133051857136085382016021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30755367904757390254677347 46133051857136085382016021)
                    ·
                      refine ⟨2162486805803254002282001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46133051857136085382016021 2162486805803254002282001)
                      ·
                        rfl

theorem cell23_4211428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_4211428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211428 prefixEnd_4211428 := by exact prefixLift 4211428
  have htrace : WordTrace (prefixWord ++ tailWord_4211428) baseStart_4211428 baseEnd_4211428 := by
    simpa [prefixWord, tailWord_4211428, baseEnd_4211428] using wordTrace_append hprefix tailTrace_4211428
  have hstable : (prefixWord ++ tailWord_4211428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211428).length < 2 ^ (prefixWord ++ tailWord_4211428).sum := by decide
  have hdescent : baseEnd_4211428 < baseStart_4211428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211432 : List Nat := [2, 1, 4, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_4211432 : Nat := 118140960795 + 4211432 * 2 ^ 59
def prefixEnd_4211432 : Nat := 4983230072969 + 3 ^ 40 * 4211432 * 2
def baseEnd_4211432 : Nat := 2162488859725871986631983

theorem tailTrace_4211432 : CollatzResearch.WordTrace tailWord_4211432 prefixEnd_4211432 2162488859725871986631983 := by
  unfold tailWord_4211432
  simp only [CollatzResearch.WordTrace]
  refine ⟨76801772039354297083934275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102402362719139062778579033 76801772039354297083934275)
  ·
    refine ⟨115202658059031445625901413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76801772039354297083934275 115202658059031445625901413)
    ·
      refine ⟨21600498386068396054856515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115202658059031445625901413 21600498386068396054856515)
      ·
        refine ⟨32400747579102594082284773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21600498386068396054856515 32400747579102594082284773)
        ·
          refine ⟨6075140171081736390428395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32400747579102594082284773 6075140171081736390428395)
          ·
            refine ⟨9112710256622604585642593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6075140171081736390428395 9112710256622604585642593)
            ·
              refine ⟨6834532692466953439231945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9112710256622604585642593 6834532692466953439231945)
              ·
                refine ⟨5125899519350215079423959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6834532692466953439231945 5125899519350215079423959)
                ·
                  refine ⟨7688849279025322619135939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5125899519350215079423959 7688849279025322619135939)
                  ·
                    refine ⟨11533273918537983928703909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7688849279025322619135939 11533273918537983928703909)
                    ·
                      refine ⟨2162488859725871986631983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11533273918537983928703909 2162488859725871986631983)
                      ·
                        rfl

theorem cell23_4211432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_4211432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211432 prefixEnd_4211432 := by exact prefixLift 4211432
  have htrace : WordTrace (prefixWord ++ tailWord_4211432) baseStart_4211432 baseEnd_4211432 := by
    simpa [prefixWord, tailWord_4211432, baseEnd_4211432] using wordTrace_append hprefix tailTrace_4211432
  have hstable : (prefixWord ++ tailWord_4211432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211432).length < 2 ^ (prefixWord ++ tailWord_4211432).sum := by decide
  have hdescent : baseEnd_4211432 < baseStart_4211432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211438 : List Nat := [4, 1, 2, 1, 1, 4, 1, 9]
def baseStart_4211438 : Nat := 118140960795 + 4211438 * 2 ^ 59
def prefixEnd_4211438 : Nat := 4983230072969 + 3 ^ 40 * 4211438 * 2
def baseEnd_4211438 : Nat := 80092294096659220857665

theorem tailTrace_4211438 : CollatzResearch.WordTrace tailWord_4211438 prefixEnd_4211438 80092294096659220857665 := by
  unfold tailWord_4211438
  simp only [CollatzResearch.WordTrace]
  refine ⟨19200470364585857149073371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102402508611124571461724645 19200470364585857149073371)
  ·
    refine ⟨28800705546878785723610057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19200470364585857149073371 28800705546878785723610057)
    ·
      refine ⟨21600529160159089292707543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28800705546878785723610057 21600529160159089292707543)
      ·
        refine ⟨32400793740238633939061315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21600529160159089292707543 32400793740238633939061315)
        ·
          refine ⟨48601190610357950908591973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32400793740238633939061315 48601190610357950908591973)
          ·
            refine ⟨9112723239442115795360995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48601190610357950908591973 9112723239442115795360995)
            ·
              refine ⟨13669084859163173693041493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9112723239442115795360995 13669084859163173693041493)
              ·
                refine ⟨80092294096659220857665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13669084859163173693041493 80092294096659220857665)
                ·
                  rfl

theorem cell23_4211438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 9].length) (baseStart_4211438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211438 prefixEnd_4211438 := by exact prefixLift 4211438
  have htrace : WordTrace (prefixWord ++ tailWord_4211438) baseStart_4211438 baseEnd_4211438 := by
    simpa [prefixWord, tailWord_4211438, baseEnd_4211438] using wordTrace_append hprefix tailTrace_4211438
  have hstable : (prefixWord ++ tailWord_4211438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211438).length < 2 ^ (prefixWord ++ tailWord_4211438).sum := by decide
  have hdescent : baseEnd_4211438 < baseStart_4211438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211448 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 3, 3, 3]
def baseStart_4211448 : Nat := 118140960795 + 4211448 * 2 ^ 59
def prefixEnd_4211448 : Nat := 4983230072969 + 3 ^ 40 * 4211448 * 2
def baseEnd_4211448 : Nat := 2162497075416343924031909

theorem tailTrace_4211448 : CollatzResearch.WordTrace tailWord_4211448 prefixEnd_4211448 2162497075416343924031909 := by
  unfold tailWord_4211448
  simp only [CollatzResearch.WordTrace]
  refine ⟨76802063823325314450225499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102402751764433752600300665 76802063823325314450225499)
  ·
    refine ⟨115203095734987971675338249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76802063823325314450225499 115203095734987971675338249)
    ·
      refine ⟨86402321801240978756503687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115203095734987971675338249 86402321801240978756503687)
      ·
        refine ⟨129603482701861468134755531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86402321801240978756503687 129603482701861468134755531)
        ·
          refine ⟨194405224052792202202133297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129603482701861468134755531 194405224052792202202133297)
          ·
            refine ⟨145803918039594151651599973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194405224052792202202133297 145803918039594151651599973)
            ·
              refine ⟨27338234632423903434674995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145803918039594151651599973 27338234632423903434674995)
              ·
                refine ⟨41007351948635855152012493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27338234632423903434674995 41007351948635855152012493)
                ·
                  refine ⟨15377756980738445682004685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41007351948635855152012493 15377756980738445682004685)
                  ·
                    refine ⟨5766658867776917130751757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15377756980738445682004685 5766658867776917130751757)
                    ·
                      refine ⟨2162497075416343924031909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5766658867776917130751757 2162497075416343924031909)
                      ·
                        rfl

theorem cell23_4211448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_4211448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211448 prefixEnd_4211448 := by exact prefixLift 4211448
  have htrace : WordTrace (prefixWord ++ tailWord_4211448) baseStart_4211448 baseEnd_4211448 := by
    simpa [prefixWord, tailWord_4211448, baseEnd_4211448] using wordTrace_append hprefix tailTrace_4211448
  have hstable : (prefixWord ++ tailWord_4211448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211448).length < 2 ^ (prefixWord ++ tailWord_4211448).sum := by decide
  have hdescent : baseEnd_4211448 < baseStart_4211448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211465 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 4, 1, 3]
def baseStart_4211465 : Nat := 118140960795 + 4211465 * 2 ^ 59
def prefixEnd_4211465 : Nat := 4983230072969 + 3 ^ 40 * 4211465 * 2
def baseEnd_4211465 : Nat := 2162505804587470357519331

theorem tailTrace_4211465 : CollatzResearch.WordTrace tailWord_4211465 prefixEnd_4211465 2162505804587470357519331 := by
  unfold tailWord_4211465
  simp only [CollatzResearch.WordTrace]
  refine ⟨153604747687589040803819849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102403165125059360535879899 153604747687589040803819849)
  ·
    refine ⟨115203560765691780602864887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153604747687589040803819849 115203560765691780602864887)
    ·
      refine ⟨172805341148537670904297331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115203560765691780602864887 172805341148537670904297331)
      ·
        refine ⟨259208011722806506356445997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172805341148537670904297331 259208011722806506356445997)
        ·
          refine ⟨97203004396052439883667249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259208011722806506356445997 97203004396052439883667249)
          ·
            refine ⟨72902253297039329912750437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97203004396052439883667249 72902253297039329912750437)
            ·
              refine ⟨13669172493194874358640707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72902253297039329912750437 13669172493194874358640707)
              ·
                refine ⟨20503758739792311537961061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13669172493194874358640707 20503758739792311537961061)
                ·
                  refine ⟨3844454763711058413367699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20503758739792311537961061 3844454763711058413367699)
                  ·
                    refine ⟨5766682145566587620051549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3844454763711058413367699 5766682145566587620051549)
                    ·
                      refine ⟨2162505804587470357519331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5766682145566587620051549 2162505804587470357519331)
                      ·
                        rfl

theorem cell23_4211465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 1, 3].length) (baseStart_4211465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211465 prefixEnd_4211465 := by exact prefixLift 4211465
  have htrace : WordTrace (prefixWord ++ tailWord_4211465) baseStart_4211465 baseEnd_4211465 := by
    simpa [prefixWord, tailWord_4211465, baseEnd_4211465] using wordTrace_append hprefix tailTrace_4211465
  have hstable : (prefixWord ++ tailWord_4211465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211465).length < 2 ^ (prefixWord ++ tailWord_4211465).sum := by decide
  have hdescent : baseEnd_4211465 < baseStart_4211465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211466 : List Nat := [3, 1, 2, 2, 1, 2, 5, 2, 1, 2, 2]
def baseStart_4211466 : Nat := 118140960795 + 4211466 * 2 ^ 59
def prefixEnd_4211466 : Nat := 4983230072969 + 3 ^ 40 * 4211466 * 2
def baseEnd_4211466 : Nat := 2162506318068124853606827

theorem tailTrace_4211466 : CollatzResearch.WordTrace tailWord_4211466 prefixEnd_4211466 2162506318068124853606827 := by
  unfold tailWord_4211466
  simp only [CollatzResearch.WordTrace]
  refine ⟨38401196040146354493651563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102403189440390278649737501 38401196040146354493651563)
  ·
    refine ⟨57601794060219531740477345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38401196040146354493651563 57601794060219531740477345)
    ·
      refine ⟨43201345545164648805358009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57601794060219531740477345 43201345545164648805358009)
      ·
        refine ⟨32401009158873486604018507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43201345545164648805358009 32401009158873486604018507)
        ·
          refine ⟨48601513738310229906027761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32401009158873486604018507 48601513738310229906027761)
          ·
            refine ⟨36451135303732672429520821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48601513738310229906027761 36451135303732672429520821)
            ·
              refine ⟨3417293934724938040267577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36451135303732672429520821 3417293934724938040267577)
              ·
                refine ⟨2562970451043703530200683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3417293934724938040267577 2562970451043703530200683)
                ·
                  refine ⟨3844455676565555295301025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562970451043703530200683 3844455676565555295301025)
                  ·
                    refine ⟨2883341757424166471475769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3844455676565555295301025 2883341757424166471475769)
                    ·
                      refine ⟨2162506318068124853606827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2883341757424166471475769 2162506318068124853606827)
                      ·
                        rfl

theorem cell23_4211466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_4211466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211466 prefixEnd_4211466 := by exact prefixLift 4211466
  have htrace : WordTrace (prefixWord ++ tailWord_4211466) baseStart_4211466 baseEnd_4211466 := by
    simpa [prefixWord, tailWord_4211466, baseEnd_4211466] using wordTrace_append hprefix tailTrace_4211466
  have hstable : (prefixWord ++ tailWord_4211466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211466).length < 2 ^ (prefixWord ++ tailWord_4211466).sum := by decide
  have hdescent : baseEnd_4211466 < baseStart_4211466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211475 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 3, 3, 2]
def baseStart_4211475 : Nat := 118140960795 + 4211475 * 2 ^ 59
def prefixEnd_4211475 : Nat := 4983230072969 + 3 ^ 40 * 4211475 * 2
def baseEnd_4211475 : Nat := 2162510939394015318394285

theorem tailTrace_4211475 : CollatzResearch.WordTrace tailWord_4211475 prefixEnd_4211475 2162510939394015318394285 := by
  unfold tailWord_4211475
  simp only [CollatzResearch.WordTrace]
  refine ⟨153605112417552812511683879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102403408278368541674455919 153605112417552812511683879)
  ·
    refine ⟨230407668626329218767525819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153605112417552812511683879 230407668626329218767525819)
    ·
      refine ⟨345611502939493828151288729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230407668626329218767525819 345611502939493828151288729)
      ·
        refine ⟨259208627204620371113466547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345611502939493828151288729 259208627204620371113466547)
        ·
          refine ⟨388812940806930556670199821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259208627204620371113466547 388812940806930556670199821)
          ·
            refine ⟨145804852802598958751324933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 388812940806930556670199821 145804852802598958751324933)
            ·
              refine ⟨27338409900487304765873425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145804852802598958751324933 27338409900487304765873425)
              ·
                refine ⟨20503807425365478574405069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27338409900487304765873425 20503807425365478574405069)
                ·
                  refine ⟨7688927784512054465401901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20503807425365478574405069 7688927784512054465401901)
                  ·
                    refine ⟨2883347919192020424525713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7688927784512054465401901 2883347919192020424525713)
                    ·
                      refine ⟨2162510939394015318394285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2883347919192020424525713 2162510939394015318394285)
                      ·
                        rfl

theorem cell23_4211475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 3, 3, 2].length) (baseStart_4211475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211475 prefixEnd_4211475 := by exact prefixLift 4211475
  have htrace : WordTrace (prefixWord ++ tailWord_4211475) baseStart_4211475 baseEnd_4211475 := by
    simpa [prefixWord, tailWord_4211475, baseEnd_4211475] using wordTrace_append hprefix tailTrace_4211475
  have hstable : (prefixWord ++ tailWord_4211475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211475).length < 2 ^ (prefixWord ++ tailWord_4211475).sum := by decide
  have hdescent : baseEnd_4211475 < baseStart_4211475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211482 : List Nat := [3, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3]
def baseStart_4211482 : Nat := 118140960795 + 4211482 * 2 ^ 59
def prefixEnd_4211482 : Nat := 4983230072969 + 3 ^ 40 * 4211482 * 2
def baseEnd_4211482 : Nat := 2162514533758596791006753

theorem tailTrace_4211482 : CollatzResearch.WordTrace tailWord_4211482 prefixEnd_4211482 2162514533758596791006753 := by
  unfold tailWord_4211482
  simp only [CollatzResearch.WordTrace]
  refine ⟨38401341932131863176797175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102403578485684968471459133 38401341932131863176797175)
  ·
    refine ⟨57602012898197794765195763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38401341932131863176797175 57602012898197794765195763)
    ·
      refine ⟨86403019347296692147793645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57602012898197794765195763 86403019347296692147793645)
      ·
        refine ⟨32401132255236259555422617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86403019347296692147793645 32401132255236259555422617)
        ·
          refine ⟨24300849191427194666566963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32401132255236259555422617 24300849191427194666566963)
          ·
            refine ⟨36451273787140791999850445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24300849191427194666566963 36451273787140791999850445)
            ·
              refine ⟨13669227670177796999943917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36451273787140791999850445 13669227670177796999943917)
              ·
                refine ⟨5125960376316673874978969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13669227670177796999943917 5125960376316673874978969)
                ·
                  refine ⟨3844470282237505406234227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5125960376316673874978969 3844470282237505406234227)
                  ·
                    refine ⟨5766705423356258109351341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3844470282237505406234227 5766705423356258109351341)
                    ·
                      refine ⟨2162514533758596791006753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5766705423356258109351341 2162514533758596791006753)
                      ·
                        rfl

theorem cell23_4211482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_4211482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211482 prefixEnd_4211482 := by exact prefixLift 4211482
  have htrace : WordTrace (prefixWord ++ tailWord_4211482) baseStart_4211482 baseEnd_4211482 := by
    simpa [prefixWord, tailWord_4211482, baseEnd_4211482] using wordTrace_append hprefix tailTrace_4211482
  have hstable : (prefixWord ++ tailWord_4211482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211482).length < 2 ^ (prefixWord ++ tailWord_4211482).sum := by decide
  have hdescent : baseEnd_4211482 < baseStart_4211482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211528 : List Nat := [2, 1, 3, 1, 1, 3, 2, 3, 7]
def baseStart_4211528 : Nat := 118140960795 + 4211528 * 2 ^ 59
def prefixEnd_4211528 : Nat := 4983230072969 + 3 ^ 40 * 4211528 * 2
def baseEnd_4211528 : Nat := 240282017096522623447949

theorem tailTrace_4211528 : CollatzResearch.WordTrace tailWord_4211528 prefixEnd_4211528 240282017096522623447949 := by
  unfold tailWord_4211528
  simp only [CollatzResearch.WordTrace]
  refine ⟨76803522743180401281681619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102404696990907201708908825 76803522743180401281681619)
  ·
    refine ⟨115205284114770601922522429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76803522743180401281681619 115205284114770601922522429)
    ·
      refine ⟨43201981543038975720945911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115205284114770601922522429 43201981543038975720945911)
      ·
        refine ⟨64802972314558463581418867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43201981543038975720945911 64802972314558463581418867)
        ·
          refine ⟨97204458471837695372128301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64802972314558463581418867 97204458471837695372128301)
          ·
            refine ⟨36451671926939135764548113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97204458471837695372128301 36451671926939135764548113)
            ·
              refine ⟨27338753945204351823411085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36451671926939135764548113 27338753945204351823411085)
              ·
                refine ⟨10252032729451631933779157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27338753945204351823411085 10252032729451631933779157)
                ·
                  refine ⟨240282017096522623447949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10252032729451631933779157 240282017096522623447949)
                  ·
                    rfl

theorem cell23_4211528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 7].length) (baseStart_4211528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211528 prefixEnd_4211528 := by exact prefixLift 4211528
  have htrace : WordTrace (prefixWord ++ tailWord_4211528) baseStart_4211528 baseEnd_4211528 := by
    simpa [prefixWord, tailWord_4211528, baseEnd_4211528] using wordTrace_append hprefix tailTrace_4211528
  have hstable : (prefixWord ++ tailWord_4211528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211528).length < 2 ^ (prefixWord ++ tailWord_4211528).sum := by decide
  have hdescent : baseEnd_4211528 < baseStart_4211528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211568 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 5]
def baseStart_4211568 : Nat := 118140960795 + 4211568 * 2 ^ 59
def prefixEnd_4211568 : Nat := 4983230072969 + 3 ^ 40 * 4211568 * 2
def baseEnd_4211568 : Nat := 2162558693094883454531357

theorem tailTrace_4211568 : CollatzResearch.WordTrace tailWord_4211568 prefixEnd_4211568 2162558693094883454531357 := by
  unfold tailWord_4211568
  simp only [CollatzResearch.WordTrace]
  refine ⟨76804252203107944697409679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102405669604143926263212905 76804252203107944697409679)
  ·
    refine ⟨115206378304661917046114519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76804252203107944697409679 115206378304661917046114519)
    ·
      refine ⟨172809567456992875569171779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115206378304661917046114519 172809567456992875569171779)
      ·
        refine ⟨259214351185489313353757669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172809567456992875569171779 259214351185489313353757669)
        ·
          refine ⟨48602690847279246253829563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 259214351185489313353757669 48602690847279246253829563)
          ·
            refine ⟨72904036270918869380744345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48602690847279246253829563 72904036270918869380744345)
            ·
              refine ⟨54678027203189152035558259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72904036270918869380744345 54678027203189152035558259)
              ·
                refine ⟨82017040804783728053337389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54678027203189152035558259 82017040804783728053337389)
                ·
                  refine ⟨30756390301793898020001521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82017040804783728053337389 30756390301793898020001521)
                  ·
                    refine ⟨23067292726345423515001141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30756390301793898020001521 23067292726345423515001141)
                    ·
                      refine ⟨2162558693094883454531357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23067292726345423515001141 2162558693094883454531357)
                      ·
                        rfl

theorem cell23_4211568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_4211568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211568 prefixEnd_4211568 := by exact prefixLift 4211568
  have htrace : WordTrace (prefixWord ++ tailWord_4211568) baseStart_4211568 baseEnd_4211568 := by
    simpa [prefixWord, tailWord_4211568, baseEnd_4211568] using wordTrace_append hprefix tailTrace_4211568
  have hstable : (prefixWord ++ tailWord_4211568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211568).length < 2 ^ (prefixWord ++ tailWord_4211568).sum := by decide
  have hdescent : baseEnd_4211568 < baseStart_4211568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211665 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 3, 5]
def baseStart_4211665 : Nat := 118140960795 + 4211665 * 2 ^ 59
def prefixEnd_4211665 : Nat := 4983230072969 + 3 ^ 40 * 4211665 * 2
def baseEnd_4211665 : Nat := 720869500239456525006137

theorem tailTrace_4211665 : CollatzResearch.WordTrace tailWord_4211665 prefixEnd_4211665 720869500239456525006137 := by
  unfold tailWord_4211665
  simp only [CollatzResearch.WordTrace]
  refine ⟨153612042286864474961100449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102408028191242983307400299 153612042286864474961100449)
  ·
    refine ⟨115209031715148356220825337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153612042286864474961100449 115209031715148356220825337)
    ·
      refine ⟨86406773786361267165619003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115209031715148356220825337 86406773786361267165619003)
      ·
        refine ⟨129610160679541900748428505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86406773786361267165619003 129610160679541900748428505)
        ·
          refine ⟨97207620509656425561321379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129610160679541900748428505 97207620509656425561321379)
          ·
            refine ⟨145811430764484638341982069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97207620509656425561321379 145811430764484638341982069)
            ·
              refine ⟨13669821634170434844560819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 145811430764484638341982069 13669821634170434844560819)
              ·
                refine ⟨20504732451255652266841229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13669821634170434844560819 20504732451255652266841229)
                ·
                  refine ⟨7689274669220869600065461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20504732451255652266841229 7689274669220869600065461)
                  ·
                    refine ⟨720869500239456525006137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7689274669220869600065461 720869500239456525006137)
                    ·
                      rfl

theorem cell23_4211665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_4211665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211665 prefixEnd_4211665 := by exact prefixLift 4211665
  have htrace : WordTrace (prefixWord ++ tailWord_4211665) baseStart_4211665 baseEnd_4211665 := by
    simpa [prefixWord, tailWord_4211665, baseEnd_4211665] using wordTrace_append hprefix tailTrace_4211665
  have hstable : (prefixWord ++ tailWord_4211665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211665).length < 2 ^ (prefixWord ++ tailWord_4211665).sum := by decide
  have hdescent : baseEnd_4211665 < baseStart_4211665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211705 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 3, 1, 5]
def baseStart_4211705 : Nat := 118140960795 + 4211705 * 2 ^ 59
def prefixEnd_4211705 : Nat := 4983230072969 + 3 ^ 40 * 4211705 * 2
def baseEnd_4211705 : Nat := 2162629039944549418518227

theorem tailTrace_4211705 : CollatzResearch.WordTrace tailWord_4211705 prefixEnd_4211705 2162629039944549418518227 := by
  unfold tailWord_4211705
  simp only [CollatzResearch.WordTrace]
  refine ⟨153613501206719561792556569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102409000804479707861704379 153613501206719561792556569)
  ·
    refine ⟨115210125905039671344417427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153613501206719561792556569 115210125905039671344417427)
    ·
      refine ⟨172815188857559507016626141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115210125905039671344417427 172815188857559507016626141)
      ·
        refine ⟨64805695821584815131234803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172815188857559507016626141 64805695821584815131234803)
        ·
          refine ⟨97208543732377222696852205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64805695821584815131234803 97208543732377222696852205)
          ·
            refine ⟨36453203899641458511319577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97208543732377222696852205 36453203899641458511319577)
            ·
              refine ⟨27339902924731093883489683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36453203899641458511319577 27339902924731093883489683)
              ·
                refine ⟨41009854387096640825234525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27339902924731093883489683 41009854387096640825234525)
                ·
                  refine ⟨15378695395161240309462947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41009854387096640825234525 15378695395161240309462947)
                  ·
                    refine ⟨23068043092741860464194421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15378695395161240309462947 23068043092741860464194421)
                    ·
                      refine ⟨2162629039944549418518227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23068043092741860464194421 2162629039944549418518227)
                      ·
                        rfl

theorem cell23_4211705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_4211705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211705 prefixEnd_4211705 := by exact prefixLift 4211705
  have htrace : WordTrace (prefixWord ++ tailWord_4211705) baseStart_4211705 baseEnd_4211705 := by
    simpa [prefixWord, tailWord_4211705, baseEnd_4211705] using wordTrace_append hprefix tailTrace_4211705
  have hstable : (prefixWord ++ tailWord_4211705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211705).length < 2 ^ (prefixWord ++ tailWord_4211705).sum := by decide
  have hdescent : baseEnd_4211705 < baseStart_4211705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211736 : List Nat := [2, 1, 2, 3, 2, 4, 2, 1, 1, 1, 4]
def baseStart_4211736 : Nat := 118140960795 + 4211736 * 2 ^ 59
def prefixEnd_4211736 : Nat := 4983230072969 + 3 ^ 40 * 4211736 * 2
def baseEnd_4211736 : Nat := 2162644957844838797230585

theorem tailTrace_4211736 : CollatzResearch.WordTrace tailWord_4211736 prefixEnd_4211736 2162644957844838797230585 := by
  unfold tailWord_4211736
  simp only [CollatzResearch.WordTrace]
  refine ⟨76807315934803627043467531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102409754579738169391290041 76807315934803627043467531)
  ·
    refine ⟨115210973902205440565201297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76807315934803627043467531 115210973902205440565201297)
    ·
      refine ⟨86408230426654080423900973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115210973902205440565201297 86408230426654080423900973)
      ·
        refine ⟨32403086409995280158962865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86408230426654080423900973 32403086409995280158962865)
        ·
          refine ⟨24302314807496460119222149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32403086409995280158962865 24302314807496460119222149)
          ·
            refine ⟨4556684026405586272354153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24302314807496460119222149 4556684026405586272354153)
            ·
              refine ⟨3417513019804189704265615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4556684026405586272354153 3417513019804189704265615)
              ·
                refine ⟨5126269529706284556398423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3417513019804189704265615 5126269529706284556398423)
                ·
                  refine ⟨7689404294559426834597635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5126269529706284556398423 7689404294559426834597635)
                  ·
                    refine ⟨11534106441839140251896453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7689404294559426834597635 11534106441839140251896453)
                    ·
                      refine ⟨2162644957844838797230585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11534106441839140251896453 2162644957844838797230585)
                      ·
                        rfl

theorem cell23_4211736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_4211736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211736 prefixEnd_4211736 := by exact prefixLift 4211736
  have htrace : WordTrace (prefixWord ++ tailWord_4211736) baseStart_4211736 baseEnd_4211736 := by
    simpa [prefixWord, tailWord_4211736, baseEnd_4211736] using wordTrace_append hprefix tailTrace_4211736
  have hstable : (prefixWord ++ tailWord_4211736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211736).length < 2 ^ (prefixWord ++ tailWord_4211736).sum := by decide
  have hdescent : baseEnd_4211736 < baseStart_4211736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211746 : List Nat := [3, 3, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_4211746 : Nat := 118140960795 + 4211746 * 2 ^ 59
def prefixEnd_4211746 : Nat := 4983230072969 + 3 ^ 40 * 4211746 * 2
def baseEnd_4211746 : Nat := 720883364217127919368513

theorem tailTrace_4211746 : CollatzResearch.WordTrace tailWord_4211746 prefixEnd_4211746 720883364217127919368513 := by
  unfold tailWord_4211746
  simp only [CollatzResearch.WordTrace]
  refine ⟨38403749149892756448699773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102409997733047350529866061 38403749149892756448699773)
  ·
    refine ⟨14401405931209783668262415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38403749149892756448699773 14401405931209783668262415)
    ·
      refine ⟨21602108896814675502393623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14401405931209783668262415 21602108896814675502393623)
      ·
        refine ⟨32403163345222013253590435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21602108896814675502393623 32403163345222013253590435)
        ·
          refine ⟨48604745017833019880385653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32403163345222013253590435 48604745017833019880385653)
          ·
            refine ⟨4556694845421845613786155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48604745017833019880385653 4556694845421845613786155)
            ·
              refine ⟨6835042268132768420679233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4556694845421845613786155 6835042268132768420679233)
              ·
                refine ⟨5126281701099576315509425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6835042268132768420679233 5126281701099576315509425)
                ·
                  refine ⟨3844711275824682236632069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5126281701099576315509425 3844711275824682236632069)
                  ·
                    refine ⟨720883364217127919368513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3844711275824682236632069 720883364217127919368513)
                    ·
                      rfl

theorem cell23_4211746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_4211746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211746 prefixEnd_4211746 := by exact prefixLift 4211746
  have htrace : WordTrace (prefixWord ++ tailWord_4211746) baseStart_4211746 baseEnd_4211746 := by
    simpa [prefixWord, tailWord_4211746, baseEnd_4211746] using wordTrace_append hprefix tailTrace_4211746
  have hstable : (prefixWord ++ tailWord_4211746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211746).length < 2 ^ (prefixWord ++ tailWord_4211746).sum := by decide
  have hdescent : baseEnd_4211746 < baseStart_4211746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211766 : List Nat := [5, 1, 2, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_4211766 : Nat := 118140960795 + 4211766 * 2 ^ 59
def prefixEnd_4211766 : Nat := 4983230072969 + 3 ^ 40 * 4211766 * 2
def baseEnd_4211766 : Nat := 2162660362264473679855447

theorem tailTrace_4211766 : CollatzResearch.WordTrace tailWord_4211766 prefixEnd_4211766 2162660362264473679855447 := by
  unfold tailWord_4211766
  simp only [CollatzResearch.WordTrace]
  refine ⟨9600982878718660575657947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102410484039665712807018101 9600982878718660575657947)
  ·
    refine ⟨14401474318077990863486921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9600982878718660575657947 14401474318077990863486921)
    ·
      refine ⟨10801105738558493147615191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14401474318077990863486921 10801105738558493147615191)
      ·
        refine ⟨16201658607837739721422787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10801105738558493147615191 16201658607837739721422787)
        ·
          refine ⟨24302487911756609582134181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16201658607837739721422787 24302487911756609582134181)
          ·
            refine ⟨4556716483454364296650159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24302487911756609582134181 4556716483454364296650159)
            ·
              refine ⟨6835074725181546444975239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4556716483454364296650159 6835074725181546444975239)
              ·
                refine ⟨10252612087772319667462859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6835074725181546444975239 10252612087772319667462859)
                ·
                  refine ⟨15378918131658479501194289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10252612087772319667462859 15378918131658479501194289)
                  ·
                    refine ⟨11534188598743859625895717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15378918131658479501194289 11534188598743859625895717)
                    ·
                      refine ⟨2162660362264473679855447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11534188598743859625895717 2162660362264473679855447)
                      ·
                        rfl

theorem cell23_4211766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_4211766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211766 prefixEnd_4211766 := by exact prefixLift 4211766
  have htrace : WordTrace (prefixWord ++ tailWord_4211766) baseStart_4211766 baseEnd_4211766 := by
    simpa [prefixWord, tailWord_4211766, baseEnd_4211766] using wordTrace_append hprefix tailTrace_4211766
  have hstable : (prefixWord ++ tailWord_4211766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211766).length < 2 ^ (prefixWord ++ tailWord_4211766).sum := by decide
  have hdescent : baseEnd_4211766 < baseStart_4211766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211769 : List Nat := [1, 2, 1, 5, 2, 1, 3, 1, 1, 3, 3]
def baseStart_4211769 : Nat := 118140960795 + 4211769 * 2 ^ 59
def prefixEnd_4211769 : Nat := 4983230072969 + 3 ^ 40 * 4211769 * 2
def baseEnd_4211769 : Nat := 2162661902706437168117933

theorem tailTrace_4211769 : CollatzResearch.WordTrace tailWord_4211769 prefixEnd_4211769 2162661902706437168117933 := by
  unfold tailWord_4211769
  simp only [CollatzResearch.WordTrace]
  refine ⟨153615835478487700722886361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102410556985658467148590907 153615835478487700722886361)
  ·
    refine ⟨115211876608865775542164771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153615835478487700722886361 115211876608865775542164771)
    ·
      refine ⟨172817814913298663313247157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115211876608865775542164771 172817814913298663313247157)
      ·
        refine ⟨16201670148121749685616921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 172817814913298663313247157 16201670148121749685616921)
        ·
          refine ⟨12151252611091312264212691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16201670148121749685616921 12151252611091312264212691)
          ·
            refine ⟨18226878916636968396319037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12151252611091312264212691 18226878916636968396319037)
            ·
              refine ⟨6835079593738863148619639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18226878916636968396319037 6835079593738863148619639)
              ·
                refine ⟨10252619390608294722929459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6835079593738863148619639 10252619390608294722929459)
                ·
                  refine ⟨15378929085912442084394189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10252619390608294722929459 15378929085912442084394189)
                  ·
                    refine ⟨5767098407217165781647821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15378929085912442084394189 5767098407217165781647821)
                    ·
                      refine ⟨2162661902706437168117933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5767098407217165781647821 2162661902706437168117933)
                      ·
                        rfl

theorem cell23_4211769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_4211769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211769 prefixEnd_4211769 := by exact prefixLift 4211769
  have htrace : WordTrace (prefixWord ++ tailWord_4211769) baseStart_4211769 baseEnd_4211769 := by
    simpa [prefixWord, tailWord_4211769, baseEnd_4211769] using wordTrace_append hprefix tailTrace_4211769
  have hstable : (prefixWord ++ tailWord_4211769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211769).length < 2 ^ (prefixWord ++ tailWord_4211769).sum := by decide
  have hdescent : baseEnd_4211769 < baseStart_4211769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211785 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 4, 6]
def baseStart_4211785 : Nat := 118140960795 + 4211785 * 2 ^ 59
def prefixEnd_4211785 : Nat := 4983230072969 + 3 ^ 40 * 4211785 * 2
def baseEnd_4211785 : Nat := 720890039465636368505953

theorem tailTrace_4211785 : CollatzResearch.WordTrace tailWord_4211785 prefixEnd_4211785 720890039465636368505953 := by
  unfold tailWord_4211785
  simp only [CollatzResearch.WordTrace]
  refine ⟨153616419046429735455468809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102410946030953156970312539 153616419046429735455468809)
  ·
    refine ⟨115212314284822301591601607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153616419046429735455468809 115212314284822301591601607)
    ·
      refine ⟨172818471427233452387402411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115212314284822301591601607 172818471427233452387402411)
      ·
        refine ⟨259227707140850178581103617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172818471427233452387402411 259227707140850178581103617)
        ·
          refine ⟨194420780355637633935827713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259227707140850178581103617 194420780355637633935827713)
          ·
            refine ⟨145815585266728225451870785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194420780355637633935827713 145815585266728225451870785)
            ·
              refine ⟨109361688950046169088903089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145815585266728225451870785 109361688950046169088903089)
              ·
                refine ⟨82021266712534626816677317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109361688950046169088903089 82021266712534626816677317)
                ·
                  refine ⟨15378987508600242528126997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82021266712534626816677317 15378987508600242528126997)
                  ·
                    refine ⟨720890039465636368505953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15378987508600242528126997 720890039465636368505953)
                    ·
                      rfl

theorem cell23_4211785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 6].length) (baseStart_4211785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211785 prefixEnd_4211785 := by exact prefixLift 4211785
  have htrace : WordTrace (prefixWord ++ tailWord_4211785) baseStart_4211785 baseEnd_4211785 := by
    simpa [prefixWord, tailWord_4211785, baseEnd_4211785] using wordTrace_append hprefix tailTrace_4211785
  have hstable : (prefixWord ++ tailWord_4211785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211785).length < 2 ^ (prefixWord ++ tailWord_4211785).sum := by decide
  have hdescent : baseEnd_4211785 < baseStart_4211785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211795 : List Nat := [1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 5]
def baseStart_4211795 : Nat := 118140960795 + 4211795 * 2 ^ 59
def prefixEnd_4211795 : Nat := 4983230072969 + 3 ^ 40 * 4211795 * 2
def baseEnd_4211795 : Nat := 2162675253203454066392813

theorem tailTrace_4211795 : CollatzResearch.WordTrace tailWord_4211795 prefixEnd_4211795 2162675253203454066392813 := by
  unfold tailWord_4211795
  simp only [CollatzResearch.WordTrace]
  refine ⟨153616783776393507163332839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102411189184262338108888559 153616783776393507163332839)
  ·
    refine ⟨230425175664590260744999259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153616783776393507163332839 230425175664590260744999259)
    ·
      refine ⟨345637763496885391117498889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230425175664590260744999259 345637763496885391117498889)
      ·
        refine ⟨259228322622664043338124167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345637763496885391117498889 259228322622664043338124167)
        ·
          refine ⟨388842483933996065007186251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259228322622664043338124167 388842483933996065007186251)
          ·
            refine ⟨583263725900994097510779377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388842483933996065007186251 583263725900994097510779377)
            ·
              refine ⟨437447794425745573133084533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 583263725900994097510779377 437447794425745573133084533)
              ·
                refine ⟨41010730727413647481226675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 437447794425745573133084533 41010730727413647481226675)
                ·
                  refine ⟨61516096091120471221840013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41010730727413647481226675 61516096091120471221840013)
                  ·
                    refine ⟨23068536034170176708190005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61516096091120471221840013 23068536034170176708190005)
                    ·
                      refine ⟨2162675253203454066392813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23068536034170176708190005 2162675253203454066392813)
                      ·
                        rfl

theorem cell23_4211795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_4211795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211795 prefixEnd_4211795 := by exact prefixLift 4211795
  have htrace : WordTrace (prefixWord ++ tailWord_4211795) baseStart_4211795 baseEnd_4211795 := by
    simpa [prefixWord, tailWord_4211795, baseEnd_4211795] using wordTrace_append hprefix tailTrace_4211795
  have hstable : (prefixWord ++ tailWord_4211795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211795).length < 2 ^ (prefixWord ++ tailWord_4211795).sum := by decide
  have hdescent : baseEnd_4211795 < baseStart_4211795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211796 : List Nat := [2, 4, 1, 1, 1, 1, 4, 3, 1, 3, 2]
def baseStart_4211796 : Nat := 118140960795 + 4211796 * 2 ^ 59
def prefixEnd_4211796 : Nat := 4983230072969 + 3 ^ 40 * 4211796 * 2
def baseEnd_4211796 : Nat := 2162675766684108562480309

theorem tailTrace_4211796 : CollatzResearch.WordTrace tailWord_4211796 prefixEnd_4211796 2162675766684108562480309 := by
  unfold tailWord_4211796
  simp only [CollatzResearch.WordTrace]
  refine ⟨76808410124694942167059621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102411213499593256222746161 76808410124694942167059621)
  ·
    refine ⟨14401576898380301656323679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76808410124694942167059621 14401576898380301656323679)
    ·
      refine ⟨21602365347570452484485519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14401576898380301656323679 21602365347570452484485519)
      ·
        refine ⟨32403548021355678726728279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21602365347570452484485519 32403548021355678726728279)
        ·
          refine ⟨48605322032033518090092419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32403548021355678726728279 48605322032033518090092419)
          ·
            refine ⟨72907983048050277135138629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48605322032033518090092419 72907983048050277135138629)
            ·
              refine ⟨13670246821509426962838493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72907983048050277135138629 13670246821509426962838493)
              ·
                refine ⟨5126342558066035111064435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13670246821509426962838493 5126342558066035111064435)
                ·
                  refine ⟨7689513837099052666596653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5126342558066035111064435 7689513837099052666596653)
                  ·
                    refine ⟨2883567688912144749973745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7689513837099052666596653 2883567688912144749973745)
                    ·
                      refine ⟨2162675766684108562480309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2883567688912144749973745 2162675766684108562480309)
                      ·
                        rfl

theorem cell23_4211796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_4211796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211796 prefixEnd_4211796 := by exact prefixLift 4211796
  have htrace : WordTrace (prefixWord ++ tailWord_4211796) baseStart_4211796 baseEnd_4211796 := by
    simpa [prefixWord, tailWord_4211796, baseEnd_4211796] using wordTrace_append hprefix tailTrace_4211796
  have hstable : (prefixWord ++ tailWord_4211796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211796).length < 2 ^ (prefixWord ++ tailWord_4211796).sum := by decide
  have hdescent : baseEnd_4211796 < baseStart_4211796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211812 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 2, 4, 3]
def baseStart_4211812 : Nat := 118140960795 + 4211812 * 2 ^ 59
def prefixEnd_4211812 : Nat := 4983230072969 + 3 ^ 40 * 4211812 * 2
def baseEnd_4211812 : Nat := 2162683982374580499880235

theorem tailTrace_4211812 : CollatzResearch.WordTrace tailWord_4211812 prefixEnd_4211812 2162683982374580499880235 := by
  unfold tailWord_4211812
  simp only [CollatzResearch.WordTrace]
  refine ⟨76808701908665959533350845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102411602544887946044467793 76808701908665959533350845)
  ·
    refine ⟨28803263215749734825006567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76808701908665959533350845 28803263215749734825006567)
    ·
      refine ⟨43204894823624602237509851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28803263215749734825006567 43204894823624602237509851)
      ·
        refine ⟨64807342235436903356264777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43204894823624602237509851 64807342235436903356264777)
        ·
          refine ⟨48605506676577677517198583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64807342235436903356264777 48605506676577677517198583)
          ·
            refine ⟨72908260014866516275797875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48605506676577677517198583 72908260014866516275797875)
            ·
              refine ⟨109362390022299774413696813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72908260014866516275797875 109362390022299774413696813)
              ·
                refine ⟨41010896258362415405136305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109362390022299774413696813 41010896258362415405136305)
                ·
                  refine ⟨30758172193771811553852229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41010896258362415405136305 30758172193771811553852229)
                  ·
                    refine ⟨5767157286332214666347293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30758172193771811553852229 5767157286332214666347293)
                    ·
                      refine ⟨2162683982374580499880235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5767157286332214666347293 2162683982374580499880235)
                      ·
                        rfl

theorem cell23_4211812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_4211812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211812 prefixEnd_4211812 := by exact prefixLift 4211812
  have htrace : WordTrace (prefixWord ++ tailWord_4211812) baseStart_4211812 baseEnd_4211812 := by
    simpa [prefixWord, tailWord_4211812, baseEnd_4211812] using wordTrace_append hprefix tailTrace_4211812
  have hstable : (prefixWord ++ tailWord_4211812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211812).length < 2 ^ (prefixWord ++ tailWord_4211812).sum := by decide
  have hdescent : baseEnd_4211812 < baseStart_4211812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211835 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 8]
def baseStart_4211835 : Nat := 118140960795 + 4211835 * 2 ^ 59
def prefixEnd_4211835 : Nat := 4983230072969 + 3 ^ 40 * 4211835 * 2
def baseEnd_4211835 : Nat := 2162695792429633909892629

theorem tailTrace_4211835 : CollatzResearch.WordTrace tailWord_4211835 prefixEnd_4211835 2162695792429633909892629 := by
  unfold tailWord_4211835
  simp only [CollatzResearch.WordTrace]
  refine ⟨153618242696248593994788959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102412161797499062663192639 153618242696248593994788959)
  ·
    refine ⟨230427364044372890992183439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153618242696248593994788959 230427364044372890992183439)
    ·
      refine ⟨345641046066559336488275159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230427364044372890992183439 345641046066559336488275159)
      ·
        refine ⟨518461569099839004732412739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345641046066559336488275159 518461569099839004732412739)
        ·
          refine ⟨777692353649758507098619109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518461569099839004732412739 777692353649758507098619109)
          ·
            refine ⟨145817316309329720080991083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 777692353649758507098619109 145817316309329720080991083)
            ·
              refine ⟨218725974463994580121486625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145817316309329720080991083 218725974463994580121486625)
              ·
                refine ⟨164044480847995935091114969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218725974463994580121486625 164044480847995935091114969)
                ·
                  refine ⟨123033360635996951318336227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 164044480847995935091114969 123033360635996951318336227)
                  ·
                    refine ⟨184550040953995426977504341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 123033360635996951318336227 184550040953995426977504341)
                    ·
                      refine ⟨2162695792429633909892629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 184550040953995426977504341 2162695792429633909892629)
                      ·
                        rfl

theorem cell23_4211835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 8].length) (baseStart_4211835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211835 prefixEnd_4211835 := by exact prefixLift 4211835
  have htrace : WordTrace (prefixWord ++ tailWord_4211835) baseStart_4211835 baseEnd_4211835 := by
    simpa [prefixWord, tailWord_4211835, baseEnd_4211835] using wordTrace_append hprefix tailTrace_4211835
  have hstable : (prefixWord ++ tailWord_4211835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211835).length < 2 ^ (prefixWord ++ tailWord_4211835).sum := by decide
  have hdescent : baseEnd_4211835 < baseStart_4211835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211866 : List Nat := [3, 1, 1, 5, 1, 2, 1, 4, 5]
def baseStart_4211866 : Nat := 118140960795 + 4211866 * 2 ^ 59
def prefixEnd_4211866 : Nat := 4983230072969 + 3 ^ 40 * 4211866 * 2
def baseEnd_4211866 : Nat := 240301301147769254289443

theorem tailTrace_4211866 : CollatzResearch.WordTrace tailWord_4211866 prefixEnd_4211866 240301301147769254289443 := by
  unfold tailWord_4211866
  simp only [CollatzResearch.WordTrace]
  refine ⟨38404843339784071572291863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102412915572757524192778301 38404843339784071572291863)
  ·
    refine ⟨57607265009676107358437795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38404843339784071572291863 57607265009676107358437795)
    ·
      refine ⟨86410897514514161037656693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57607265009676107358437795 86410897514514161037656693)
      ·
        refine ⟨8101021641985702597280315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86410897514514161037656693 8101021641985702597280315)
        ·
          refine ⟨12151532462978553895920473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8101021641985702597280315 12151532462978553895920473)
          ·
            refine ⟨9113649347233915421940355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12151532462978553895920473 9113649347233915421940355)
            ·
              refine ⟨13670474020850873132910533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9113649347233915421940355 13670474020850873132910533)
              ·
                refine ⟨2563213878909538712420725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13670474020850873132910533 2563213878909538712420725)
                ·
                  refine ⟨240301301147769254289443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2563213878909538712420725 240301301147769254289443)
                  ·
                    rfl

theorem cell23_4211866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 5].length) (baseStart_4211866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211866 prefixEnd_4211866 := by exact prefixLift 4211866
  have htrace : WordTrace (prefixWord ++ tailWord_4211866) baseStart_4211866 baseEnd_4211866 := by
    simpa [prefixWord, tailWord_4211866, baseEnd_4211866] using wordTrace_append hprefix tailTrace_4211866
  have hstable : (prefixWord ++ tailWord_4211866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211866).length < 2 ^ (prefixWord ++ tailWord_4211866).sum := by decide
  have hdescent : baseEnd_4211866 < baseStart_4211866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211869 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 1, 7, 2]
def baseStart_4211869 : Nat := 118140960795 + 4211869 * 2 ^ 59
def prefixEnd_4211869 : Nat := 4983230072969 + 3 ^ 40 * 4211869 * 2
def baseEnd_4211869 : Nat := 2162713250771886776867473

theorem tailTrace_4211869 : CollatzResearch.WordTrace tailWord_4211869 prefixEnd_4211869 2162713250771886776867473 := by
  unfold tailWord_4211869
  simp only [CollatzResearch.WordTrace]
  refine ⟨153619482778125417801526661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102412988518750278534351107 153619482778125417801526661)
  ·
    refine ⟨28803653020898515837786249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153619482778125417801526661 28803653020898515837786249)
    ·
      refine ⟨21602739765673886878339687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28803653020898515837786249 21602739765673886878339687)
      ·
        refine ⟨32404109648510830317509531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21602739765673886878339687 32404109648510830317509531)
        ·
          refine ⟨48606164472766245476264297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32404109648510830317509531 48606164472766245476264297)
          ·
            refine ⟨36454623354574684107198223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48606164472766245476264297 36454623354574684107198223)
            ·
              refine ⟨54681935031862026160797335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36454623354574684107198223 54681935031862026160797335)
              ·
                refine ⟨82022902547793039241196003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54681935031862026160797335 82022902547793039241196003)
                ·
                  refine ⟨123034353821689558861794005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82022902547793039241196003 123034353821689558861794005)
                  ·
                    refine ⟨2883617667695849035823297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 123034353821689558861794005 2883617667695849035823297)
                    ·
                      refine ⟨2162713250771886776867473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2883617667695849035823297 2162713250771886776867473)
                      ·
                        rfl

theorem cell23_4211869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_4211869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211869 prefixEnd_4211869 := by exact prefixLift 4211869
  have htrace : WordTrace (prefixWord ++ tailWord_4211869) baseStart_4211869 baseEnd_4211869 := by
    simpa [prefixWord, tailWord_4211869, baseEnd_4211869] using wordTrace_append hprefix tailTrace_4211869
  have hstable : (prefixWord ++ tailWord_4211869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211869).length < 2 ^ (prefixWord ++ tailWord_4211869).sum := by decide
  have hdescent : baseEnd_4211869 < baseStart_4211869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211872 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 5]
def baseStart_4211872 : Nat := 118140960795 + 4211872 * 2 ^ 59
def prefixEnd_4211872 : Nat := 4983230072969 + 3 ^ 40 * 4211872 * 2
def baseEnd_4211872 : Nat := 2162714791213850265129959

theorem tailTrace_4211872 : CollatzResearch.WordTrace tailWord_4211872 prefixEnd_4211872 2162714791213850265129959 := by
  unfold tailWord_4211872
  simp only [CollatzResearch.WordTrace]
  refine ⟨76809796098557274656942935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102413061464743032875923913 76809796098557274656942935)
  ·
    refine ⟨115214694147835911985414403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76809796098557274656942935 115214694147835911985414403)
    ·
      refine ⟨172822041221753867978121605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115214694147835911985414403 172822041221753867978121605)
      ·
        refine ⟨32404132729078850245897801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172822041221753867978121605 32404132729078850245897801)
        ·
          refine ⟨24303099546809137684423351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32404132729078850245897801 24303099546809137684423351)
          ·
            refine ⟨36454649320213706526635027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24303099546809137684423351 36454649320213706526635027)
            ·
              refine ⟨54681973980320559789952541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36454649320213706526635027 54681973980320559789952541)
              ·
                refine ⟨20505740242620209921232203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54681973980320559789952541 20505740242620209921232203)
                ·
                  refine ⟨30758610363930314881848305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20505740242620209921232203 30758610363930314881848305)
                  ·
                    refine ⟨23068957772947736161386229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30758610363930314881848305 23068957772947736161386229)
                    ·
                      refine ⟨2162714791213850265129959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23068957772947736161386229 2162714791213850265129959)
                      ·
                        rfl

theorem cell23_4211872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_4211872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211872 prefixEnd_4211872 := by exact prefixLift 4211872
  have htrace : WordTrace (prefixWord ++ tailWord_4211872) baseStart_4211872 baseEnd_4211872 := by
    simpa [prefixWord, tailWord_4211872, baseEnd_4211872] using wordTrace_append hprefix tailTrace_4211872
  have hstable : (prefixWord ++ tailWord_4211872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211872).length < 2 ^ (prefixWord ++ tailWord_4211872).sum := by decide
  have hdescent : baseEnd_4211872 < baseStart_4211872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211912 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_4211912 : Nat := 118140960795 + 4211912 * 2 ^ 59
def prefixEnd_4211912 : Nat := 4983230072969 + 3 ^ 40 * 4211912 * 2
def baseEnd_4211912 : Nat := 2162735330440030108629775

theorem tailTrace_4211912 : CollatzResearch.WordTrace tailWord_4211912 prefixEnd_4211912 2162735330440030108629775 := by
  unfold tailWord_4211912
  simp only [CollatzResearch.WordTrace]
  refine ⟨76810525558484818072670995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102414034077979757430227993 76810525558484818072670995)
  ·
    refine ⟨115215788337727227109006493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76810525558484818072670995 115215788337727227109006493)
    ·
      refine ⟨43205920626647710165877435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115215788337727227109006493 43205920626647710165877435)
      ·
        refine ⟨64808880939971565248816153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43205920626647710165877435 64808880939971565248816153)
        ·
          refine ⟨48606660704978673936612115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64808880939971565248816153 48606660704978673936612115)
          ·
            refine ⟨72909991057468010904918173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48606660704978673936612115 72909991057468010904918173)
            ·
              refine ⟨27341246646550504089344315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72909991057468010904918173 27341246646550504089344315)
              ·
                refine ⟨41011869969825756134016473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27341246646550504089344315 41011869969825756134016473)
                ·
                  refine ⟨30758902477369317100512355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41011869969825756134016473 30758902477369317100512355)
                  ·
                    refine ⟨46138353716053975650768533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30758902477369317100512355 46138353716053975650768533)
                    ·
                      refine ⟨2162735330440030108629775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46138353716053975650768533 2162735330440030108629775)
                      ·
                        rfl

theorem cell23_4211912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_4211912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211912 prefixEnd_4211912 := by exact prefixLift 4211912
  have htrace : WordTrace (prefixWord ++ tailWord_4211912) baseStart_4211912 baseEnd_4211912 := by
    simpa [prefixWord, tailWord_4211912, baseEnd_4211912] using wordTrace_append hprefix tailTrace_4211912
  have hstable : (prefixWord ++ tailWord_4211912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211912).length < 2 ^ (prefixWord ++ tailWord_4211912).sum := by decide
  have hdescent : baseEnd_4211912 < baseStart_4211912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4211989 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_4211989 : Nat := 118140960795 + 4211989 * 2 ^ 59
def prefixEnd_4211989 : Nat := 4983230072969 + 3 ^ 40 * 4211989 * 2
def baseEnd_4211989 : Nat := 2162774868450426307366921

theorem tailTrace_4211989 : CollatzResearch.WordTrace tailWord_4211989 prefixEnd_4211989 2162774868450426307366921 := by
  unfold tailWord_4211989
  simp only [CollatzResearch.WordTrace]
  refine ⟨153623859537690678295895021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102415906358460452197263347 153623859537690678295895021)
  ·
    refine ⟨57608947326634004360960633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153623859537690678295895021 57608947326634004360960633)
    ·
      refine ⟨43206710494975503270720475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57608947326634004360960633 43206710494975503270720475)
      ·
        refine ⟨64810065742463254906080713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43206710494975503270720475 64810065742463254906080713)
        ·
          refine ⟨48607549306847441179560535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64810065742463254906080713 48607549306847441179560535)
          ·
            refine ⟨72911323960271161769340803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48607549306847441179560535 72911323960271161769340803)
            ·
              refine ⟨109366985940406742654011205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72911323960271161769340803 109366985940406742654011205)
              ·
                refine ⟨20506309863826264247627101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109366985940406742654011205 20506309863826264247627101)
                ·
                  refine ⟨7689866198934849092860163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20506309863826264247627101 7689866198934849092860163)
                  ·
                    refine ⟨11534799298402273639290245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7689866198934849092860163 11534799298402273639290245)
                    ·
                      refine ⟨2162774868450426307366921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11534799298402273639290245 2162774868450426307366921)
                      ·
                        rfl

theorem cell23_4211989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_4211989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4211989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4211989 prefixEnd_4211989 := by exact prefixLift 4211989
  have htrace : WordTrace (prefixWord ++ tailWord_4211989) baseStart_4211989 baseEnd_4211989 := by
    simpa [prefixWord, tailWord_4211989, baseEnd_4211989] using wordTrace_append hprefix tailTrace_4211989
  have hstable : (prefixWord ++ tailWord_4211989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4211989).length < 2 ^ (prefixWord ++ tailWord_4211989).sum := by decide
  have hdescent : baseEnd_4211989 < baseStart_4211989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4211989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212010 : List Nat := [3, 1, 4, 2, 1, 2, 2, 1, 2, 3, 2]
def baseStart_4212010 : Nat := 118140960795 + 4212010 * 2 ^ 59
def prefixEnd_4212010 : Nat := 4983230072969 + 3 ^ 40 * 4212010 * 2
def baseEnd_4212010 : Nat := 2162785651544170725204325

theorem tailTrace_4212010 : CollatzResearch.WordTrace tailWord_4212010 prefixEnd_4212010 2162785651544170725204325 := by
  unfold tailWord_4212010
  simp only [CollatzResearch.WordTrace]
  refine ⟨38406156367653649720602371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102416416980409732588272989 38406156367653649720602371)
  ·
    refine ⟨57609234551480474580903557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38406156367653649720602371 57609234551480474580903557)
    ·
      refine ⟨10801731478402588983919417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57609234551480474580903557 10801731478402588983919417)
      ·
        refine ⟨8101298608801941737939563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10801731478402588983919417 8101298608801941737939563)
        ·
          refine ⟨12151947913202912606909345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8101298608801941737939563 12151947913202912606909345)
          ·
            refine ⟨9113960934902184455182009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12151947913202912606909345 9113960934902184455182009)
            ·
              refine ⟨6835470701176638341386507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9113960934902184455182009 6835470701176638341386507)
              ·
                refine ⟨10253206051764957512079761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6835470701176638341386507 10253206051764957512079761)
                ·
                  refine ⟨7689904538823718134059821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10253206051764957512079761 7689904538823718134059821)
                  ·
                    refine ⟨2883714202058894300272433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7689904538823718134059821 2883714202058894300272433)
                    ·
                      refine ⟨2162785651544170725204325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2883714202058894300272433 2162785651544170725204325)
                      ·
                        rfl

theorem cell23_4212010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_4212010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212010 prefixEnd_4212010 := by exact prefixLift 4212010
  have htrace : WordTrace (prefixWord ++ tailWord_4212010) baseStart_4212010 baseEnd_4212010 := by
    simpa [prefixWord, tailWord_4212010, baseEnd_4212010] using wordTrace_append hprefix tailTrace_4212010
  have hstable : (prefixWord ++ tailWord_4212010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212010).length < 2 ^ (prefixWord ++ tailWord_4212010).sum := by decide
  have hdescent : baseEnd_4212010 < baseStart_4212010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212019 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 4]
def baseStart_4212019 : Nat := 118140960795 + 4212019 * 2 ^ 59
def prefixEnd_4212019 : Nat := 4983230072969 + 3 ^ 40 * 4212019 * 2
def baseEnd_4212019 : Nat := 2162790272870061189991783

theorem tailTrace_4212019 : CollatzResearch.WordTrace tailWord_4212019 prefixEnd_4212019 2162790272870061189991783 := by
  unfold tailWord_4212019
  simp only [CollatzResearch.WordTrace]
  refine ⟨153624953727581993419487111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102416635818387995612991407 153624953727581993419487111)
  ·
    refine ⟨230437430591372990129230667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153624953727581993419487111 230437430591372990129230667)
    ·
      refine ⟨345656145887059485193846001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230437430591372990129230667 345656145887059485193846001)
      ·
        refine ⟨259242109415294613895384501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345656145887059485193846001 259242109415294613895384501)
        ·
          refine ⟨24303947757683870052692297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 259242109415294613895384501 24303947757683870052692297)
          ·
            refine ⟨18227960818262902539519223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24303947757683870052692297 18227960818262902539519223)
            ·
              refine ⟨27341941227394353809278835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18227960818262902539519223 27341941227394353809278835)
              ·
                refine ⟨41012911841091530713918253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27341941227394353809278835 41012911841091530713918253)
                ·
                  refine ⟨15379841940409324017719345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41012911841091530713918253 15379841940409324017719345)
                  ·
                    refine ⟨11534881455306993013289509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15379841940409324017719345 11534881455306993013289509)
                    ·
                      refine ⟨2162790272870061189991783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11534881455306993013289509 2162790272870061189991783)
                      ·
                        rfl

theorem cell23_4212019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_4212019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212019 prefixEnd_4212019 := by exact prefixLift 4212019
  have htrace : WordTrace (prefixWord ++ tailWord_4212019) baseStart_4212019 baseEnd_4212019 := by
    simpa [prefixWord, tailWord_4212019, baseEnd_4212019] using wordTrace_append hprefix tailTrace_4212019
  have hstable : (prefixWord ++ tailWord_4212019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212019).length < 2 ^ (prefixWord ++ tailWord_4212019).sum := by decide
  have hdescent : baseEnd_4212019 < baseStart_4212019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212029 : List Nat := [1, 4, 1, 5, 12]
def baseStart_4212029 : Nat := 118140960795 + 4212029 * 2 ^ 59
def prefixEnd_4212029 : Nat := 4983230072969 + 3 ^ 40 * 4212029 * 2
def baseEnd_4212029 : Nat := 2966797541394521468953

theorem tailTrace_4212029 : CollatzResearch.WordTrace tailWord_4212029 prefixEnd_4212029 2966797541394521468953 := by
  unfold tailWord_4212029
  simp only [CollatzResearch.WordTrace]
  refine ⟨153625318457545765127351141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102416878971697176751567427 153625318457545765127351141)
  ·
    refine ⟨28804747210789830961378339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153625318457545765127351141 28804747210789830961378339)
    ·
      refine ⟨43207120816184746442067509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28804747210789830961378339 43207120816184746442067509)
      ·
        refine ⟨4050667576517319978943829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 43207120816184746442067509 4050667576517319978943829)
        ·
          refine ⟨2966797541394521468953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4050667576517319978943829 2966797541394521468953)
          ·
            rfl

theorem cell23_4212029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 12].length) (baseStart_4212029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212029 prefixEnd_4212029 := by exact prefixLift 4212029
  have htrace : WordTrace (prefixWord ++ tailWord_4212029) baseStart_4212029 baseEnd_4212029 := by
    simpa [prefixWord, tailWord_4212029, baseEnd_4212029] using wordTrace_append hprefix tailTrace_4212029
  have hstable : (prefixWord ++ tailWord_4212029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212029).length < 2 ^ (prefixWord ++ tailWord_4212029).sum := by decide
  have hdescent : baseEnd_4212029 < baseStart_4212029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212033 : List Nat := [1, 2, 5, 2, 1, 1, 1, 4, 2, 4]
def baseStart_4212033 : Nat := 118140960795 + 4212033 * 2 ^ 59
def prefixEnd_4212033 : Nat := 4983230072969 + 3 ^ 40 * 4212033 * 2
def baseEnd_4212033 : Nat := 720932487199741378405573

theorem tailTrace_4212033 : CollatzResearch.WordTrace tailWord_4212033 prefixEnd_4212033 720932487199741378405573 := by
  unfold tailWord_4212033
  simp only [CollatzResearch.WordTrace]
  refine ⟨153625464349531273810496753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102416976233020849206997835 153625464349531273810496753)
  ·
    refine ⟨115219098262148455357872565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153625464349531273810496753 115219098262148455357872565)
    ·
      refine ⟨10801790462076417689800553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115219098262148455357872565 10801790462076417689800553)
      ·
        refine ⟨8101342846557313267350415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10801790462076417689800553 8101342846557313267350415)
        ·
          refine ⟨12152014269835969901025623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8101342846557313267350415 12152014269835969901025623)
          ·
            refine ⟨18228021404753954851538435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12152014269835969901025623 18228021404753954851538435)
            ·
              refine ⟨27342032107130932277307653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18228021404753954851538435 27342032107130932277307653)
              ·
                refine ⟨5126631020087049801995185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27342032107130932277307653 5126631020087049801995185)
                ·
                  refine ⟨3844973265065287351496389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5126631020087049801995185 3844973265065287351496389)
                  ·
                    refine ⟨720932487199741378405573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3844973265065287351496389 720932487199741378405573)
                    ·
                      rfl

theorem cell23_4212033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_4212033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212033 prefixEnd_4212033 := by exact prefixLift 4212033
  have htrace : WordTrace (prefixWord ++ tailWord_4212033) baseStart_4212033 baseEnd_4212033 := by
    simpa [prefixWord, tailWord_4212033, baseEnd_4212033] using wordTrace_append hprefix tailTrace_4212033
  have hstable : (prefixWord ++ tailWord_4212033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212033).length < 2 ^ (prefixWord ++ tailWord_4212033).sum := by decide
  have hdescent : baseEnd_4212033 < baseStart_4212033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212056 : List Nat := [2, 1, 2, 2, 1, 1, 6, 1, 1, 3, 3]
def baseStart_4212056 : Nat := 118140960795 + 4212056 * 2 ^ 59
def prefixEnd_4212056 : Nat := 4983230072969 + 3 ^ 40 * 4212056 * 2
def baseEnd_4212056 : Nat := 2162809271654277545229113

theorem tailTrace_4212056 : CollatzResearch.WordTrace tailWord_4212056 prefixEnd_4212056 2162809271654277545229113 := by
  unfold tailWord_4212056
  simp only [CollatzResearch.WordTrace]
  refine ⟨76813151614223974369292011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102417535485631965825722681 76813151614223974369292011)
  ·
    refine ⟨115219727421335961553938017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76813151614223974369292011 115219727421335961553938017)
    ·
      refine ⟨86414795566001971165453513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115219727421335961553938017 86414795566001971165453513)
      ·
        refine ⟨64811096674501478374090135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86414795566001971165453513 64811096674501478374090135)
        ·
          refine ⟨97216645011752217561135203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64811096674501478374090135 97216645011752217561135203)
          ·
            refine ⟨145824967517628326341702805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97216645011752217561135203 145824967517628326341702805)
            ·
              refine ⟨6835545352388827797267319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 145824967517628326341702805 6835545352388827797267319)
              ·
                refine ⟨10253318028583241695900979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6835545352388827797267319 10253318028583241695900979)
                ·
                  refine ⟨15379977042874862543851469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10253318028583241695900979 15379977042874862543851469)
                  ·
                    refine ⟨5767491391078073453944301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15379977042874862543851469 5767491391078073453944301)
                    ·
                      refine ⟨2162809271654277545229113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5767491391078073453944301 2162809271654277545229113)
                      ·
                        rfl

theorem cell23_4212056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_4212056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212056 prefixEnd_4212056 := by exact prefixLift 4212056
  have htrace : WordTrace (prefixWord ++ tailWord_4212056) baseStart_4212056 baseEnd_4212056 := by
    simpa [prefixWord, tailWord_4212056, baseEnd_4212056] using wordTrace_append hprefix tailTrace_4212056
  have hstable : (prefixWord ++ tailWord_4212056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212056).length < 2 ^ (prefixWord ++ tailWord_4212056).sum := by decide
  have hdescent : baseEnd_4212056 < baseStart_4212056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212061 : List Nat := [1, 4, 5, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_4212061 : Nat := 118140960795 + 4212061 * 2 ^ 59
def prefixEnd_4212061 : Nat := 4983230072969 + 3 ^ 40 * 4212061 * 2
def baseEnd_4212061 : Nat := 2162811839057550025666591

theorem tailTrace_4212061 : CollatzResearch.WordTrace tailWord_4212061 prefixEnd_4212061 2162811839057550025666591 := by
  unfold tailWord_4212061
  simp only [CollatzResearch.WordTrace]
  refine ⟨153626485593429834592516037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102417657062286556395010691 153626485593429834592516037)
  ·
    refine ⟨28804966048768093986096757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153626485593429834592516037 28804966048768093986096757)
    ·
      refine ⟨2700465567072008811196571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28804966048768093986096757 2700465567072008811196571)
      ·
        refine ⟨4050698350608013216794857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2700465567072008811196571 4050698350608013216794857)
        ·
          refine ⟨3038023762956009912596143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4050698350608013216794857 3038023762956009912596143)
          ·
            refine ⟨4557035644434014868894215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3038023762956009912596143 4557035644434014868894215)
            ·
              refine ⟨6835553466651022303341323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4557035644434014868894215 6835553466651022303341323)
              ·
                refine ⟨10253330199976533455011985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6835553466651022303341323 10253330199976533455011985)
                ·
                  refine ⟨7689997649982400091258989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10253330199976533455011985 7689997649982400091258989)
                  ·
                    refine ⟨2883749118743400034222121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7689997649982400091258989 2883749118743400034222121)
                    ·
                      refine ⟨2162811839057550025666591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2883749118743400034222121 2162811839057550025666591)
                      ·
                        rfl

theorem cell23_4212061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_4212061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212061 prefixEnd_4212061 := by exact prefixLift 4212061
  have htrace : WordTrace (prefixWord ++ tailWord_4212061) baseStart_4212061 baseEnd_4212061 := by
    simpa [prefixWord, tailWord_4212061, baseEnd_4212061] using wordTrace_append hprefix tailTrace_4212061
  have hstable : (prefixWord ++ tailWord_4212061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212061).length < 2 ^ (prefixWord ++ tailWord_4212061).sum := by decide
  have hdescent : baseEnd_4212061 < baseStart_4212061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212069 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 2, 2, 5]
def baseStart_4212069 : Nat := 118140960795 + 4212069 * 2 ^ 59
def prefixEnd_4212069 : Nat := 4983230072969 + 3 ^ 40 * 4212069 * 2
def baseEnd_4212069 : Nat := 2162815946902785994366553

theorem tailTrace_4212069 : CollatzResearch.WordTrace tailWord_4212069 prefixEnd_4212069 2162815946902785994366553 := by
  unfold tailWord_4212069
  simp only [CollatzResearch.WordTrace]
  refine ⟨153626777377400851958807261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102417851584933901305871507 153626777377400851958807261)
  ·
    refine ⟨57610041516525319484552723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153626777377400851958807261 57610041516525319484552723)
    ·
      refine ⟨86415062274787979226829085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57610041516525319484552723 86415062274787979226829085)
      ·
        refine ⟨32405648353045492210060907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86415062274787979226829085 32405648353045492210060907)
        ·
          refine ⟨48608472529568238315091361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32405648353045492210060907 48608472529568238315091361)
          ·
            refine ⟨36456354397176178736318521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48608472529568238315091361 36456354397176178736318521)
            ·
              refine ⟨27342265797882134052238891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36456354397176178736318521 27342265797882134052238891)
              ·
                refine ⟨41013398696823201078358337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27342265797882134052238891 41013398696823201078358337)
                ·
                  refine ⟨30760049022617400808768753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41013398696823201078358337 30760049022617400808768753)
                  ·
                    refine ⟨23070036766963050606576565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30760049022617400808768753 23070036766963050606576565)
                    ·
                      refine ⟨2162815946902785994366553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23070036766963050606576565 2162815946902785994366553)
                      ·
                        rfl

theorem cell23_4212069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_4212069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212069 prefixEnd_4212069 := by exact prefixLift 4212069
  have htrace : WordTrace (prefixWord ++ tailWord_4212069) baseStart_4212069 baseEnd_4212069 := by
    simpa [prefixWord, tailWord_4212069, baseEnd_4212069] using wordTrace_append hprefix tailTrace_4212069
  have hstable : (prefixWord ++ tailWord_4212069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212069).length < 2 ^ (prefixWord ++ tailWord_4212069).sum := by decide
  have hdescent : baseEnd_4212069 < baseStart_4212069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212074 : List Nat := [3, 1, 3, 3, 2, 1, 2, 3, 1, 2, 2]
def baseStart_4212074 : Nat := 118140960795 + 4212074 * 2 ^ 59
def prefixEnd_4212074 : Nat := 4983230072969 + 3 ^ 40 * 4212074 * 2
def baseEnd_4212074 : Nat := 2162818514306058474804031

theorem tailTrace_4212074 : CollatzResearch.WordTrace tailWord_4212074 prefixEnd_4212074 2162818514306058474804031 := by
  unfold tailWord_4212074
  simp only [CollatzResearch.WordTrace]
  refine ⟨38406739935595684453184819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102417973161588491875159517 38406739935595684453184819)
  ·
    refine ⟨57610109903393526679777229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38406739935595684453184819 57610109903393526679777229)
    ·
      refine ⟨21603791213772572504916461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57610109903393526679777229 21603791213772572504916461)
      ·
        refine ⟨8101421705164714689343673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21603791213772572504916461 8101421705164714689343673)
        ·
          refine ⟨6076066278873536017007755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8101421705164714689343673 6076066278873536017007755)
          ·
            refine ⟨9114099418310304025511633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6076066278873536017007755 9114099418310304025511633)
            ·
              refine ⟨6835574563732728019133725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9114099418310304025511633 6835574563732728019133725)
              ·
                refine ⟨2563340461399773007175147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6835574563732728019133725 2563340461399773007175147)
                ·
                  refine ⟨3845010692099659510762721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2563340461399773007175147 3845010692099659510762721)
                  ·
                    refine ⟨2883758019074744633072041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3845010692099659510762721 2883758019074744633072041)
                    ·
                      refine ⟨2162818514306058474804031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2883758019074744633072041 2162818514306058474804031)
                      ·
                        rfl

theorem cell23_4212074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_4212074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212074 prefixEnd_4212074 := by exact prefixLift 4212074
  have htrace : WordTrace (prefixWord ++ tailWord_4212074) baseStart_4212074 baseEnd_4212074 := by
    simpa [prefixWord, tailWord_4212074, baseEnd_4212074] using wordTrace_append hprefix tailTrace_4212074
  have hstable : (prefixWord ++ tailWord_4212074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212074).length < 2 ^ (prefixWord ++ tailWord_4212074).sum := by decide
  have hdescent : baseEnd_4212074 < baseStart_4212074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212089 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 2, 6]
def baseStart_4212089 : Nat := 118140960795 + 4212089 * 2 ^ 59
def prefixEnd_4212089 : Nat := 4983230072969 + 3 ^ 40 * 4212089 * 2
def baseEnd_4212089 : Nat := 720942072171958638705487

theorem tailTrace_4212089 : CollatzResearch.WordTrace tailWord_4212089 prefixEnd_4212089 720942072171958638705487 := by
  unfold tailWord_4212089
  simp only [CollatzResearch.WordTrace]
  refine ⟨153627506837328395374535321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102418337891552263583023547 153627506837328395374535321)
  ·
    refine ⟨115220630127996296530901491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153627506837328395374535321 115220630127996296530901491)
    ·
      refine ⟨172830945191994444796352237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115220630127996296530901491 172830945191994444796352237)
      ·
        refine ⟨64811604446997916798632089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172830945191994444796352237 64811604446997916798632089)
        ·
          refine ⟨48608703335248437598974067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64811604446997916798632089 48608703335248437598974067)
          ·
            refine ⟨72913055002872656398461101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48608703335248437598974067 72913055002872656398461101)
            ·
              refine ⟨27342395626077246149422913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72913055002872656398461101 27342395626077246149422913)
              ·
                refine ⟨20506796719557934612067185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27342395626077246149422913 20506796719557934612067185)
                ·
                  refine ⟨15380097539668450959050389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20506796719557934612067185 15380097539668450959050389)
                  ·
                    refine ⟨720942072171958638705487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15380097539668450959050389 720942072171958638705487)
                    ·
                      rfl

theorem cell23_4212089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 2, 6].length) (baseStart_4212089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212089 prefixEnd_4212089 := by exact prefixLift 4212089
  have htrace : WordTrace (prefixWord ++ tailWord_4212089) baseStart_4212089 baseEnd_4212089 := by
    simpa [prefixWord, tailWord_4212089, baseEnd_4212089] using wordTrace_append hprefix tailTrace_4212089
  have hstable : (prefixWord ++ tailWord_4212089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212089).length < 2 ^ (prefixWord ++ tailWord_4212089).sum := by decide
  have hdescent : baseEnd_4212089 < baseStart_4212089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212096 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 3, 4, 2]
def baseStart_4212096 : Nat := 118140960795 + 4212096 * 2 ^ 59
def prefixEnd_4212096 : Nat := 4983230072969 + 3 ^ 40 * 4212096 * 2
def baseEnd_4212096 : Nat := 2162829810880457388728929

theorem tailTrace_4212096 : CollatzResearch.WordTrace tailWord_4212096 prefixEnd_4212096 2162829810880457388728929 := by
  unfold tailWord_4212096
  simp only [CollatzResearch.WordTrace]
  refine ⟨76813881074151517785020071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102418508098868690380026761 76813881074151517785020071)
  ·
    refine ⟨115220821611227276677530107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76813881074151517785020071 115220821611227276677530107)
    ·
      refine ⟨172831232416840915016295161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115220821611227276677530107 172831232416840915016295161)
      ·
        refine ⟨129623424312630686262221371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172831232416840915016295161 129623424312630686262221371)
        ·
          refine ⟨194435136468946029393332057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129623424312630686262221371 194435136468946029393332057)
          ·
            refine ⟨145826352351709522044999043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194435136468946029393332057 145826352351709522044999043)
            ·
              refine ⟨218739528527564283067498565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145826352351709522044999043 218739528527564283067498565)
              ·
                refine ⟨41013661598918303075155981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 218739528527564283067498565 41013661598918303075155981)
                ·
                  refine ⟨15380123099594363653183493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41013661598918303075155981 15380123099594363653183493)
                  ·
                    refine ⟨2883773081173943184971905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15380123099594363653183493 2883773081173943184971905)
                    ·
                      refine ⟨2162829810880457388728929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2883773081173943184971905 2162829810880457388728929)
                      ·
                        rfl

theorem cell23_4212096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3, 4, 2].length) (baseStart_4212096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212096 prefixEnd_4212096 := by exact prefixLift 4212096
  have htrace : WordTrace (prefixWord ++ tailWord_4212096) baseStart_4212096 baseEnd_4212096 := by
    simpa [prefixWord, tailWord_4212096, baseEnd_4212096] using wordTrace_append hprefix tailTrace_4212096
  have hstable : (prefixWord ++ tailWord_4212096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212096).length < 2 ^ (prefixWord ++ tailWord_4212096).sum := by decide
  have hdescent : baseEnd_4212096 < baseStart_4212096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212130 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 4, 2, 2]
def baseStart_4212130 : Nat := 118140960795 + 4212130 * 2 ^ 59
def prefixEnd_4212130 : Nat := 4983230072969 + 3 ^ 40 * 4212130 * 2
def baseEnd_4212130 : Nat := 2162847269222710255703773

theorem tailTrace_4212130 : CollatzResearch.WordTrace tailWord_4212130 prefixEnd_4212130 2162847269222710255703773 := by
  unfold tailWord_4212130
  simp only [CollatzResearch.WordTrace]
  refine ⟨38407250557544964844194461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102419334820119906251185229 38407250557544964844194461)
  ·
    refine ⟨14402718959079361816572923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38407250557544964844194461 14402718959079361816572923)
    ·
      refine ⟨21604078438619042724859385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14402718959079361816572923 21604078438619042724859385)
      ·
        refine ⟨16203058828964282043644539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21604078438619042724859385 16203058828964282043644539)
        ·
          refine ⟨24304588243446423065466809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16203058828964282043644539 24304588243446423065466809)
          ·
            refine ⟨18228441182584817299100107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24304588243446423065466809 18228441182584817299100107)
            ·
              refine ⟨27342661773877225948650161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18228441182584817299100107 27342661773877225948650161)
              ·
                refine ⟨20506996330407919461487621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27342661773877225948650161 20506996330407919461487621)
                ·
                  refine ⟨3845061811951484899028929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20506996330407919461487621 3845061811951484899028929)
                  ·
                    refine ⟨2883796358963613674271697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3845061811951484899028929 2883796358963613674271697)
                    ·
                      refine ⟨2162847269222710255703773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2883796358963613674271697 2162847269222710255703773)
                      ·
                        rfl

theorem cell23_4212130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_4212130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212130 prefixEnd_4212130 := by exact prefixLift 4212130
  have htrace : WordTrace (prefixWord ++ tailWord_4212130) baseStart_4212130 baseEnd_4212130 := by
    simpa [prefixWord, tailWord_4212130, baseEnd_4212130] using wordTrace_append hprefix tailTrace_4212130
  have hstable : (prefixWord ++ tailWord_4212130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212130).length < 2 ^ (prefixWord ++ tailWord_4212130).sum := by decide
  have hdescent : baseEnd_4212130 < baseStart_4212130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212146 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3]
def baseStart_4212146 : Nat := 118140960795 + 4212146 * 2 ^ 59
def prefixEnd_4212146 : Nat := 4983230072969 + 3 ^ 40 * 4212146 * 2
def baseEnd_4212146 : Nat := 2162855484913182193103699

theorem tailTrace_4212146 : CollatzResearch.WordTrace tailWord_4212146 prefixEnd_4212146 2162855484913182193103699 := by
  unfold tailWord_4212146
  simp only [CollatzResearch.WordTrace]
  refine ⟨38407396449530473527340073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102419723865414596072906861 38407396449530473527340073)
  ·
    refine ⟨28805547337147855145505055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38407396449530473527340073 28805547337147855145505055)
    ·
      refine ⟨43208321005721782718257583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28805547337147855145505055 43208321005721782718257583)
      ·
        refine ⟨64812481508582674077386375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43208321005721782718257583 64812481508582674077386375)
        ·
          refine ⟨97218722262874011116079563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64812481508582674077386375 97218722262874011116079563)
          ·
            refine ⟨145828083394311016674119345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97218722262874011116079563 145828083394311016674119345)
            ·
              refine ⟨109371062545733262505589509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145828083394311016674119345 109371062545733262505589509)
              ·
                refine ⟨20507074227324986719798033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109371062545733262505589509 20507074227324986719798033)
                ·
                  refine ⟨15380305670493740039848525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20507074227324986719798033 15380305670493740039848525)
                  ·
                    refine ⟨5767614626435152514943197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15380305670493740039848525 5767614626435152514943197)
                    ·
                      refine ⟨2162855484913182193103699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5767614626435152514943197 2162855484913182193103699)
                      ·
                        rfl

theorem cell23_4212146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_4212146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212146 prefixEnd_4212146 := by exact prefixLift 4212146
  have htrace : WordTrace (prefixWord ++ tailWord_4212146) baseStart_4212146 baseEnd_4212146 := by
    simpa [prefixWord, tailWord_4212146, baseEnd_4212146] using wordTrace_append hprefix tailTrace_4212146
  have hstable : (prefixWord ++ tailWord_4212146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212146).length < 2 ^ (prefixWord ++ tailWord_4212146).sum := by decide
  have hdescent : baseEnd_4212146 < baseStart_4212146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212153 : List Nat := [1, 2, 1, 4, 4, 2, 1, 1, 7]
def baseStart_4212153 : Nat := 118140960795 + 4212153 * 2 ^ 59
def prefixEnd_4212153 : Nat := 4983230072969 + 3 ^ 40 * 4212153 * 2
def baseEnd_4212153 : Nat := 240317675475307073968463

theorem tailTrace_4212153 : CollatzResearch.WordTrace tailWord_4212153 prefixEnd_4212153 240317675475307073968463 := by
  unfold tailWord_4212153
  simp only [CollatzResearch.WordTrace]
  refine ⟨153629841109096534304865113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102419894072731022869910075 153629841109096534304865113)
  ·
    refine ⟨115222380831822400728648835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153629841109096534304865113 115222380831822400728648835)
    ·
      refine ⟨172833571247733601092973253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115222380831822400728648835 172833571247733601092973253)
      ·
        refine ⟨32406294608950050204932485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172833571247733601092973253 32406294608950050204932485)
        ·
          refine ⟨6076180239178134413424841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32406294608950050204932485 6076180239178134413424841)
          ·
            refine ⟨4557135179383600810068631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6076180239178134413424841 4557135179383600810068631)
            ·
              refine ⟨6835702769075401215102947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4557135179383600810068631 6835702769075401215102947)
              ·
                refine ⟨10253554153613101822654421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6835702769075401215102947 10253554153613101822654421)
                ·
                  refine ⟨240317675475307073968463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10253554153613101822654421 240317675475307073968463)
                  ·
                    rfl

theorem cell23_4212153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 7].length) (baseStart_4212153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212153 prefixEnd_4212153 := by exact prefixLift 4212153
  have htrace : WordTrace (prefixWord ++ tailWord_4212153) baseStart_4212153 baseEnd_4212153 := by
    simpa [prefixWord, tailWord_4212153, baseEnd_4212153] using wordTrace_append hprefix tailTrace_4212153
  have hstable : (prefixWord ++ tailWord_4212153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212153).length < 2 ^ (prefixWord ++ tailWord_4212153).sum := by decide
  have hdescent : baseEnd_4212153 < baseStart_4212153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212164 : List Nat := [2, 3, 3, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_4212164 : Nat := 118140960795 + 4212164 * 2 ^ 59
def prefixEnd_4212164 : Nat := 4983230072969 + 3 ^ 40 * 4212164 * 2
def baseEnd_4212164 : Nat := 2162864727564963122678617

theorem tailTrace_4212164 : CollatzResearch.WordTrace tailWord_4212164 prefixEnd_4212164 2162864727564963122678617 := by
  unfold tailWord_4212164
  simp only [CollatzResearch.WordTrace]
  refine ⟨76815121156028341591757773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102420161541371122122343697 76815121156028341591757773)
  ·
    refine ⟨28805670433510628096909165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76815121156028341591757773 28805670433510628096909165)
    ·
      refine ⟨10802126412566485536340937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28805670433510628096909165 10802126412566485536340937)
      ·
        refine ⟨8101594809424864152255703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10802126412566485536340937 8101594809424864152255703)
        ·
          refine ⟨12152392214137296228383555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8101594809424864152255703 12152392214137296228383555)
          ·
            refine ⟨18228588321205944342575333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12152392214137296228383555 18228588321205944342575333)
            ·
              refine ⟨3417860310226114564232875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18228588321205944342575333 3417860310226114564232875)
              ·
                refine ⟨5126790465339171846349313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3417860310226114564232875 5126790465339171846349313)
                ·
                  refine ⟨3845092849004378884761985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5126790465339171846349313 3845092849004378884761985)
                  ·
                    refine ⟨2883819636753284163571489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3845092849004378884761985 2883819636753284163571489)
                    ·
                      refine ⟨2162864727564963122678617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2883819636753284163571489 2162864727564963122678617)
                      ·
                        rfl

theorem cell23_4212164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_4212164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212164 prefixEnd_4212164 := by exact prefixLift 4212164
  have htrace : WordTrace (prefixWord ++ tailWord_4212164) baseStart_4212164 baseEnd_4212164 := by
    simpa [prefixWord, tailWord_4212164, baseEnd_4212164] using wordTrace_append hprefix tailTrace_4212164
  have hstable : (prefixWord ++ tailWord_4212164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212164).length < 2 ^ (prefixWord ++ tailWord_4212164).sum := by decide
  have hdescent : baseEnd_4212164 < baseStart_4212164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212206 : List Nat := [4, 1, 2, 1, 2, 1, 1, 1, 2, 3, 5]
def baseStart_4212206 : Nat := 118140960795 + 4212206 * 2 ^ 59
def prefixEnd_4212206 : Nat := 4983230072969 + 3 ^ 40 * 4212206 * 2
def baseEnd_4212206 : Nat := 2162886293752451958353423

theorem tailTrace_4212206 : CollatzResearch.WordTrace tailWord_4212206 prefixEnd_4212206 2162886293752451958353423 := by
  unfold tailWord_4212206
  simp only [CollatzResearch.WordTrace]
  refine ⟨19203971772238065544568059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102421182785269682904362981 19203971772238065544568059)
  ·
    refine ⟨28805957658357098316852089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19203971772238065544568059 28805957658357098316852089)
    ·
      refine ⟨21604468243767823737639067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28805957658357098316852089 21604468243767823737639067)
      ·
        refine ⟨32406702365651735606458601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21604468243767823737639067 32406702365651735606458601)
        ·
          refine ⟨24305026774238801704843951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32406702365651735606458601 24305026774238801704843951)
          ·
            refine ⟨36457540161358202557265927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24305026774238801704843951 36457540161358202557265927)
            ·
              refine ⟨54686310242037303835898891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36457540161358202557265927 54686310242037303835898891)
              ·
                refine ⟨82029465363055955753848337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54686310242037303835898891 82029465363055955753848337)
                ·
                  refine ⟨61522099022291966815386253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82029465363055955753848337 61522099022291966815386253)
                  ·
                    refine ⟨23070787133359487555769845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61522099022291966815386253 23070787133359487555769845)
                    ·
                      refine ⟨2162886293752451958353423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23070787133359487555769845 2162886293752451958353423)
                      ·
                        rfl

theorem cell23_4212206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_4212206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212206 prefixEnd_4212206 := by exact prefixLift 4212206
  have htrace : WordTrace (prefixWord ++ tailWord_4212206) baseStart_4212206 baseEnd_4212206 := by
    simpa [prefixWord, tailWord_4212206, baseEnd_4212206] using wordTrace_append hprefix tailTrace_4212206
  have hstable : (prefixWord ++ tailWord_4212206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212206).length < 2 ^ (prefixWord ++ tailWord_4212206).sum := by decide
  have hdescent : baseEnd_4212206 < baseStart_4212206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212237 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_4212237 : Nat := 118140960795 + 4212237 * 2 ^ 59
def prefixEnd_4212237 : Nat := 4983230072969 + 3 ^ 40 * 4212237 * 2
def baseEnd_4212237 : Nat := 2162902211652741337065781

theorem tailTrace_4212237 : CollatzResearch.WordTrace tailWord_4212237 prefixEnd_4212237 2162902211652741337065781 := by
  unfold tailWord_4212237
  simp only [CollatzResearch.WordTrace]
  refine ⟨153632904840792216650922965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102421936560528144433948643 153632904840792216650922965)
  ·
    refine ⟨3600771207206067577756007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 153632904840792216650922965 3600771207206067577756007)
    ·
      refine ⟨5401156810809101366634011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3600771207206067577756007 5401156810809101366634011)
      ·
        refine ⟨8101735216213652049951017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5401156810809101366634011 8101735216213652049951017)
        ·
          refine ⟨6076301412160239037463263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8101735216213652049951017 6076301412160239037463263)
          ·
            refine ⟨9114452118240358556194895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6076301412160239037463263 9114452118240358556194895)
            ·
              refine ⟨13671678177360537834292343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9114452118240358556194895 13671678177360537834292343)
              ·
                refine ⟨20507517266040806751438515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13671678177360537834292343 20507517266040806751438515)
                ·
                  refine ⟨30761275899061210127157773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20507517266040806751438515 30761275899061210127157773)
                  ·
                    refine ⟨11535478462147953797684165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30761275899061210127157773 11535478462147953797684165)
                    ·
                      refine ⟨2162902211652741337065781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11535478462147953797684165 2162902211652741337065781)
                      ·
                        rfl

theorem cell23_4212237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_4212237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212237 prefixEnd_4212237 := by exact prefixLift 4212237
  have htrace : WordTrace (prefixWord ++ tailWord_4212237) baseStart_4212237 baseEnd_4212237 := by
    simpa [prefixWord, tailWord_4212237, baseEnd_4212237] using wordTrace_append hprefix tailTrace_4212237
  have hstable : (prefixWord ++ tailWord_4212237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212237).length < 2 ^ (prefixWord ++ tailWord_4212237).sum := by decide
  have hdescent : baseEnd_4212237 < baseStart_4212237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212293 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 2, 6, 2]
def baseStart_4212293 : Nat := 118140960795 + 4212293 * 2 ^ 59
def prefixEnd_4212293 : Nat := 4983230072969 + 3 ^ 40 * 4212293 * 2
def baseEnd_4212293 : Nat := 2162930966569393117965523

theorem tailTrace_4212293 : CollatzResearch.WordTrace tailWord_4212293 prefixEnd_4212293 2162930966569393117965523 := by
  unfold tailWord_4212293
  simp only [CollatzResearch.WordTrace]
  refine ⟨153634947328589338214961533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102423298219059558809974355 153634947328589338214961533)
  ·
    refine ⟨57613105248221001830610575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153634947328589338214961533 57613105248221001830610575)
    ·
      refine ⟨86419657872331502745915863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57613105248221001830610575 86419657872331502745915863)
      ·
        refine ⟨129629486808497254118873795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86419657872331502745915863 129629486808497254118873795)
        ·
          refine ⟨194444230212745881178310693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129629486808497254118873795 194444230212745881178310693)
          ·
            refine ⟨36458293164889852720933255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 194444230212745881178310693 36458293164889852720933255)
            ·
              refine ⟨54687439747334779081399883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36458293164889852720933255 54687439747334779081399883)
              ·
                refine ⟨82031159621002168622099825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54687439747334779081399883 82031159621002168622099825)
                ·
                  refine ⟨61523369715751626466574869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82031159621002168622099825 61523369715751626466574869)
                  ·
                    refine ⟨2883907955425857490620697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61523369715751626466574869 2883907955425857490620697)
                    ·
                      refine ⟨2162930966569393117965523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2883907955425857490620697 2162930966569393117965523)
                      ·
                        rfl

theorem cell23_4212293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 6, 2].length) (baseStart_4212293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212293 prefixEnd_4212293 := by exact prefixLift 4212293
  have htrace : WordTrace (prefixWord ++ tailWord_4212293) baseStart_4212293 baseEnd_4212293 := by
    simpa [prefixWord, tailWord_4212293, baseEnd_4212293] using wordTrace_append hprefix tailTrace_4212293
  have hstable : (prefixWord ++ tailWord_4212293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212293).length < 2 ^ (prefixWord ++ tailWord_4212293).sum := by decide
  have hdescent : baseEnd_4212293 < baseStart_4212293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212327 : List Nat := [1, 1, 5, 1, 1, 1, 5, 1, 3, 2, 2]
def baseStart_4212327 : Nat := 118140960795 + 4212327 * 2 ^ 59
def prefixEnd_4212327 : Nat := 4983230072969 + 3 ^ 40 * 4212327 * 2
def baseEnd_4212327 : Nat := 2162948424911645984940367

theorem tailTrace_4212327 : CollatzResearch.WordTrace tailWord_4212327 prefixEnd_4212327 2162948424911645984940367 := by
  unfold tailWord_4212327
  simp only [CollatzResearch.WordTrace]
  refine ⟨153636187410466162021699235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102424124940310774681132823 153636187410466162021699235)
  ·
    refine ⟨230454281115699243032548853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153636187410466162021699235 230454281115699243032548853)
    ·
      refine ⟨21605088854596804034301455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 230454281115699243032548853 21605088854596804034301455)
      ·
        refine ⟨32407633281895206051452183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21605088854596804034301455 32407633281895206051452183)
        ·
          refine ⟨48611449922842809077178275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32407633281895206051452183 48611449922842809077178275)
          ·
            refine ⟨72917174884264213615767413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48611449922842809077178275 72917174884264213615767413)
            ·
              refine ⟨6835985145399770026478195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72917174884264213615767413 6835985145399770026478195)
              ·
                refine ⟨10253977718099655039717293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6835985145399770026478195 10253977718099655039717293)
                ·
                  refine ⟨3845241644287370639893985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10253977718099655039717293 3845241644287370639893985)
                  ·
                    refine ⟨2883931233215527979920489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3845241644287370639893985 2883931233215527979920489)
                    ·
                      refine ⟨2162948424911645984940367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2883931233215527979920489 2162948424911645984940367)
                      ·
                        rfl

theorem cell23_4212327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_4212327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212327 prefixEnd_4212327 := by exact prefixLift 4212327
  have htrace : WordTrace (prefixWord ++ tailWord_4212327) baseStart_4212327 baseEnd_4212327 := by
    simpa [prefixWord, tailWord_4212327, baseEnd_4212327] using wordTrace_append hprefix tailTrace_4212327
  have hstable : (prefixWord ++ tailWord_4212327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212327).length < 2 ^ (prefixWord ++ tailWord_4212327).sum := by decide
  have hdescent : baseEnd_4212327 < baseStart_4212327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212343 : List Nat := [1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 3]
def baseStart_4212343 : Nat := 118140960795 + 4212343 * 2 ^ 59
def prefixEnd_4212343 : Nat := 4983230072969 + 3 ^ 40 * 4212343 * 2
def baseEnd_4212343 : Nat := 2162956640602117922340293

theorem tailTrace_4212343 : CollatzResearch.WordTrace tailWord_4212343 prefixEnd_4212343 2162956640602117922340293 := by
  unfold tailWord_4212343
  simp only [CollatzResearch.WordTrace]
  refine ⟨153636770978408196754281683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102424513985605464502854455 153636770978408196754281683)
  ·
    refine ⟨230455156467612295131422525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153636770978408196754281683 230455156467612295131422525)
    ·
      refine ⟨86420683675354610674283447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230455156467612295131422525 86420683675354610674283447)
      ·
        refine ⟨129631025513031916011425171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86420683675354610674283447 129631025513031916011425171)
        ·
          refine ⟨194446538269547874017137757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129631025513031916011425171 194446538269547874017137757)
          ·
            refine ⟨72917451851080452756426659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 194446538269547874017137757 72917451851080452756426659)
            ·
              refine ⟨109376177776620679134639989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72917451851080452756426659 109376177776620679134639989)
              ·
                refine ⟨10254016666558188668872499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109376177776620679134639989 10254016666558188668872499)
                ·
                  refine ⟨15381024999837283003308749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10254016666558188668872499 15381024999837283003308749)
                  ·
                    refine ⟨5767884374938981126240781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15381024999837283003308749 5767884374938981126240781)
                    ·
                      refine ⟨2162956640602117922340293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5767884374938981126240781 2162956640602117922340293)
                      ·
                        rfl

theorem cell23_4212343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_4212343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212343 prefixEnd_4212343 := by exact prefixLift 4212343
  have htrace : WordTrace (prefixWord ++ tailWord_4212343) baseStart_4212343 baseEnd_4212343 := by
    simpa [prefixWord, tailWord_4212343, baseEnd_4212343] using wordTrace_append hprefix tailTrace_4212343
  have hstable : (prefixWord ++ tailWord_4212343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212343).length < 2 ^ (prefixWord ++ tailWord_4212343).sum := by decide
  have hdescent : baseEnd_4212343 < baseStart_4212343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212346 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 4, 7]
def baseStart_4212346 : Nat := 118140960795 + 4212346 * 2 ^ 59
def prefixEnd_4212346 : Nat := 4983230072969 + 3 ^ 40 * 4212346 * 2
def baseEnd_4212346 : Nat := 720986060348027136867593

theorem tailTrace_4212346 : CollatzResearch.WordTrace tailWord_4212346 prefixEnd_4212346 720986060348027136867593 := by
  unfold tailWord_4212346
  simp only [CollatzResearch.WordTrace]
  refine ⟨38409220099349332066660223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102424586931598218844427261 38409220099349332066660223)
  ·
    refine ⟨57613830149023998099990335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38409220099349332066660223 57613830149023998099990335)
    ·
      refine ⟨86420745223535997149985503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57613830149023998099990335 86420745223535997149985503)
      ·
        refine ⟨129631117835303995724978255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86420745223535997149985503 129631117835303995724978255)
        ·
          refine ⟨194446676752955993587467383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129631117835303995724978255 194446676752955993587467383)
          ·
            refine ⟨291670015129433990381201075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194446676752955993587467383 291670015129433990381201075)
            ·
              refine ⟨437505022694150985571801613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291670015129433990381201075 437505022694150985571801613)
              ·
                refine ⟨164064383510306619589425605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 437505022694150985571801613 164064383510306619589425605)
                ·
                  refine ⟨30762071908182491173017301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164064383510306619589425605 30762071908182491173017301)
                  ·
                    refine ⟨720986060348027136867593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30762071908182491173017301 720986060348027136867593)
                    ·
                      rfl

theorem cell23_4212346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_4212346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212346 prefixEnd_4212346 := by exact prefixLift 4212346
  have htrace : WordTrace (prefixWord ++ tailWord_4212346) baseStart_4212346 baseEnd_4212346 := by
    simpa [prefixWord, tailWord_4212346, baseEnd_4212346] using wordTrace_append hprefix tailTrace_4212346
  have hstable : (prefixWord ++ tailWord_4212346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212346).length < 2 ^ (prefixWord ++ tailWord_4212346).sum := by decide
  have hdescent : baseEnd_4212346 < baseStart_4212346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212400 : List Nat := [2, 1, 1, 1, 2, 1, 5, 3, 1, 4, 2]
def baseStart_4212400 : Nat := 118140960795 + 4212400 * 2 ^ 59
def prefixEnd_4212400 : Nat := 4983230072969 + 3 ^ 40 * 4212400 * 2
def baseEnd_4212400 : Nat := 2162985908999424199327531

theorem tailTrace_4212400 : CollatzResearch.WordTrace tailWord_4212400 prefixEnd_4212400 2162985908999424199327531 := by
  unfold tailWord_4212400
  simp only [CollatzResearch.WordTrace]
  refine ⟨76819424969600847744553327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102425899959467796992737769 76819424969600847744553327)
  ·
    refine ⟨115229137454401271616829991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76819424969600847744553327 115229137454401271616829991)
    ·
      refine ⟨172843706181601907425244987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115229137454401271616829991 172843706181601907425244987)
      ·
        refine ⟨259265559272402861137867481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172843706181601907425244987 259265559272402861137867481)
        ·
          refine ⟨194449169454302145853400611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259265559272402861137867481 194449169454302145853400611)
          ·
            refine ⟨291673754181453218780100917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194449169454302145853400611 291673754181453218780100917)
            ·
              refine ⟨27344414454511239260634461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 291673754181453218780100917 27344414454511239260634461)
              ·
                refine ⟨10254155420441714722737923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27344414454511239260634461 10254155420441714722737923)
                ·
                  refine ⟨15381233130662572084106885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10254155420441714722737923 15381233130662572084106885)
                  ·
                    refine ⟨2883981211999232265770041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15381233130662572084106885 2883981211999232265770041)
                    ·
                      refine ⟨2162985908999424199327531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2883981211999232265770041 2162985908999424199327531)
                      ·
                        rfl

theorem cell23_4212400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 1, 4, 2].length) (baseStart_4212400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212400 prefixEnd_4212400 := by exact prefixLift 4212400
  have htrace : WordTrace (prefixWord ++ tailWord_4212400) baseStart_4212400 baseEnd_4212400 := by
    simpa [prefixWord, tailWord_4212400, baseEnd_4212400] using wordTrace_append hprefix tailTrace_4212400
  have hstable : (prefixWord ++ tailWord_4212400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212400).length < 2 ^ (prefixWord ++ tailWord_4212400).sum := by decide
  have hdescent : baseEnd_4212400 < baseStart_4212400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212403 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 3]
def baseStart_4212403 : Nat := 118140960795 + 4212403 * 2 ^ 59
def prefixEnd_4212403 : Nat := 4983230072969 + 3 ^ 40 * 4212403 * 2
def baseEnd_4212403 : Nat := 2162987449441387687590017

theorem tailTrace_4212403 : CollatzResearch.WordTrace tailWord_4212403 prefixEnd_4212403 2162987449441387687590017 := by
  unfold tailWord_4212403
  simp only [CollatzResearch.WordTrace]
  refine ⟨153638959358190827001465863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102425972905460551334310575 153638959358190827001465863)
  ·
    refine ⟨230458439037286240502198795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153638959358190827001465863 230458439037286240502198795)
    ·
      refine ⟨345687658555929360753298193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230458439037286240502198795 345687658555929360753298193)
      ·
        refine ⟨259265743916947020564973645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345687658555929360753298193 259265743916947020564973645)
        ·
          refine ⟨97224653968855132711865117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259265743916947020564973645 97224653968855132711865117)
          ·
            refine ⟨36459245238320674766949419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97224653968855132711865117 36459245238320674766949419)
            ·
              refine ⟨54688867857481012150424129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36459245238320674766949419 54688867857481012150424129)
              ·
                refine ⟨41016650893110759112818097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54688867857481012150424129 41016650893110759112818097)
                ·
                  refine ⟨30762488169833069334613573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41016650893110759112818097 30762488169833069334613573)
                  ·
                    refine ⟨5767966531843700500240045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30762488169833069334613573 5767966531843700500240045)
                    ·
                      refine ⟨2162987449441387687590017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5767966531843700500240045 2162987449441387687590017)
                      ·
                        rfl

theorem cell23_4212403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 3].length) (baseStart_4212403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212403 prefixEnd_4212403 := by exact prefixLift 4212403
  have htrace : WordTrace (prefixWord ++ tailWord_4212403) baseStart_4212403 baseEnd_4212403 := by
    simpa [prefixWord, tailWord_4212403, baseEnd_4212403] using wordTrace_append hprefix tailTrace_4212403
  have hstable : (prefixWord ++ tailWord_4212403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212403).length < 2 ^ (prefixWord ++ tailWord_4212403).sum := by decide
  have hdescent : baseEnd_4212403 < baseStart_4212403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212413 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 1, 4, 4]
def baseStart_4212413 : Nat := 118140960795 + 4212413 * 2 ^ 59
def prefixEnd_4212413 : Nat := 4983230072969 + 3 ^ 40 * 4212413 * 2
def baseEnd_4212413 : Nat := 2162992584247932648464971

theorem tailTrace_4212413 : CollatzResearch.WordTrace tailWord_4212413 prefixEnd_4212413 2162992584247932648464971 := by
  unfold tailWord_4212413
  simp only [CollatzResearch.WordTrace]
  refine ⟨153639324088154598709329893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102426216058769732472886595 153639324088154598709329893)
  ·
    refine ⟨28807373266528987257999355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153639324088154598709329893 28807373266528987257999355)
    ·
      refine ⟨43211059899793480886999033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28807373266528987257999355 43211059899793480886999033)
      ·
        refine ⟨32408294924845110665249275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43211059899793480886999033 32408294924845110665249275)
        ·
          refine ⟨48612442387267665997873913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32408294924845110665249275 48612442387267665997873913)
          ·
            refine ⟨36459331790450749498405435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48612442387267665997873913 36459331790450749498405435)
            ·
              refine ⟨54688997685676124247608153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36459331790450749498405435 54688997685676124247608153)
              ·
                refine ⟨41016748264257093185706115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54688997685676124247608153 41016748264257093185706115)
                ·
                  refine ⟨61525122396385639778559173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41016748264257093185706115 61525122396385639778559173)
                  ·
                    refine ⟨11535960449322307458479845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61525122396385639778559173 11535960449322307458479845)
                    ·
                      refine ⟨2162992584247932648464971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11535960449322307458479845 2162992584247932648464971)
                      ·
                        rfl

theorem cell23_4212413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_4212413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212413 prefixEnd_4212413 := by exact prefixLift 4212413
  have htrace : WordTrace (prefixWord ++ tailWord_4212413) baseStart_4212413 baseEnd_4212413 := by
    simpa [prefixWord, tailWord_4212413, baseEnd_4212413] using wordTrace_append hprefix tailTrace_4212413
  have hstable : (prefixWord ++ tailWord_4212413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212413).length < 2 ^ (prefixWord ++ tailWord_4212413).sum := by decide
  have hdescent : baseEnd_4212413 < baseStart_4212413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212434 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 4, 2, 2]
def baseStart_4212434 : Nat := 118140960795 + 4212434 * 2 ^ 59
def prefixEnd_4212434 : Nat := 4983230072969 + 3 ^ 40 * 4212434 * 2
def baseEnd_4212434 : Nat := 2163003367341677066302375

theorem tailTrace_4212434 : CollatzResearch.WordTrace tailWord_4212434 prefixEnd_4212434 2163003367341677066302375 := by
  unfold tailWord_4212434
  simp only [CollatzResearch.WordTrace]
  refine ⟨38410022505269629823961089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102426726680719012863896237 38410022505269629823961089)
  ·
    refine ⟨28807516878952222367970817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38410022505269629823961089 28807516878952222367970817)
    ·
      refine ⟨21605637659214166775978113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28807516878952222367970817 21605637659214166775978113)
      ·
        refine ⟨16204228244410625081983585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21605637659214166775978113 16204228244410625081983585)
        ·
          refine ⟨12153171183307968811487689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16204228244410625081983585 12153171183307968811487689)
          ·
            refine ⟨9114878387480976608615767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12153171183307968811487689 9114878387480976608615767)
            ·
              refine ⟨13672317581221464912923651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9114878387480976608615767 13672317581221464912923651)
              ·
                refine ⟨20508476371832197369385477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13672317581221464912923651 20508476371832197369385477)
                ·
                  refine ⟨3845339319718537006759777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20508476371832197369385477 3845339319718537006759777)
                  ·
                    refine ⟨2884004489788902755069833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3845339319718537006759777 2884004489788902755069833)
                    ·
                      refine ⟨2163003367341677066302375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2884004489788902755069833 2163003367341677066302375)
                      ·
                        rfl

theorem cell23_4212434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_4212434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212434 prefixEnd_4212434 := by exact prefixLift 4212434
  have htrace : WordTrace (prefixWord ++ tailWord_4212434) baseStart_4212434 baseEnd_4212434 := by
    simpa [prefixWord, tailWord_4212434, baseEnd_4212434] using wordTrace_append hprefix tailTrace_4212434
  have hstable : (prefixWord ++ tailWord_4212434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212434).length < 2 ^ (prefixWord ++ tailWord_4212434).sum := by decide
  have hdescent : baseEnd_4212434 < baseStart_4212434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212440 : List Nat := [2, 1, 2, 2, 3, 1, 1, 6, 5]
def baseStart_4212440 : Nat := 118140960795 + 4212440 * 2 ^ 59
def prefixEnd_4212440 : Nat := 4983230072969 + 3 ^ 40 * 4212440 * 2
def baseEnd_4212440 : Nat := 240334049802844893647483

theorem tailTrace_4212440 : CollatzResearch.WordTrace tailWord_4212440 prefixEnd_4212440 240334049802844893647483 := by
  unfold tailWord_4212440
  simp only [CollatzResearch.WordTrace]
  refine ⟨76820154429528391160281387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102426872572704521547041849 76820154429528391160281387)
  ·
    refine ⟨115230231644292586740422081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76820154429528391160281387 115230231644292586740422081)
    ·
      refine ⟨86422673733219440055316561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115230231644292586740422081 86422673733219440055316561)
      ·
        refine ⟨64817005299914580041487421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86422673733219440055316561 64817005299914580041487421)
        ·
          refine ⟨24306376987467967515557783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64817005299914580041487421 24306376987467967515557783)
          ·
            refine ⟨36459565481201951273336675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24306376987467967515557783 36459565481201951273336675)
            ·
              refine ⟨54689348221802926910005013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36459565481201951273336675 54689348221802926910005013)
              ·
                refine ⟨2563563197897012198906485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54689348221802926910005013 2563563197897012198906485)
                ·
                  refine ⟨240334049802844893647483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2563563197897012198906485 240334049802844893647483)
                  ·
                    rfl

theorem cell23_4212440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 5].length) (baseStart_4212440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212440 prefixEnd_4212440 := by exact prefixLift 4212440
  have htrace : WordTrace (prefixWord ++ tailWord_4212440) baseStart_4212440 baseEnd_4212440 := by
    simpa [prefixWord, tailWord_4212440, baseEnd_4212440] using wordTrace_append hprefix tailTrace_4212440
  have hstable : (prefixWord ++ tailWord_4212440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212440).length < 2 ^ (prefixWord ++ tailWord_4212440).sum := by decide
  have hdescent : baseEnd_4212440 < baseStart_4212440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212451 : List Nat := [1, 1, 1, 7, 3, 1, 1, 1, 1, 4, 2]
def baseStart_4212451 : Nat := 118140960795 + 4212451 * 2 ^ 59
def prefixEnd_4212451 : Nat := 4983230072969 + 3 ^ 40 * 4212451 * 2
def baseEnd_4212451 : Nat := 2163012096512803499789797

theorem tailTrace_4212451 : CollatzResearch.WordTrace tailWord_4212451 prefixEnd_4212451 2163012096512803499789797 := by
  unfold tailWord_4212451
  simp only [CollatzResearch.WordTrace]
  refine ⟨153640710062016931199213207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102427140041344620799475471 153640710062016931199213207)
  ·
    refine ⟨230461065093025396798819811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153640710062016931199213207 230461065093025396798819811)
    ·
      refine ⟨345691597639538095198229717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230461065093025396798819811 345691597639538095198229717)
      ·
        refine ⟨8102146819676674106208509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 345691597639538095198229717 8102146819676674106208509)
        ·
          refine ⟨3038305057378752789828191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8102146819676674106208509 3038305057378752789828191)
          ·
            refine ⟨4557457586068129184742287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3038305057378752789828191 4557457586068129184742287)
            ·
              refine ⟨6836186379102193777113431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4557457586068129184742287 6836186379102193777113431)
              ·
                refine ⟨10254279568653290665670147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6836186379102193777113431 10254279568653290665670147)
                ·
                  refine ⟨15381419352979935998505221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10254279568653290665670147 15381419352979935998505221)
                  ·
                    refine ⟨2884016128683737999719729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15381419352979935998505221 2884016128683737999719729)
                    ·
                      refine ⟨2163012096512803499789797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2884016128683737999719729 2163012096512803499789797)
                      ·
                        rfl

theorem cell23_4212451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_4212451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212451 prefixEnd_4212451 := by exact prefixLift 4212451
  have htrace : WordTrace (prefixWord ++ tailWord_4212451) baseStart_4212451 baseEnd_4212451 := by
    simpa [prefixWord, tailWord_4212451, baseEnd_4212451] using wordTrace_append hprefix tailTrace_4212451
  have hstable : (prefixWord ++ tailWord_4212451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212451).length < 2 ^ (prefixWord ++ tailWord_4212451).sum := by decide
  have hdescent : baseEnd_4212451 < baseStart_4212451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212453 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 3, 7]
def baseStart_4212453 : Nat := 118140960795 + 4212453 * 2 ^ 59
def prefixEnd_4212453 : Nat := 4983230072969 + 3 ^ 40 * 4212453 * 2
def baseEnd_4212453 : Nat := 721004374491370830654929

theorem tailTrace_4212453 : CollatzResearch.WordTrace tailWord_4212453 prefixEnd_4212453 721004374491370830654929 := by
  unfold tailWord_4212453
  simp only [CollatzResearch.WordTrace]
  refine ⟨153640783008009685540786013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102427188672006457027190675 153640783008009685540786013)
  ·
    refine ⟨57615293628003632077794755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153640783008009685540786013 57615293628003632077794755)
    ·
      refine ⟨86422940442005448116692133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57615293628003632077794755 86422940442005448116692133)
      ·
        refine ⟨16204301332876021521879775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86422940442005448116692133 16204301332876021521879775)
        ·
          refine ⟨24306451999314032282819663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16204301332876021521879775 24306451999314032282819663)
          ·
            refine ⟨36459677998971048424229495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24306451999314032282819663 36459677998971048424229495)
            ·
              refine ⟨54689516998456572636344243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36459677998971048424229495 54689516998456572636344243)
              ·
                refine ⟨82034275497684858954516365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54689516998456572636344243 82034275497684858954516365)
                ·
                  refine ⟨30762853311631822107943637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82034275497684858954516365 30762853311631822107943637)
                  ·
                    refine ⟨721004374491370830654929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30762853311631822107943637 721004374491370830654929)
                    ·
                      rfl

theorem cell23_4212453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_4212453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212453 prefixEnd_4212453 := by exact prefixLift 4212453
  have htrace : WordTrace (prefixWord ++ tailWord_4212453) baseStart_4212453 baseEnd_4212453 := by
    simpa [prefixWord, tailWord_4212453, baseEnd_4212453] using wordTrace_append hprefix tailTrace_4212453
  have hstable : (prefixWord ++ tailWord_4212453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212453).length < 2 ^ (prefixWord ++ tailWord_4212453).sum := by decide
  have hdescent : baseEnd_4212453 < baseStart_4212453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212460 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 2, 5, 2]
def baseStart_4212460 : Nat := 118140960795 + 4212460 * 2 ^ 59
def prefixEnd_4212460 : Nat := 4983230072969 + 3 ^ 40 * 4212460 * 2
def baseEnd_4212460 : Nat := 2163016717838693964577255

theorem tailTrace_4212460 : CollatzResearch.WordTrace tailWord_4212460 prefixEnd_4212460 2163016717838693964577255 := by
  unfold tailWord_4212460
  simp only [CollatzResearch.WordTrace]
  refine ⟨76820519159492162868145417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102427358879322883824193889 76820519159492162868145417)
  ·
    refine ⟨57615389369619122151109063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76820519159492162868145417 57615389369619122151109063)
    ·
      refine ⟨86423084054428683226663595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57615389369619122151109063 86423084054428683226663595)
      ·
        refine ⟨129634626081643024839995393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86423084054428683226663595 129634626081643024839995393)
        ·
          refine ⟨97225969561232268629996545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129634626081643024839995393 97225969561232268629996545)
          ·
            refine ⟨72919477170924201472497409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97225969561232268629996545 72919477170924201472497409)
            ·
              refine ⟨54689607878193151104373057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72919477170924201472497409 54689607878193151104373057)
              ·
                refine ⟨41017205908644863328279793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54689607878193151104373057 41017205908644863328279793)
                ·
                  refine ⟨30762904431483647496209845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41017205908644863328279793 30762904431483647496209845)
                  ·
                    refine ⟨2884022290451591952769673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30762904431483647496209845 2884022290451591952769673)
                    ·
                      refine ⟨2163016717838693964577255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2884022290451591952769673 2163016717838693964577255)
                      ·
                        rfl

theorem cell23_4212460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 5, 2].length) (baseStart_4212460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212460 prefixEnd_4212460 := by exact prefixLift 4212460
  have htrace : WordTrace (prefixWord ++ tailWord_4212460) baseStart_4212460 baseEnd_4212460 := by
    simpa [prefixWord, tailWord_4212460, baseEnd_4212460] using wordTrace_append hprefix tailTrace_4212460
  have hstable : (prefixWord ++ tailWord_4212460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212460).length < 2 ^ (prefixWord ++ tailWord_4212460).sum := by decide
  have hdescent : baseEnd_4212460 < baseStart_4212460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212470 : List Nat := [5, 1, 1, 1, 1, 3, 2, 1, 1, 7]
def baseStart_4212470 : Nat := 118140960795 + 4212470 * 2 ^ 59
def prefixEnd_4212470 : Nat := 4983230072969 + 3 ^ 40 * 4212470 * 2
def baseEnd_4212470 : Nat := 721007284215079641817403

theorem tailTrace_4212470 : CollatzResearch.WordTrace tailWord_4212470 prefixEnd_4212470 721007284215079641817403 := by
  unfold tailWord_4212470
  simp only [CollatzResearch.WordTrace]
  refine ⟨9602587690559256090259679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102427602032632064962769909 9602587690559256090259679)
  ·
    refine ⟨14403881535838884135389519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9602587690559256090259679 14403881535838884135389519)
    ·
      refine ⟨21605822303758326203084279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14403881535838884135389519 21605822303758326203084279)
      ·
        refine ⟨32408733455637489304626419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21605822303758326203084279 32408733455637489304626419)
        ·
          refine ⟨48613100183456233956939629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32408733455637489304626419 48613100183456233956939629)
          ·
            refine ⟨18229912568796087733852361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48613100183456233956939629 18229912568796087733852361)
            ·
              refine ⟨13672434426597065800389271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18229912568796087733852361 13672434426597065800389271)
              ·
                refine ⟨20508651639895598700583907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13672434426597065800389271 20508651639895598700583907)
                ·
                  refine ⟨30762977459843398050875861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20508651639895598700583907 30762977459843398050875861)
                  ·
                    refine ⟨721007284215079641817403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30762977459843398050875861 721007284215079641817403)
                    ·
                      rfl

theorem cell23_4212470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_4212470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212470 prefixEnd_4212470 := by exact prefixLift 4212470
  have htrace : WordTrace (prefixWord ++ tailWord_4212470) baseStart_4212470 baseEnd_4212470 := by
    simpa [prefixWord, tailWord_4212470, baseEnd_4212470] using wordTrace_append hprefix tailTrace_4212470
  have hstable : (prefixWord ++ tailWord_4212470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212470).length < 2 ^ (prefixWord ++ tailWord_4212470).sum := by decide
  have hdescent : baseEnd_4212470 < baseStart_4212470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212487 : List Nat := [1, 1, 4, 4, 2, 1, 1, 2, 2, 5]
def baseStart_4212487 : Nat := 118140960795 + 4212487 * 2 ^ 59
def prefixEnd_4212487 : Nat := 4983230072969 + 3 ^ 40 * 4212487 * 2
def baseEnd_4212487 : Nat := 721010193938788452979877

theorem tailTrace_4212487 : CollatzResearch.WordTrace tailWord_4212487 prefixEnd_4212487 721010193938788452979877 := by
  unfold tailWord_4212487
  simp only [CollatzResearch.WordTrace]
  refine ⟨153642023089886509347523715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102428015393257672898349143 153642023089886509347523715)
  ·
    refine ⟨230463034634829764021285573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153642023089886509347523715 230463034634829764021285573)
    ·
      refine ⟨43211818994030580753991045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230463034634829764021285573 43211818994030580753991045)
      ·
        refine ⟨8102216061380733891373321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43211818994030580753991045 8102216061380733891373321)
        ·
          refine ⟨6076662046035550418529991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8102216061380733891373321 6076662046035550418529991)
          ·
            refine ⟨9114993069053325627794987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6076662046035550418529991 9114993069053325627794987)
            ·
              refine ⟨13672489603579988441692481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9114993069053325627794987 13672489603579988441692481)
              ·
                refine ⟨10254367202684991331269361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13672489603579988441692481 10254367202684991331269361)
                ·
                  refine ⟨7690775402013743498452021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10254367202684991331269361 7690775402013743498452021)
                  ·
                    refine ⟨721010193938788452979877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7690775402013743498452021 721010193938788452979877)
                    ·
                      rfl

theorem cell23_4212487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_4212487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212487 prefixEnd_4212487 := by exact prefixLift 4212487
  have htrace : WordTrace (prefixWord ++ tailWord_4212487) baseStart_4212487 baseEnd_4212487 := by
    simpa [prefixWord, tailWord_4212487, baseEnd_4212487] using wordTrace_append hprefix tailTrace_4212487
  have hstable : (prefixWord ++ tailWord_4212487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212487).length < 2 ^ (prefixWord ++ tailWord_4212487).sum := by decide
  have hdescent : baseEnd_4212487 < baseStart_4212487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212490 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 4, 1, 4]
def baseStart_4212490 : Nat := 118140960795 + 4212490 * 2 ^ 59
def prefixEnd_4212490 : Nat := 4983230072969 + 3 ^ 40 * 4212490 * 2
def baseEnd_4212490 : Nat := 2163032122258328847202117

theorem tailTrace_4212490 : CollatzResearch.WordTrace tailWord_4212490 prefixEnd_4212490 2163032122258328847202117 := by
  unfold tailWord_4212490
  simp only [CollatzResearch.WordTrace]
  refine ⟨38410533127218910214970731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102428088339250427239921949 38410533127218910214970731)
  ·
    refine ⟨57615799690828365322456097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38410533127218910214970731 57615799690828365322456097)
    ·
      refine ⟨43211849768121273991842073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57615799690828365322456097 43211849768121273991842073)
      ·
        refine ⟨32408887326090955493881555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43211849768121273991842073 32408887326090955493881555)
        ·
          refine ⟨48613330989136433240822333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32408887326090955493881555 48613330989136433240822333)
          ·
            refine ⟨18229999120926162465308375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48613330989136433240822333 18229999120926162465308375)
            ·
              refine ⟨27344998681389243697962563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18229999120926162465308375 27344998681389243697962563)
              ·
                refine ⟨41017498022083865546943845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27344998681389243697962563 41017498022083865546943845)
                ·
                  refine ⟨7690780879140724790051971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41017498022083865546943845 7690780879140724790051971)
                  ·
                    refine ⟨11536171318711087185077957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7690780879140724790051971 11536171318711087185077957)
                    ·
                      refine ⟨2163032122258328847202117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11536171318711087185077957 2163032122258328847202117)
                      ·
                        rfl

theorem cell23_4212490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_4212490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212490 prefixEnd_4212490 := by exact prefixLift 4212490
  have htrace : WordTrace (prefixWord ++ tailWord_4212490) baseStart_4212490 baseEnd_4212490 := by
    simpa [prefixWord, tailWord_4212490, baseEnd_4212490] using wordTrace_append hprefix tailTrace_4212490
  have hstable : (prefixWord ++ tailWord_4212490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212490).length < 2 ^ (prefixWord ++ tailWord_4212490).sum := by decide
  have hdescent : baseEnd_4212490 < baseStart_4212490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212634 : List Nat := [3, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3]
def baseStart_4212634 : Nat := 118140960795 + 4212634 * 2 ^ 59
def prefixEnd_4212634 : Nat := 4983230072969 + 3 ^ 40 * 4212634 * 2
def baseEnd_4212634 : Nat := 2163106063472576283801455

theorem tailTrace_4212634 : CollatzResearch.WordTrace tailWord_4212634 prefixEnd_4212634 2163106063472576283801455 := by
  unfold tailWord_4212634
  simp only [CollatzResearch.WordTrace]
  refine ⟨38411846155088488363281239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102431589746902635635416637 38411846155088488363281239)
  ·
    refine ⟨57617769232632732544921859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38411846155088488363281239 57617769232632732544921859)
    ·
      refine ⟨86426653848949098817382789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57617769232632732544921859 86426653848949098817382789)
      ·
        refine ⟨16204997596677956028259273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86426653848949098817382789 16204997596677956028259273)
        ·
          refine ⟨12153748197508467021194455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16204997596677956028259273 12153748197508467021194455)
          ·
            refine ⟨18230622296262700531791683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12153748197508467021194455 18230622296262700531791683)
            ·
              refine ⟨27345933444394050797687525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18230622296262700531791683 27345933444394050797687525)
              ·
                refine ⟨5127362520823884524566411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27345933444394050797687525 5127362520823884524566411)
                ·
                  refine ⟨7691043781235826786849617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5127362520823884524566411 7691043781235826786849617)
                  ·
                    refine ⟨5768282835926870090137213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7691043781235826786849617 5768282835926870090137213)
                    ·
                      refine ⟨2163106063472576283801455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5768282835926870090137213 2163106063472576283801455)
                      ·
                        rfl

theorem cell23_4212634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_4212634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212634 prefixEnd_4212634 := by exact prefixLift 4212634
  have htrace : WordTrace (prefixWord ++ tailWord_4212634) baseStart_4212634 baseEnd_4212634 := by
    simpa [prefixWord, tailWord_4212634, baseEnd_4212634] using wordTrace_append hprefix tailTrace_4212634
  have hstable : (prefixWord ++ tailWord_4212634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212634).length < 2 ^ (prefixWord ++ tailWord_4212634).sum := by decide
  have hdescent : baseEnd_4212634 < baseStart_4212634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212637 : List Nat := [1, 4, 2, 1, 2, 2, 4, 7]
def baseStart_4212637 : Nat := 118140960795 + 4212637 * 2 ^ 59
def prefixEnd_4212637 : Nat := 4983230072969 + 3 ^ 40 * 4212637 * 2
def baseEnd_4212637 : Nat := 80115096441279250817183

theorem tailTrace_4212637 : CollatzResearch.WordTrace tailWord_4212637 prefixEnd_4212637 80115096441279250817183 := by
  unfold tailWord_4212637
  simp only [CollatzResearch.WordTrace]
  refine ⟨153647494039343084965484165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102431662692895389976989443 153647494039343084965484165)
  ·
    refine ⟨28808905132376828431028281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153647494039343084965484165 28808905132376828431028281)
    ·
      refine ⟨21606678849282621323271211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28808905132376828431028281 21606678849282621323271211)
      ·
        refine ⟨32410018273923931984906817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21606678849282621323271211 32410018273923931984906817)
        ·
          refine ⟨24307513705442948988680113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32410018273923931984906817 24307513705442948988680113)
          ·
            refine ⟨18230635279082211741510085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24307513705442948988680113 18230635279082211741510085)
            ·
              refine ⟨3418244114827914701533141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18230635279082211741510085 3418244114827914701533141)
              ·
                refine ⟨80115096441279250817183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3418244114827914701533141 80115096441279250817183)
                ·
                  rfl

theorem cell23_4212637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 7].length) (baseStart_4212637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212637 prefixEnd_4212637 := by exact prefixLift 4212637
  have htrace : WordTrace (prefixWord ++ tailWord_4212637) baseStart_4212637 baseEnd_4212637 := by
    simpa [prefixWord, tailWord_4212637, baseEnd_4212637] using wordTrace_append hprefix tailTrace_4212637
  have hstable : (prefixWord ++ tailWord_4212637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212637).length < 2 ^ (prefixWord ++ tailWord_4212637).sum := by decide
  have hdescent : baseEnd_4212637 < baseStart_4212637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212664 : List Nat := [2, 1, 2, 1, 2, 3, 2, 4, 2, 1, 3]
def baseStart_4212664 : Nat := 118140960795 + 4212664 * 2 ^ 59
def prefixEnd_4212664 : Nat := 4983230072969 + 3 ^ 40 * 4212664 * 2
def baseEnd_4212664 : Nat := 2163121467892211166426317

theorem tailTrace_4212664 : CollatzResearch.WordTrace tailWord_4212664 prefixEnd_4212664 2163121467892211166426317 := by
  unfold tailWord_4212664
  simp only [CollatzResearch.WordTrace]
  refine ⟨76824239405122634288358523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102432319206830179051144697 76824239405122634288358523)
  ·
    refine ⟨115236359107683951432537785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76824239405122634288358523 115236359107683951432537785)
    ·
      refine ⟨86427269330762963574403339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115236359107683951432537785 86427269330762963574403339)
      ·
        refine ⟨129640903996144445361605009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86427269330762963574403339 129640903996144445361605009)
        ·
          refine ⟨97230677997108334021203757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129640903996144445361605009 97230677997108334021203757)
          ·
            refine ⟨36461504248915625257951409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97230677997108334021203757 36461504248915625257951409)
            ·
              refine ⟨27346128186686718943463557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36461504248915625257951409 27346128186686718943463557)
              ·
                refine ⟨5127399035003759801899417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27346128186686718943463557 5127399035003759801899417)
                ·
                  refine ⟨3845549276252819851424563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5127399035003759801899417 3845549276252819851424563)
                  ·
                    refine ⟨5768323914379229777136845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3845549276252819851424563 5768323914379229777136845)
                    ·
                      refine ⟨2163121467892211166426317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5768323914379229777136845 2163121467892211166426317)
                      ·
                        rfl

theorem cell23_4212664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 2, 1, 3].length) (baseStart_4212664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212664 prefixEnd_4212664 := by exact prefixLift 4212664
  have htrace : WordTrace (prefixWord ++ tailWord_4212664) baseStart_4212664 baseEnd_4212664 := by
    simpa [prefixWord, tailWord_4212664, baseEnd_4212664] using wordTrace_append hprefix tailTrace_4212664
  have hstable : (prefixWord ++ tailWord_4212664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212664).length < 2 ^ (prefixWord ++ tailWord_4212664).sum := by decide
  have hdescent : baseEnd_4212664 < baseStart_4212664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212704 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 6, 2, 2]
def baseStart_4212704 : Nat := 118140960795 + 4212704 * 2 ^ 59
def prefixEnd_4212704 : Nat := 4983230072969 + 3 ^ 40 * 4212704 * 2
def baseEnd_4212704 : Nat := 2163142007118391009926133

theorem tailTrace_4212704 : CollatzResearch.WordTrace tailWord_4212704 prefixEnd_4212704 2163142007118391009926133 := by
  unfold tailWord_4212704
  simp only [CollatzResearch.WordTrace]
  refine ⟨76824968865050177704086583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102433291820066903605448777 76824968865050177704086583)
  ·
    refine ⟨115237453297575266556129875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76824968865050177704086583 115237453297575266556129875)
    ·
      refine ⟨172856179946362899834194813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115237453297575266556129875 172856179946362899834194813)
      ·
        refine ⟨64821067479886087437823055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172856179946362899834194813 64821067479886087437823055)
        ·
          refine ⟨97231601219829131156734583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64821067479886087437823055 97231601219829131156734583)
          ·
            refine ⟨145847401829743696735101875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97231601219829131156734583 145847401829743696735101875)
            ·
              refine ⟨218771102744615545102652813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145847401829743696735101875 218771102744615545102652813)
              ·
                refine ⟨82039163529230829413494805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 218771102744615545102652813 82039163529230829413494805)
                ·
                  refine ⟨3845585790432695128757569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 82039163529230829413494805 3845585790432695128757569)
                  ·
                    refine ⟨2884189342824521346568177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3845585790432695128757569 2884189342824521346568177)
                    ·
                      refine ⟨2163142007118391009926133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2884189342824521346568177 2163142007118391009926133)
                      ·
                        rfl

theorem cell23_4212704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_4212704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212704 prefixEnd_4212704 := by exact prefixLift 4212704
  have htrace : WordTrace (prefixWord ++ tailWord_4212704) baseStart_4212704 baseEnd_4212704 := by
    simpa [prefixWord, tailWord_4212704, baseEnd_4212704] using wordTrace_append hprefix tailTrace_4212704
  have hstable : (prefixWord ++ tailWord_4212704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212704).length < 2 ^ (prefixWord ++ tailWord_4212704).sum := by decide
  have hdescent : baseEnd_4212704 < baseStart_4212704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212707 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 5]
def baseStart_4212707 : Nat := 118140960795 + 4212707 * 2 ^ 59
def prefixEnd_4212707 : Nat := 4983230072969 + 3 ^ 40 * 4212707 * 2
def baseEnd_4212707 : Nat := 2163143547560354498188619

theorem tailTrace_4212707 : CollatzResearch.WordTrace tailWord_4212707 prefixEnd_4212707 2163143547560354498188619 := by
  unfold tailWord_4212707
  simp only [CollatzResearch.WordTrace]
  refine ⟨153650047149089486920532375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102433364766059657947021583 153650047149089486920532375)
  ·
    refine ⟨230475070723634230380798563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153650047149089486920532375 230475070723634230380798563)
    ·
      refine ⟨345712606085451345571197845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230475070723634230380798563 345712606085451345571197845)
      ·
        refine ⟨16205278410255531823649899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 345712606085451345571197845 16205278410255531823649899)
        ·
          refine ⟨24307917615383297735474849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16205278410255531823649899 24307917615383297735474849)
          ·
            refine ⟨18230938211537473301606137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24307917615383297735474849 18230938211537473301606137)
            ·
              refine ⟨13673203658653104976204603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18230938211537473301606137 13673203658653104976204603)
              ·
                refine ⟨20509805487979657464306905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13673203658653104976204603 20509805487979657464306905)
                ·
                  refine ⟨15382354115984743098230179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20509805487979657464306905 15382354115984743098230179)
                  ·
                    refine ⟨23073531173977114647345269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15382354115984743098230179 23073531173977114647345269)
                    ·
                      refine ⟨2163143547560354498188619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23073531173977114647345269 2163143547560354498188619)
                      ·
                        rfl

theorem cell23_4212707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_4212707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212707 prefixEnd_4212707 := by exact prefixLift 4212707
  have htrace : WordTrace (prefixWord ++ tailWord_4212707) baseStart_4212707 baseEnd_4212707 := by
    simpa [prefixWord, tailWord_4212707, baseEnd_4212707] using wordTrace_append hprefix tailTrace_4212707
  have hstable : (prefixWord ++ tailWord_4212707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212707).length < 2 ^ (prefixWord ++ tailWord_4212707).sum := by decide
  have hdescent : baseEnd_4212707 < baseStart_4212707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212720 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 7]
def baseStart_4212720 : Nat := 118140960795 + 4212720 * 2 ^ 59
def prefixEnd_4212720 : Nat := 4983230072969 + 3 ^ 40 * 4212720 * 2
def baseEnd_4212720 : Nat := 2163150222808862947326059

theorem tailTrace_4212720 : CollatzResearch.WordTrace tailWord_4212720 prefixEnd_4212720 2163150222808862947326059 := by
  unfold tailWord_4212720
  simp only [CollatzResearch.WordTrace]
  refine ⟨76825260649021195070377807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102433680865361593427170409 76825260649021195070377807)
  ·
    refine ⟨115237890973531792605566711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76825260649021195070377807 115237890973531792605566711)
    ·
      refine ⟨172856836460297688908350067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115237890973531792605566711 172856836460297688908350067)
      ·
        refine ⟨259285254690446533362525101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172856836460297688908350067 259285254690446533362525101)
        ·
          refine ⟨97231970508917450010946913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259285254690446533362525101 97231970508917450010946913)
          ·
            refine ⟨72923977881688087508210185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97231970508917450010946913 72923977881688087508210185)
            ·
              refine ⟨54692983411266065631157639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72923977881688087508210185 54692983411266065631157639)
              ·
                refine ⟨82039475116899098446736459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54692983411266065631157639 82039475116899098446736459)
                ·
                  refine ⟨123059212675348647670104689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82039475116899098446736459 123059212675348647670104689)
                  ·
                    refine ⟨92294409506511485752578517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 123059212675348647670104689 92294409506511485752578517)
                    ·
                      refine ⟨2163150222808862947326059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92294409506511485752578517 2163150222808862947326059)
                      ·
                        rfl

theorem cell23_4212720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 7].length) (baseStart_4212720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212720 prefixEnd_4212720 := by exact prefixLift 4212720
  have htrace : WordTrace (prefixWord ++ tailWord_4212720) baseStart_4212720 baseEnd_4212720 := by
    simpa [prefixWord, tailWord_4212720, baseEnd_4212720] using wordTrace_append hprefix tailTrace_4212720
  have hstable : (prefixWord ++ tailWord_4212720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212720).length < 2 ^ (prefixWord ++ tailWord_4212720).sum := by decide
  have hdescent : baseEnd_4212720 < baseStart_4212720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212730 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8]
def baseStart_4212730 : Nat := 118140960795 + 4212730 * 2 ^ 59
def prefixEnd_4212730 : Nat := 4983230072969 + 3 ^ 40 * 4212730 * 2
def baseEnd_4212730 : Nat := 2163155357615407908201013

theorem tailTrace_4212730 : CollatzResearch.WordTrace tailWord_4212730 prefixEnd_4212730 2163155357615407908201013 := by
  unfold tailWord_4212730
  simp only [CollatzResearch.WordTrace]
  refine ⟨38412721507001540462154911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102433924018670774565746429 38412721507001540462154911)
  ·
    refine ⟨57619082260502310693232367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38412721507001540462154911 57619082260502310693232367)
    ·
      refine ⟨86428623390753466039848551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57619082260502310693232367 86428623390753466039848551)
      ·
        refine ⟨129642935086130199059772827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86428623390753466039848551 129642935086130199059772827)
        ·
          refine ⟨194464402629195298589659241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129642935086130199059772827 194464402629195298589659241)
          ·
            refine ⟨145848301971896473942244431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 194464402629195298589659241 145848301971896473942244431)
            ·
              refine ⟨218772452957844710913366647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145848301971896473942244431 218772452957844710913366647)
              ·
                refine ⟨328158679436767066370049971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218772452957844710913366647 328158679436767066370049971)
                ·
                  refine ⟨492238019155150599555074957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 328158679436767066370049971 492238019155150599555074957)
                  ·
                    refine ⟨184589257183181474833153109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 492238019155150599555074957 184589257183181474833153109)
                    ·
                      refine ⟨2163155357615407908201013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 184589257183181474833153109 2163155357615407908201013)
                      ·
                        rfl

theorem cell23_4212730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_4212730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212730 prefixEnd_4212730 := by exact prefixLift 4212730
  have htrace : WordTrace (prefixWord ++ tailWord_4212730) baseStart_4212730 baseEnd_4212730 := by
    simpa [prefixWord, tailWord_4212730, baseEnd_4212730] using wordTrace_append hprefix tailTrace_4212730
  have hstable : (prefixWord ++ tailWord_4212730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212730).length < 2 ^ (prefixWord ++ tailWord_4212730).sum := by decide
  have hdescent : baseEnd_4212730 < baseStart_4212730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212734 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_4212734 : Nat := 118140960795 + 4212734 * 2 ^ 59
def prefixEnd_4212734 : Nat := 4983230072969 + 3 ^ 40 * 4212734 * 2
def baseEnd_4212734 : Nat := 2163157411538025892550995

theorem tailTrace_4212734 : CollatzResearch.WordTrace tailWord_4212734 prefixEnd_4212734 2163157411538025892550995 := by
  unfold tailWord_4212734
  simp only [CollatzResearch.WordTrace]
  refine ⟨19206378989998958816470657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102434021279994447021176837 19206378989998958816470657)
  ·
    refine ⟨14404784242499219112352993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19206378989998958816470657 14404784242499219112352993)
    ·
      refine ⟨10803588181874414334264745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14404784242499219112352993 10803588181874414334264745)
      ·
        refine ⟨8102691136405810750698559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10803588181874414334264745 8102691136405810750698559)
        ·
          refine ⟨12154036704608716126047839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8102691136405810750698559 12154036704608716126047839)
          ·
            refine ⟨18231055056913074189071759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12154036704608716126047839 18231055056913074189071759)
            ·
              refine ⟨27346582585369611283607639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18231055056913074189071759 27346582585369611283607639)
              ·
                refine ⟨41019873878054416925411459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27346582585369611283607639 41019873878054416925411459)
                ·
                  refine ⟨61529810817081625388117189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41019873878054416925411459 61529810817081625388117189)
                  ·
                    refine ⟨11536839528202804760271973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61529810817081625388117189 11536839528202804760271973)
                    ·
                      refine ⟨2163157411538025892550995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11536839528202804760271973 2163157411538025892550995)
                      ·
                        rfl

theorem cell23_4212734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_4212734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212734 prefixEnd_4212734 := by exact prefixLift 4212734
  have htrace : WordTrace (prefixWord ++ tailWord_4212734) baseStart_4212734 baseEnd_4212734 := by
    simpa [prefixWord, tailWord_4212734, baseEnd_4212734] using wordTrace_append hprefix tailTrace_4212734
  have hstable : (prefixWord ++ tailWord_4212734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212734).length < 2 ^ (prefixWord ++ tailWord_4212734).sum := by decide
  have hdescent : baseEnd_4212734 < baseStart_4212734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212772 : List Nat := [2, 3, 1, 4, 3, 1, 1, 2, 2, 2, 2]
def baseStart_4212772 : Nat := 118140960795 + 4212772 * 2 ^ 59
def prefixEnd_4212772 : Nat := 4983230072969 + 3 ^ 40 * 4212772 * 2
def baseEnd_4212772 : Nat := 2163176923802896743875821

theorem tailTrace_4212772 : CollatzResearch.WordTrace tailWord_4212772 prefixEnd_4212772 2163176923802896743875821 := by
  unfold tailWord_4212772
  simp only [CollatzResearch.WordTrace]
  refine ⟨76826208946927001510824285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102434945262569335347765713 76826208946927001510824285)
  ·
    refine ⟨28809828355097625566559107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76826208946927001510824285 28809828355097625566559107)
    ·
      refine ⟨43214742532646438349838661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28809828355097625566559107 43214742532646438349838661)
      ·
        refine ⟨8102764224871207190594749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43214742532646438349838661 8102764224871207190594749)
        ·
          refine ⟨3038536584326702696473031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8102764224871207190594749 3038536584326702696473031)
          ·
            refine ⟨4557804876490054044709547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3038536584326702696473031 4557804876490054044709547)
            ·
              refine ⟨6836707314735081067064321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4557804876490054044709547 6836707314735081067064321)
              ·
                refine ⟨5127530486051310800298241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6836707314735081067064321 5127530486051310800298241)
                ·
                  refine ⟨3845647864538483100223681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5127530486051310800298241 3845647864538483100223681)
                  ·
                    refine ⟨2884235898403862325167761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3845647864538483100223681 2884235898403862325167761)
                    ·
                      refine ⟨2163176923802896743875821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2884235898403862325167761 2163176923802896743875821)
                      ·
                        rfl

theorem cell23_4212772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_4212772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212772 prefixEnd_4212772 := by exact prefixLift 4212772
  have htrace : WordTrace (prefixWord ++ tailWord_4212772) baseStart_4212772 baseEnd_4212772 := by
    simpa [prefixWord, tailWord_4212772, baseEnd_4212772] using wordTrace_append hprefix tailTrace_4212772
  have hstable : (prefixWord ++ tailWord_4212772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212772).length < 2 ^ (prefixWord ++ tailWord_4212772).sum := by decide
  have hdescent : baseEnd_4212772 < baseStart_4212772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212807 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_4212807 : Nat := 118140960795 + 4212807 * 2 ^ 59
def prefixEnd_4212807 : Nat := 4983230072969 + 3 ^ 40 * 4212807 * 2
def baseEnd_4212807 : Nat := 2163194895625804106938159

theorem tailTrace_4212807 : CollatzResearch.WordTrace tailWord_4212807 prefixEnd_4212807 2163194895625804106938159 := by
  unfold tailWord_4212807
  simp only [CollatzResearch.WordTrace]
  refine ⟨153653694448727203999172675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102435796299151469332781783 153653694448727203999172675)
  ·
    refine ⟨230480541673090805998759013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153653694448727203999172675 230480541673090805998759013)
    ·
      refine ⟨43215101563704526124767315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230480541673090805998759013 43215101563704526124767315)
      ·
        refine ⟨64822652345556789187150973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43215101563704526124767315 64822652345556789187150973)
        ·
          refine ⟨24308494629583795945181615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64822652345556789187150973 24308494629583795945181615)
          ·
            refine ⟨36462741944375693917772423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24308494629583795945181615 36462741944375693917772423)
            ·
              refine ⟨54694112916563540876658635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36462741944375693917772423 54694112916563540876658635)
              ·
                refine ⟨82041169374845311314987953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54694112916563540876658635 82041169374845311314987953)
                ·
                  refine ⟨61530877031133983486240965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 82041169374845311314987953 61530877031133983486240965)
                  ·
                    refine ⟨11537039443337621903670181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61530877031133983486240965 11537039443337621903670181)
                    ·
                      refine ⟨2163194895625804106938159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11537039443337621903670181 2163194895625804106938159)
                      ·
                        rfl

theorem cell23_4212807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_4212807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212807 prefixEnd_4212807 := by exact prefixLift 4212807
  have htrace : WordTrace (prefixWord ++ tailWord_4212807) baseStart_4212807 baseEnd_4212807 := by
    simpa [prefixWord, tailWord_4212807, baseEnd_4212807] using wordTrace_append hprefix tailTrace_4212807
  have hstable : (prefixWord ++ tailWord_4212807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212807).length < 2 ^ (prefixWord ++ tailWord_4212807).sum := by decide
  have hdescent : baseEnd_4212807 < baseStart_4212807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212814 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3]
def baseStart_4212814 : Nat := 118140960795 + 4212814 * 2 ^ 59
def prefixEnd_4212814 : Nat := 4983230072969 + 3 ^ 40 * 4212814 * 2
def baseEnd_4212814 : Nat := 2163198489990385579550627

theorem tailTrace_4212814 : CollatzResearch.WordTrace tailWord_4212814 prefixEnd_4212814 2163198489990385579550627 := by
  unfold tailWord_4212814
  simp only [CollatzResearch.WordTrace]
  refine ⟨19206743719962730524334687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102435966506467896129784997 19206743719962730524334687)
  ·
    refine ⟨28810115579944095786502031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19206743719962730524334687 28810115579944095786502031)
    ·
      refine ⟨43215173369916143679753047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28810115579944095786502031 43215173369916143679753047)
      ·
        refine ⟨64822760054874215519629571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43215173369916143679753047 64822760054874215519629571)
        ·
          refine ⟨97234140082311323279444357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64822760054874215519629571 97234140082311323279444357)
          ·
            refine ⟨18231401265433373114895817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97234140082311323279444357 18231401265433373114895817)
            ·
              refine ⟨13673550949075029836171863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18231401265433373114895817 13673550949075029836171863)
              ·
                refine ⟨20510326423612544754257795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13673550949075029836171863 20510326423612544754257795)
                ·
                  refine ⟨30765489635418817131386693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20510326423612544754257795 30765489635418817131386693)
                  ·
                    refine ⟨5768529306641028212135005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30765489635418817131386693 5768529306641028212135005)
                    ·
                      refine ⟨2163198489990385579550627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5768529306641028212135005 2163198489990385579550627)
                      ·
                        rfl

theorem cell23_4212814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_4212814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212814 prefixEnd_4212814 := by exact prefixLift 4212814
  have htrace : WordTrace (prefixWord ++ tailWord_4212814) baseStart_4212814 baseEnd_4212814 := by
    simpa [prefixWord, tailWord_4212814, baseEnd_4212814] using wordTrace_append hprefix tailTrace_4212814
  have hstable : (prefixWord ++ tailWord_4212814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212814).length < 2 ^ (prefixWord ++ tailWord_4212814).sum := by decide
  have hdescent : baseEnd_4212814 < baseStart_4212814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212871 : List Nat := [1, 1, 4, 2, 1, 1, 3, 3, 2, 3, 2]
def baseStart_4212871 : Nat := 118140960795 + 4212871 * 2 ^ 59
def prefixEnd_4212871 : Nat := 4983230072969 + 3 ^ 40 * 4212871 * 2
def baseEnd_4212871 : Nat := 2163227758387691856537865

theorem tailTrace_4212871 : CollatzResearch.WordTrace tailWord_4212871 prefixEnd_4212871 2163227758387691856537865 := by
  unfold tailWord_4212871
  simp only [CollatzResearch.WordTrace]
  refine ⟨153656028720495342929502467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102437352480330228619668311 153656028720495342929502467)
  ·
    refine ⟨230484043080743014394253701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153656028720495342929502467 230484043080743014394253701)
    ·
      refine ⟨43215758077639315198922569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230484043080743014394253701 43215758077639315198922569)
      ·
        refine ⟨32411818558229486399191927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43215758077639315198922569 32411818558229486399191927)
        ·
          refine ⟨48617727837344229598787891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32411818558229486399191927 48617727837344229598787891)
          ·
            refine ⟨72926591756016344398181837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48617727837344229598787891 72926591756016344398181837)
            ·
              refine ⟨27347471908506129149318189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72926591756016344398181837 27347471908506129149318189)
              ·
                refine ⟨10255301965689798430994321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27347471908506129149318189 10255301965689798430994321)
                ·
                  refine ⟨7691476474267348823245741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10255301965689798430994321 7691476474267348823245741)
                  ·
                    refine ⟨2884303677850255808717153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7691476474267348823245741 2884303677850255808717153)
                    ·
                      refine ⟨2163227758387691856537865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2884303677850255808717153 2163227758387691856537865)
                      ·
                        rfl

theorem cell23_4212871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_4212871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212871 prefixEnd_4212871 := by exact prefixLift 4212871
  have htrace : WordTrace (prefixWord ++ tailWord_4212871) baseStart_4212871 baseEnd_4212871 := by
    simpa [prefixWord, tailWord_4212871, baseEnd_4212871] using wordTrace_append hprefix tailTrace_4212871
  have hstable : (prefixWord ++ tailWord_4212871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212871).length < 2 ^ (prefixWord ++ tailWord_4212871).sum := by decide
  have hdescent : baseEnd_4212871 < baseStart_4212871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212895 : List Nat := [1, 1, 2, 6, 1, 2, 1, 4, 1, 1, 3]
def baseStart_4212895 : Nat := 118140960795 + 4212895 * 2 ^ 59
def prefixEnd_4212895 : Nat := 4983230072969 + 3 ^ 40 * 4212895 * 2
def baseEnd_4212895 : Nat := 2163240081923399762637755

theorem tailTrace_4212895 : CollatzResearch.WordTrace tailWord_4212895 prefixEnd_4212895 2163240081923399762637755 := by
  unfold tailWord_4212895
  simp only [CollatzResearch.WordTrace]
  refine ⟨153656904072408395028376139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102437936048272263352250759 153656904072408395028376139)
  ·
    refine ⟨230485356108612592542564209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153656904072408395028376139 230485356108612592542564209)
    ·
      refine ⟨172864017081459444406923157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230485356108612592542564209 172864017081459444406923157)
      ·
        refine ⟨8103000800693411456574523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 172864017081459444406923157 8103000800693411456574523)
        ·
          refine ⟨12154501201040117184861785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8103000800693411456574523 12154501201040117184861785)
          ·
            refine ⟨9115875900780087888646339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12154501201040117184861785 9115875900780087888646339)
            ·
              refine ⟨13673813851170131832969509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9115875900780087888646339 13673813851170131832969509)
              ·
                refine ⟨2563840097094399718681783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13673813851170131832969509 2563840097094399718681783)
                ·
                  refine ⟨3845760145641599578022675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2563840097094399718681783 3845760145641599578022675)
                  ·
                    refine ⟨5768640218462399367034013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3845760145641599578022675 5768640218462399367034013)
                    ·
                      refine ⟨2163240081923399762637755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5768640218462399367034013 2163240081923399762637755)
                      ·
                        rfl

theorem cell23_4212895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_4212895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212895 prefixEnd_4212895 := by exact prefixLift 4212895
  have htrace : WordTrace (prefixWord ++ tailWord_4212895) baseStart_4212895 baseEnd_4212895 := by
    simpa [prefixWord, tailWord_4212895, baseEnd_4212895] using wordTrace_append hprefix tailTrace_4212895
  have hstable : (prefixWord ++ tailWord_4212895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212895).length < 2 ^ (prefixWord ++ tailWord_4212895).sum := by decide
  have hdescent : baseEnd_4212895 < baseStart_4212895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212921 : List Nat := [1, 2, 1, 4, 1, 2, 2, 4, 1, 2, 3]
def baseStart_4212921 : Nat := 118140960795 + 4212921 * 2 ^ 59
def prefixEnd_4212921 : Nat := 4983230072969 + 3 ^ 40 * 4212921 * 2
def baseEnd_4212921 : Nat := 2163253432420416660912635

theorem tailTrace_4212921 : CollatzResearch.WordTrace tailWord_4212921 prefixEnd_4212921 2163253432420416660912635 := by
  unfold tailWord_4212921
  simp only [CollatzResearch.WordTrace]
  refine ⟨153657852370314201468822617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102438568246876134312548411 153657852370314201468822617)
  ·
    refine ⟨115243389277735651101616963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153657852370314201468822617 115243389277735651101616963)
    ·
      refine ⟨172865083916603476652425445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115243389277735651101616963 172865083916603476652425445)
      ·
        refine ⟨32412203234363151872329771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172865083916603476652425445 32412203234363151872329771)
        ·
          refine ⟨48618304851544727808494657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32412203234363151872329771 48618304851544727808494657)
          ·
            refine ⟨36463728638658545856370993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48618304851544727808494657 36463728638658545856370993)
            ·
              refine ⟨27347796478993909392278245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36463728638658545856370993 27347796478993909392278245)
              ·
                refine ⟨5127711839811358011052171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27347796478993909392278245 5127711839811358011052171)
                ·
                  refine ⟨7691567759717037016578257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5127711839811358011052171 7691567759717037016578257)
                  ·
                    refine ⟨5768675819787777762433693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7691567759717037016578257 5768675819787777762433693)
                    ·
                      refine ⟨2163253432420416660912635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5768675819787777762433693 2163253432420416660912635)
                      ·
                        rfl

theorem cell23_4212921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_4212921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212921 prefixEnd_4212921 := by exact prefixLift 4212921
  have htrace : WordTrace (prefixWord ++ tailWord_4212921) baseStart_4212921 baseEnd_4212921 := by
    simpa [prefixWord, tailWord_4212921, baseEnd_4212921] using wordTrace_append hprefix tailTrace_4212921
  have hstable : (prefixWord ++ tailWord_4212921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212921).length < 2 ^ (prefixWord ++ tailWord_4212921).sum := by decide
  have hdescent : baseEnd_4212921 < baseStart_4212921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212937 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 1, 9]
def baseStart_4212937 : Nat := 118140960795 + 4212937 * 2 ^ 59
def prefixEnd_4212937 : Nat := 4983230072969 + 3 ^ 40 * 4212937 * 2
def baseEnd_4212937 : Nat := 721087216036962866104187

theorem tailTrace_4212937 : CollatzResearch.WordTrace tailWord_4212937 prefixEnd_4212937 721087216036962866104187 := by
  unfold tailWord_4212937
  simp only [CollatzResearch.WordTrace]
  refine ⟨153658435938256236201405065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102438957292170824134270043 153658435938256236201405065)
  ·
    refine ⟨115243826953692177151053799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153658435938256236201405065 115243826953692177151053799)
    ·
      refine ⟨172865740430538265726580699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115243826953692177151053799 172865740430538265726580699)
      ·
        refine ⟨259298610645807398589871049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172865740430538265726580699 259298610645807398589871049)
        ·
          refine ⟨194473957984355548942403287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259298610645807398589871049 194473957984355548942403287)
          ·
            refine ⟨291710936976533323413604931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194473957984355548942403287 291710936976533323413604931)
            ·
              refine ⟨437566405464799985120407397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291710936976533323413604931 437566405464799985120407397)
              ·
                refine ⟨82043701024649997210076387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 437566405464799985120407397 82043701024649997210076387)
                ·
                  refine ⟨123065551536974995815114581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82043701024649997210076387 123065551536974995815114581)
                  ·
                    refine ⟨721087216036962866104187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 123065551536974995815114581 721087216036962866104187)
                    ·
                      rfl

theorem cell23_4212937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 9].length) (baseStart_4212937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212937 prefixEnd_4212937 := by exact prefixLift 4212937
  have htrace : WordTrace (prefixWord ++ tailWord_4212937) baseStart_4212937 baseEnd_4212937 := by
    simpa [prefixWord, tailWord_4212937, baseEnd_4212937] using wordTrace_append hprefix tailTrace_4212937
  have hstable : (prefixWord ++ tailWord_4212937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212937).length < 2 ^ (prefixWord ++ tailWord_4212937).sum := by decide
  have hdescent : baseEnd_4212937 < baseStart_4212937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212947 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 7]
def baseStart_4212947 : Nat := 118140960795 + 4212947 * 2 ^ 59
def prefixEnd_4212947 : Nat := 4983230072969 + 3 ^ 40 * 4212947 * 2
def baseEnd_4212947 : Nat := 2163266782917433559187515

theorem tailTrace_4212947 : CollatzResearch.WordTrace tailWord_4212947 prefixEnd_4212947 2163266782917433559187515 := by
  unfold tailWord_4212947
  simp only [CollatzResearch.WordTrace]
  refine ⟨153658800668220007909269095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102439200445480005272846063 153658800668220007909269095)
  ·
    refine ⟨230488201002330011863903643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153658800668220007909269095 230488201002330011863903643)
    ·
      refine ⟨345732301503495017795855465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230488201002330011863903643 345732301503495017795855465)
      ·
        refine ⟨259299226127621263346891599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345732301503495017795855465 259299226127621263346891599)
        ·
          refine ⟨388948839191431895020337399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259299226127621263346891599 388948839191431895020337399)
          ·
            refine ⟨583423258787147842530506099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 388948839191431895020337399 583423258787147842530506099)
            ·
              refine ⟨875134888180721763795759149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 583423258787147842530506099 875134888180721763795759149)
              ·
                refine ⟨328175583067770661423409681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 875134888180721763795759149 328175583067770661423409681)
                ·
                  refine ⟨246131687300827996067557261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 328175583067770661423409681 246131687300827996067557261)
                  ·
                    refine ⟨92299382737810498525333973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 246131687300827996067557261 92299382737810498525333973)
                    ·
                      refine ⟨2163266782917433559187515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92299382737810498525333973 2163266782917433559187515)
                      ·
                        rfl

theorem cell23_4212947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_4212947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212947 prefixEnd_4212947 := by exact prefixLift 4212947
  have htrace : WordTrace (prefixWord ++ tailWord_4212947) baseStart_4212947 baseEnd_4212947 := by
    simpa [prefixWord, tailWord_4212947, baseEnd_4212947] using wordTrace_append hprefix tailTrace_4212947
  have hstable : (prefixWord ++ tailWord_4212947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212947).length < 2 ^ (prefixWord ++ tailWord_4212947).sum := by decide
  have hdescent : baseEnd_4212947 < baseStart_4212947 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212962 : List Nat := [3, 3, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_4212962 : Nat := 118140960795 + 4212962 * 2 ^ 59
def prefixEnd_4212962 : Nat := 4983230072969 + 3 ^ 40 * 4212962 * 2
def baseEnd_4212962 : Nat := 721091495042417000166649

theorem tailTrace_4212962 : CollatzResearch.WordTrace tailWord_4212962 prefixEnd_4212962 721091495042417000166649 := by
  unfold tailWord_4212962
  simp only [CollatzResearch.WordTrace]
  refine ⟨38414836940791416367766285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102439565175443776980710093 38414836940791416367766285)
  ·
    refine ⟨14405563852796781137912357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38414836940791416367766285 14405563852796781137912357)
    ·
      refine ⟨2701043222399396463358567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14405563852796781137912357 2701043222399396463358567)
      ·
        refine ⟨4051564833599094695037851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2701043222399396463358567 4051564833599094695037851)
        ·
          refine ⟨6077347250398642042556777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4051564833599094695037851 6077347250398642042556777)
          ·
            refine ⟨4558010437798981531917583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6077347250398642042556777 4558010437798981531917583)
            ·
              refine ⟨6837015656698472297876375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4558010437798981531917583 6837015656698472297876375)
              ·
                refine ⟨10255523485047708446814563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6837015656698472297876375 10255523485047708446814563)
                ·
                  refine ⟨15383285227571562670221845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10255523485047708446814563 15383285227571562670221845)
                  ·
                    refine ⟨721091495042417000166649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15383285227571562670221845 721091495042417000166649)
                    ·
                      rfl

theorem cell23_4212962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_4212962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212962 prefixEnd_4212962 := by exact prefixLift 4212962
  have htrace : WordTrace (prefixWord ++ tailWord_4212962) baseStart_4212962 baseEnd_4212962 := by
    simpa [prefixWord, tailWord_4212962, baseEnd_4212962] using wordTrace_append hprefix tailTrace_4212962
  have hstable : (prefixWord ++ tailWord_4212962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212962).length < 2 ^ (prefixWord ++ tailWord_4212962).sum := by decide
  have hdescent : baseEnd_4212962 < baseStart_4212962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212968 : List Nat := [2, 1, 4, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_4212968 : Nat := 118140960795 + 4212968 * 2 ^ 59
def prefixEnd_4212968 : Nat := 4983230072969 + 3 ^ 40 * 4212968 * 2
def baseEnd_4212968 : Nat := 2163277566011177977024919

theorem tailTrace_4212968 : CollatzResearch.WordTrace tailWord_4212968 prefixEnd_4212968 2163277566011177977024919 := by
  unfold tailWord_4212968
  simp only [CollatzResearch.WordTrace]
  refine ⟨76829783300571964247891779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102439711067429285663855705 76829783300571964247891779)
  ·
    refine ⟨115244674950857946371837669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76829783300571964247891779 115244674950857946371837669)
    ·
      refine ⟨21608376553285864944719563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115244674950857946371837669 21608376553285864944719563)
      ·
        refine ⟨32412564829928797417079345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21608376553285864944719563 32412564829928797417079345)
        ·
          refine ⟨24309423622446598062809509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32412564829928797417079345 24309423622446598062809509)
          ·
            refine ⟨4558016929208737136776783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24309423622446598062809509 4558016929208737136776783)
            ·
              refine ⟨6837025393813105705165175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4558016929208737136776783 6837025393813105705165175)
              ·
                refine ⟨10255538090719658557747763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6837025393813105705165175 10255538090719658557747763)
                ·
                  refine ⟨15383307136079487836621645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10255538090719658557747763 15383307136079487836621645)
                  ·
                    refine ⟨5768740176029807938733117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15383307136079487836621645 5768740176029807938733117)
                    ·
                      refine ⟨2163277566011177977024919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5768740176029807938733117 2163277566011177977024919)
                      ·
                        rfl

theorem cell23_4212968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_4212968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212968 prefixEnd_4212968 := by exact prefixLift 4212968
  have htrace : WordTrace (prefixWord ++ tailWord_4212968) baseStart_4212968 baseEnd_4212968 := by
    simpa [prefixWord, tailWord_4212968, baseEnd_4212968] using wordTrace_append hprefix tailTrace_4212968
  have hstable : (prefixWord ++ tailWord_4212968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212968).length < 2 ^ (prefixWord ++ tailWord_4212968).sum := by decide
  have hdescent : baseEnd_4212968 < baseStart_4212968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4212991 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 3, 4, 2]
def baseStart_4212991 : Nat := 118140960795 + 4212991 * 2 ^ 59
def prefixEnd_4212991 : Nat := 4983230072969 + 3 ^ 40 * 4212991 * 2
def baseEnd_4212991 : Nat := 2163289376066231387037313

theorem tailTrace_4212991 : CollatzResearch.WordTrace tailWord_4212991 prefixEnd_4212991 2163289376066231387037313 := by
  unfold tailWord_4212991
  simp only [CollatzResearch.WordTrace]
  refine ⟨153660405480060603423870827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102440270320040402282580551 153660405480060603423870827)
  ·
    refine ⟨230490608220090905135806241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153660405480060603423870827 230490608220090905135806241)
    ·
      refine ⟨172867956165068178851854681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230490608220090905135806241 172867956165068178851854681)
      ·
        refine ⟨129650967123801134138891011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172867956165068178851854681 129650967123801134138891011)
        ·
          refine ⟨194476450685701701208336517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129650967123801134138891011 194476450685701701208336517)
          ·
            refine ⟨36464334503569068976563097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 194476450685701701208336517 36464334503569068976563097)
            ·
              refine ⟨27348250877676801732422323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36464334503569068976563097 27348250877676801732422323)
              ·
                refine ⟨41022376316515202598633485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27348250877676801732422323 41022376316515202598633485)
                ·
                  refine ⟨15383391118693200974487557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41022376316515202598633485 15383391118693200974487557)
                  ·
                    refine ⟨2884385834754975182716417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15383391118693200974487557 2884385834754975182716417)
                    ·
                      refine ⟨2163289376066231387037313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2884385834754975182716417 2163289376066231387037313)
                      ·
                        rfl

theorem cell23_4212991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 4, 2].length) (baseStart_4212991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4212991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4212991 prefixEnd_4212991 := by exact prefixLift 4212991
  have htrace : WordTrace (prefixWord ++ tailWord_4212991) baseStart_4212991 baseEnd_4212991 := by
    simpa [prefixWord, tailWord_4212991, baseEnd_4212991] using wordTrace_append hprefix tailTrace_4212991
  have hstable : (prefixWord ++ tailWord_4212991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4212991).length < 2 ^ (prefixWord ++ tailWord_4212991).sum := by decide
  have hdescent : baseEnd_4212991 < baseStart_4212991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4212991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213098 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_4213098 : Nat := 118140960795 + 4213098 * 2 ^ 59
def prefixEnd_4213098 : Nat := 4983230072969 + 3 ^ 40 * 4213098 * 2
def baseEnd_4213098 : Nat := 2163344318496262468399321

theorem tailTrace_4213098 : CollatzResearch.WordTrace tailWord_4213098 prefixEnd_4213098 2163344318496262468399321 := by
  unfold tailWord_4213098
  simp only [CollatzResearch.WordTrace]
  refine ⟨38416077022668240174503987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102442872060448640465343965 38416077022668240174503987)
  ·
    refine ⟨57624115534002360261755981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38416077022668240174503987 57624115534002360261755981)
    ·
      refine ⟨21609043325250885098158493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57624115534002360261755981 21609043325250885098158493)
      ·
        refine ⟨8103391246969081911809435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21609043325250885098158493 8103391246969081911809435)
        ·
          refine ⟨12155086870453622867714153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8103391246969081911809435 12155086870453622867714153)
          ·
            refine ⟨9116315152840217150785615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12155086870453622867714153 9116315152840217150785615)
            ·
              refine ⟨13674472729260325726178423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9116315152840217150785615 13674472729260325726178423)
              ·
                refine ⟨20511709093890488589267635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13674472729260325726178423 20511709093890488589267635)
                ·
                  refine ⟨30767563640835732883901453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20511709093890488589267635 30767563640835732883901453)
                  ·
                    refine ⟨11537836365313399831463045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30767563640835732883901453 11537836365313399831463045)
                    ·
                      refine ⟨2163344318496262468399321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11537836365313399831463045 2163344318496262468399321)
                      ·
                        rfl

theorem cell23_4213098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_4213098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213098 prefixEnd_4213098 := by exact prefixLift 4213098
  have htrace : WordTrace (prefixWord ++ tailWord_4213098) baseStart_4213098 baseEnd_4213098 := by
    simpa [prefixWord, tailWord_4213098, baseEnd_4213098] using wordTrace_append hprefix tailTrace_4213098
  have hstable : (prefixWord ++ tailWord_4213098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213098).length < 2 ^ (prefixWord ++ tailWord_4213098).sum := by decide
  have hdescent : baseEnd_4213098 < baseStart_4213098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213171 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 4]
def baseStart_4213171 : Nat := 118140960795 + 4213171 * 2 ^ 59
def prefixEnd_4213171 : Nat := 4983230072969 + 3 ^ 40 * 4213171 * 2
def baseEnd_4213171 : Nat := 2163381802584040682786485

theorem tailTrace_4213171 : CollatzResearch.WordTrace tailWord_4213171 prefixEnd_4213171 2163381802584040682786485 := by
  unfold tailWord_4213171
  simp only [CollatzResearch.WordTrace]
  refine ⟨153666970619408494165423367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102444647079605662776948911 153666970619408494165423367)
  ·
    refine ⟨230500455929112741248135051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153666970619408494165423367 230500455929112741248135051)
    ·
      refine ⟨345750683893669111872202577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230500455929112741248135051 345750683893669111872202577)
      ·
        refine ⟨259313012920251833904151933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345750683893669111872202577 259313012920251833904151933)
        ·
          refine ⟨97242379845094437714056975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259313012920251833904151933 97242379845094437714056975)
          ·
            refine ⟨145863569767641656571085463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97242379845094437714056975 145863569767641656571085463)
            ·
              refine ⟨218795354651462484856628195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145863569767641656571085463 218795354651462484856628195)
              ·
                refine ⟨328193031977193727284942293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218795354651462484856628195 328193031977193727284942293)
                ·
                  refine ⟨7692024186965477983240835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 328193031977193727284942293 7692024186965477983240835)
                  ·
                    refine ⟨11538036280448216974861253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7692024186965477983240835 11538036280448216974861253)
                    ·
                      refine ⟨2163381802584040682786485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11538036280448216974861253 2163381802584040682786485)
                      ·
                        rfl

theorem cell23_4213171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 7, 1, 4].length) (baseStart_4213171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213171 prefixEnd_4213171 := by exact prefixLift 4213171
  have htrace : WordTrace (prefixWord ++ tailWord_4213171) baseStart_4213171 baseEnd_4213171 := by
    simpa [prefixWord, tailWord_4213171, baseEnd_4213171] using wordTrace_append hprefix tailTrace_4213171
  have hstable : (prefixWord ++ tailWord_4213171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213171).length < 2 ^ (prefixWord ++ tailWord_4213171).sum := by decide
  have hdescent : baseEnd_4213171 < baseStart_4213171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213175 : List Nat := [1, 1, 3, 1, 3, 4, 1, 2, 2, 3, 2]
def baseStart_4213175 : Nat := 118140960795 + 4213175 * 2 ^ 59
def prefixEnd_4213175 : Nat := 4983230072969 + 3 ^ 40 * 4213175 * 2
def baseEnd_4213175 : Nat := 2163383856506658667136467

theorem tailTrace_4213175 : CollatzResearch.WordTrace tailWord_4213175 prefixEnd_4213175 2163383856506658667136467 := by
  unfold tailWord_4213175
  simp only [CollatzResearch.WordTrace]
  refine ⟨153667116511394002848568979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102444744340929335232379319 153667116511394002848568979)
  ·
    refine ⟨230500674767091004272853469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153667116511394002848568979 230500674767091004272853469)
    ·
      refine ⟨86437753037659126602320051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230500674767091004272853469 86437753037659126602320051)
      ·
        refine ⟨129656629556488689903480077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86437753037659126602320051 129656629556488689903480077)
        ·
          refine ⟨48621236083683258713805029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129656629556488689903480077 48621236083683258713805029)
          ·
            refine ⟨9116481765690611008838443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48621236083683258713805029 9116481765690611008838443)
            ·
              refine ⟨13674722648535916513257665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9116481765690611008838443 13674722648535916513257665)
              ·
                refine ⟨10256041986401937384943249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13674722648535916513257665 10256041986401937384943249)
                ·
                  refine ⟨7692031489801453038707437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10256041986401937384943249 7692031489801453038707437)
                  ·
                    refine ⟨2884511808675544889515289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7692031489801453038707437 2884511808675544889515289)
                    ·
                      refine ⟨2163383856506658667136467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2884511808675544889515289 2163383856506658667136467)
                      ·
                        rfl

theorem cell23_4213175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 3, 2].length) (baseStart_4213175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213175 prefixEnd_4213175 := by exact prefixLift 4213175
  have htrace : WordTrace (prefixWord ++ tailWord_4213175) baseStart_4213175 baseEnd_4213175 := by
    simpa [prefixWord, tailWord_4213175, baseEnd_4213175] using wordTrace_append hprefix tailTrace_4213175
  have hstable : (prefixWord ++ tailWord_4213175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213175).length < 2 ^ (prefixWord ++ tailWord_4213175).sum := by decide
  have hdescent : baseEnd_4213175 < baseStart_4213175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213182 : List Nat := [4, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3]
def baseStart_4213182 : Nat := 118140960795 + 4213182 * 2 ^ 59
def prefixEnd_4213182 : Nat := 4983230072969 + 3 ^ 40 * 4213182 * 2
def baseEnd_4213182 : Nat := 2163387450871240139748935

theorem tailTrace_4213182 : CollatzResearch.WordTrace tailWord_4213182 prefixEnd_4213182 2163387450871240139748935 := by
  unfold tailWord_4213182
  simp only [CollatzResearch.WordTrace]
  refine ⟨19208421477796080380509225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102444914548245762029382533 19208421477796080380509225)
  ·
    refine ⟨14406316108347060285381919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19208421477796080380509225 14406316108347060285381919)
    ·
      refine ⟨21609474162520590428072879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14406316108347060285381919 21609474162520590428072879)
      ·
        refine ⟨32414211243780885642109319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21609474162520590428072879 32414211243780885642109319)
        ·
          refine ⟨48621316865671328463163979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32414211243780885642109319 48621316865671328463163979)
          ·
            refine ⟨72931975298506992694745969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48621316865671328463163979 72931975298506992694745969)
            ·
              refine ⟨54698981473880244521059477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72931975298506992694745969 54698981473880244521059477)
              ·
                refine ⟨2564014756588136461924663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54698981473880244521059477 2564014756588136461924663)
                ·
                  refine ⟨3846022134882204692886995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2564014756588136461924663 3846022134882204692886995)
                  ·
                    refine ⟨5769033202323307039330493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3846022134882204692886995 5769033202323307039330493)
                    ·
                      refine ⟨2163387450871240139748935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5769033202323307039330493 2163387450871240139748935)
                      ·
                        rfl

theorem cell23_4213182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_4213182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213182 prefixEnd_4213182 := by exact prefixLift 4213182
  have htrace : WordTrace (prefixWord ++ tailWord_4213182) baseStart_4213182 baseEnd_4213182 := by
    simpa [prefixWord, tailWord_4213182, baseEnd_4213182] using wordTrace_append hprefix tailTrace_4213182
  have hstable : (prefixWord ++ tailWord_4213182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213182).length < 2 ^ (prefixWord ++ tailWord_4213182).sum := by decide
  have hdescent : baseEnd_4213182 < baseStart_4213182 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213201 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 5, 2, 4]
def baseStart_4213201 : Nat := 118140960795 + 4213201 * 2 ^ 59
def prefixEnd_4213201 : Nat := 4983230072969 + 3 ^ 40 * 4213201 * 2
def baseEnd_4213201 : Nat := 2163397207003675565411347

theorem tailTrace_4213201 : CollatzResearch.WordTrace tailWord_4213201 prefixEnd_4213201 2163397207003675565411347 := by
  unfold tailWord_4213201
  simp only [CollatzResearch.WordTrace]
  refine ⟨153668064809299809289015457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102445376539533206192676971 153668064809299809289015457)
  ·
    refine ⟨115251048606974856966761593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153668064809299809289015457 115251048606974856966761593)
    ·
      refine ⟨86438286455231142725071195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115251048606974856966761593 86438286455231142725071195)
      ·
        refine ⟨129657429682846714087606793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86438286455231142725071195 129657429682846714087606793)
        ·
          refine ⟨97243072262135035565705095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129657429682846714087606793 97243072262135035565705095)
          ·
            refine ⟨145864608393202553348557643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97243072262135035565705095 145864608393202553348557643)
            ·
              refine ⟨218796912589803830022836465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145864608393202553348557643 218796912589803830022836465)
              ·
                refine ⟨164097684442352872517127349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218796912589803830022836465 164097684442352872517127349)
                ·
                  refine ⟨15384157916470581798480689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 164097684442352872517127349 15384157916470581798480689)
                  ·
                    refine ⟨11538118437352936348860517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15384157916470581798480689 11538118437352936348860517)
                    ·
                      refine ⟨2163397207003675565411347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11538118437352936348860517 2163397207003675565411347)
                      ·
                        rfl

theorem cell23_4213201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_4213201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213201 prefixEnd_4213201 := by exact prefixLift 4213201
  have htrace : WordTrace (prefixWord ++ tailWord_4213201) baseStart_4213201 baseEnd_4213201 := by
    simpa [prefixWord, tailWord_4213201, baseEnd_4213201] using wordTrace_append hprefix tailTrace_4213201
  have hstable : (prefixWord ++ tailWord_4213201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213201).length < 2 ^ (prefixWord ++ tailWord_4213201).sum := by decide
  have hdescent : baseEnd_4213201 < baseStart_4213201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213205 : List Nat := [1, 3, 2, 3, 1, 2, 3, 2, 1, 1, 4]
def baseStart_4213205 : Nat := 118140960795 + 4213205 * 2 ^ 59
def prefixEnd_4213205 : Nat := 4983230072969 + 3 ^ 40 * 4213205 * 2
def baseEnd_4213205 : Nat := 2163399260926293549761329

theorem tailTrace_4213205 : CollatzResearch.WordTrace tailWord_4213205 prefixEnd_4213205 2163399260926293549761329 := by
  unfold tailWord_4213205
  simp only [CollatzResearch.WordTrace]
  refine ⟨153668210701285317972161069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102445473800856878648107379 153668210701285317972161069)
  ·
    refine ⟨57625579012981994239560401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153668210701285317972161069 57625579012981994239560401)
    ·
      refine ⟨43219184259736495679670301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57625579012981994239560401 43219184259736495679670301)
      ·
        refine ⟨16207194097401185879876363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43219184259736495679670301 16207194097401185879876363)
        ·
          refine ⟨24310791146101778819814545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16207194097401185879876363 24310791146101778819814545)
          ·
            refine ⟨18233093359576334114860909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24310791146101778819814545 18233093359576334114860909)
            ·
              refine ⟨6837410009841125293072841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18233093359576334114860909 6837410009841125293072841)
              ·
                refine ⟨5128057507380843969804631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6837410009841125293072841 5128057507380843969804631)
                ·
                  refine ⟨7692086261071265954706947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5128057507380843969804631 7692086261071265954706947)
                  ·
                    refine ⟨11538129391606898932060421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7692086261071265954706947 11538129391606898932060421)
                    ·
                      refine ⟨2163399260926293549761329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11538129391606898932060421 2163399260926293549761329)
                      ·
                        rfl

theorem cell23_4213205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_4213205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213205 prefixEnd_4213205 := by exact prefixLift 4213205
  have htrace : WordTrace (prefixWord ++ tailWord_4213205) baseStart_4213205 baseEnd_4213205 := by
    simpa [prefixWord, tailWord_4213205, baseEnd_4213205] using wordTrace_append hprefix tailTrace_4213205
  have hstable : (prefixWord ++ tailWord_4213205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213205).length < 2 ^ (prefixWord ++ tailWord_4213205).sum := by decide
  have hdescent : baseEnd_4213205 < baseStart_4213205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213241 : List Nat := [1, 2, 1, 3, 1, 2, 3, 1, 2, 7]
def baseStart_4213241 : Nat := 118140960795 + 4213241 * 2 ^ 59
def prefixEnd_4213241 : Nat := 4983230072969 + 3 ^ 40 * 4213241 * 2
def baseEnd_4213241 : Nat := 721139248743285136303721

theorem tailTrace_4213241 : CollatzResearch.WordTrace tailWord_4213241 prefixEnd_4213241 721139248743285136303721 := by
  unfold tailWord_4213241
  simp only [CollatzResearch.WordTrace]
  refine ⟨153669523729154896120471577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102446349152769930746981051 153669523729154896120471577)
  ·
    refine ⟨115252142796866172090353683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153669523729154896120471577 115252142796866172090353683)
    ·
      refine ⟨172878214195299258135530525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115252142796866172090353683 172878214195299258135530525)
      ·
        refine ⟨64829330323237221800823947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172878214195299258135530525 64829330323237221800823947)
        ·
          refine ⟨97243995484855832701235921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64829330323237221800823947 97243995484855832701235921)
          ·
            refine ⟨72932996613641874525926941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97243995484855832701235921 72932996613641874525926941)
            ·
              refine ⟨27349873730115702947222603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72932996613641874525926941 27349873730115702947222603)
              ·
                refine ⟨41024810595173554420833905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27349873730115702947222603 41024810595173554420833905)
                ·
                  refine ⟨30768607946380165815625429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41024810595173554420833905 30768607946380165815625429)
                  ·
                    refine ⟨721139248743285136303721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30768607946380165815625429 721139248743285136303721)
                    ·
                      rfl

theorem cell23_4213241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 7].length) (baseStart_4213241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213241 prefixEnd_4213241 := by exact prefixLift 4213241
  have htrace : WordTrace (prefixWord ++ tailWord_4213241) baseStart_4213241 baseEnd_4213241 := by
    simpa [prefixWord, tailWord_4213241, baseEnd_4213241] using wordTrace_append hprefix tailTrace_4213241
  have hstable : (prefixWord ++ tailWord_4213241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213241).length < 2 ^ (prefixWord ++ tailWord_4213241).sum := by decide
  have hdescent : baseEnd_4213241 < baseStart_4213241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213298 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3]
def baseStart_4213298 : Nat := 118140960795 + 4213298 * 2 ^ 59
def prefixEnd_4213298 : Nat := 4983230072969 + 3 ^ 40 * 4213298 * 2
def baseEnd_4213298 : Nat := 2163447014627161685898401

theorem tailTrace_4213298 : CollatzResearch.WordTrace tailWord_4213298 prefixEnd_4213298 2163447014627161685898401 := by
  unfold tailWord_4213298
  simp only [CollatzResearch.WordTrace]
  refine ⟨38417900672487098713824137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102447735126632263236864365 38417900672487098713824137)
  ·
    refine ⟨28813425504365324035368103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38417900672487098713824137 28813425504365324035368103)
    ·
      refine ⟨43220138256547986053052155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28813425504365324035368103 43220138256547986053052155)
      ·
        refine ⟨64830207384821979079578233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43220138256547986053052155 64830207384821979079578233)
        ·
          refine ⟨48622655538616484309683675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64830207384821979079578233 48622655538616484309683675)
          ·
            refine ⟨72933983307924726464525513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48622655538616484309683675 72933983307924726464525513)
            ·
              refine ⟨54700487480943544848394135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72933983307924726464525513 54700487480943544848394135)
              ·
                refine ⟨82050731221415317272591203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54700487480943544848394135 82050731221415317272591203)
                ·
                  refine ⟨123076096832122975908886805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82050731221415317272591203 123076096832122975908886805)
                  ·
                    refine ⟨5769192039005764495729069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 123076096832122975908886805 5769192039005764495729069)
                    ·
                      refine ⟨2163447014627161685898401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5769192039005764495729069 2163447014627161685898401)
                      ·
                        rfl

theorem cell23_4213298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_4213298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213298 prefixEnd_4213298 := by exact prefixLift 4213298
  have htrace : WordTrace (prefixWord ++ tailWord_4213298) baseStart_4213298 baseEnd_4213298 := by
    simpa [prefixWord, tailWord_4213298, baseEnd_4213298] using wordTrace_append hprefix tailTrace_4213298
  have hstable : (prefixWord ++ tailWord_4213298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213298).length < 2 ^ (prefixWord ++ tailWord_4213298).sum := by decide
  have hdescent : baseEnd_4213298 < baseStart_4213298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213312 : List Nat := [2, 1, 1, 2, 2, 2, 2, 5, 2, 2, 2]
def baseStart_4213312 : Nat := 118140960795 + 4213312 * 2 ^ 59
def prefixEnd_4213312 : Nat := 4983230072969 + 3 ^ 40 * 4213312 * 2
def baseEnd_4213312 : Nat := 2163454203356324631123337

theorem tailTrace_4213312 : CollatzResearch.WordTrace tailWord_4213312 prefixEnd_4213312 2163454203356324631123337 := by
  unfold tailWord_4213312
  simp only [CollatzResearch.WordTrace]
  refine ⟨76836056655948837623153095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102448075541265116830870793 76836056655948837623153095)
  ·
    refine ⟨115254084983923256434729643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76836056655948837623153095 115254084983923256434729643)
    ·
      refine ⟨172881127475884884652094465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115254084983923256434729643 172881127475884884652094465)
      ·
        refine ⟨129660845606913663489070849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172881127475884884652094465 129660845606913663489070849)
        ·
          refine ⟨97245634205185247616803137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129660845606913663489070849 97245634205185247616803137)
          ·
            refine ⟨72934225653888935712602353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97245634205185247616803137 72934225653888935712602353)
            ·
              refine ⟨54700669240416701784451765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72934225653888935712602353 54700669240416701784451765)
              ·
                refine ⟨5128187741289065792292353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54700669240416701784451765 5128187741289065792292353)
                ·
                  refine ⟨3846140805966799344219265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5128187741289065792292353 3846140805966799344219265)
                  ·
                    refine ⟨2884605604475099508164449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3846140805966799344219265 2884605604475099508164449)
                    ·
                      refine ⟨2163454203356324631123337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2884605604475099508164449 2163454203356324631123337)
                      ·
                        rfl

theorem cell23_4213312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 2, 2, 2].length) (baseStart_4213312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213312 prefixEnd_4213312 := by exact prefixLift 4213312
  have htrace : WordTrace (prefixWord ++ tailWord_4213312) baseStart_4213312 baseEnd_4213312 := by
    simpa [prefixWord, tailWord_4213312, baseEnd_4213312] using wordTrace_append hprefix tailTrace_4213312
  have hstable : (prefixWord ++ tailWord_4213312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213312).length < 2 ^ (prefixWord ++ tailWord_4213312).sum := by decide
  have hdescent : baseEnd_4213312 < baseStart_4213312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213328 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 3]
def baseStart_4213328 : Nat := 118140960795 + 4213328 * 2 ^ 59
def prefixEnd_4213328 : Nat := 4983230072969 + 3 ^ 40 * 4213328 * 2
def baseEnd_4213328 : Nat := 2163462419046796568523263

theorem tailTrace_4213328 : CollatzResearch.WordTrace tailWord_4213328 prefixEnd_4213328 2163462419046796568523263 := by
  unfold tailWord_4213328
  simp only [CollatzResearch.WordTrace]
  refine ⟨76836348439919854989444319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102448464586559806652592425 76836348439919854989444319)
  ·
    refine ⟨115254522659879782484166479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76836348439919854989444319 115254522659879782484166479)
    ·
      refine ⟨172881783989819673726249719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115254522659879782484166479 172881783989819673726249719)
      ·
        refine ⟨259322675984729510589374579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172881783989819673726249719 259322675984729510589374579)
        ·
          refine ⟨388984013977094265884061869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259322675984729510589374579 388984013977094265884061869)
          ·
            refine ⟨145869005241410349706523201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 388984013977094265884061869 145869005241410349706523201)
            ·
              refine ⟨109401753931057762279892401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145869005241410349706523201 109401753931057762279892401)
              ·
                refine ⟨82051315448293321709919301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109401753931057762279892401 82051315448293321709919301)
                ·
                  refine ⟨15384621646554997820609869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82051315448293321709919301 15384621646554997820609869)
                  ·
                    refine ⟨5769233117458124182728701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15384621646554997820609869 5769233117458124182728701)
                    ·
                      refine ⟨2163462419046796568523263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5769233117458124182728701 2163462419046796568523263)
                      ·
                        rfl

theorem cell23_4213328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 3].length) (baseStart_4213328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213328 prefixEnd_4213328 := by exact prefixLift 4213328
  have htrace : WordTrace (prefixWord ++ tailWord_4213328) baseStart_4213328 baseEnd_4213328 := by
    simpa [prefixWord, tailWord_4213328, baseEnd_4213328] using wordTrace_append hprefix tailTrace_4213328
  have hstable : (prefixWord ++ tailWord_4213328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213328).length < 2 ^ (prefixWord ++ tailWord_4213328).sum := by decide
  have hdescent : baseEnd_4213328 < baseStart_4213328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213352 : List Nat := [2, 1, 4, 3, 2, 2, 1, 1, 7]
def baseStart_4213352 : Nat := 118140960795 + 4213352 * 2 ^ 59
def prefixEnd_4213352 : Nat := 4983230072969 + 3 ^ 40 * 4213352 * 2
def baseEnd_4213352 : Nat := 240386082509167163847017

theorem tailTrace_4213352 : CollatzResearch.WordTrace tailWord_4213352 prefixEnd_4213352 240386082509167163847017 := by
  unfold tailWord_4213352
  simp only [CollatzResearch.WordTrace]
  refine ⟨76836786115876381038881155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102449048154501841385174873 76836786115876381038881155)
  ·
    refine ⟨115255179173814571558321733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76836786115876381038881155 115255179173814571558321733)
    ·
      refine ⟨21610346095090232167185325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115255179173814571558321733 21610346095090232167185325)
      ·
        refine ⟨8103879785658837062694497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21610346095090232167185325 8103879785658837062694497)
        ·
          refine ⟨6077909839244127797020873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8103879785658837062694497 6077909839244127797020873)
          ·
            refine ⟨4558432379433095847765655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6077909839244127797020873 4558432379433095847765655)
            ·
              refine ⟨6837648569149643771648483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4558432379433095847765655 6837648569149643771648483)
              ·
                refine ⟨10256472853724465657472725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6837648569149643771648483 10256472853724465657472725)
                ·
                  refine ⟨240386082509167163847017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10256472853724465657472725 240386082509167163847017)
                  ·
                    rfl

theorem cell23_4213352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 7].length) (baseStart_4213352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213352 prefixEnd_4213352 := by exact prefixLift 4213352
  have htrace : WordTrace (prefixWord ++ tailWord_4213352) baseStart_4213352 baseEnd_4213352 := by
    simpa [prefixWord, tailWord_4213352, baseEnd_4213352] using wordTrace_append hprefix tailTrace_4213352
  have hstable : (prefixWord ++ tailWord_4213352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213352).length < 2 ^ (prefixWord ++ tailWord_4213352).sum := by decide
  have hdescent : baseEnd_4213352 < baseStart_4213352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213385 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 4, 4, 2]
def baseStart_4213385 : Nat := 118140960795 + 4213385 * 2 ^ 59
def prefixEnd_4213385 : Nat := 4983230072969 + 3 ^ 40 * 4213385 * 2
def baseEnd_4213385 : Nat := 2163491687444102845510501

theorem tailTrace_4213385 : CollatzResearch.WordTrace tailWord_4213385 prefixEnd_4213385 2163491687444102845510501 := by
  unfold tailWord_4213385
  simp only [CollatzResearch.WordTrace]
  refine ⟨153674775840633208713713609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102449850560422139142475739 153674775840633208713713609)
  ·
    refine ⟨115256081880474906535285207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153674775840633208713713609 115256081880474906535285207)
    ·
      refine ⟨172884122820712359802927811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115256081880474906535285207 172884122820712359802927811)
      ·
        refine ⟨259326184231068539704391717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172884122820712359802927811 259326184231068539704391717)
        ·
          refine ⟨48623659543325351194573447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 259326184231068539704391717 48623659543325351194573447)
          ·
            refine ⟨72935489314988026791860171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48623659543325351194573447 72935489314988026791860171)
            ·
              refine ⟨109403233972482040187790257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72935489314988026791860171 109403233972482040187790257)
              ·
                refine ⟨82052425479361530140842693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109403233972482040187790257 82052425479361530140842693)
                ·
                  refine ⟨15384829777380286901408005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82052425479361530140842693 15384829777380286901408005)
                  ·
                    refine ⟨2884655583258803794014001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15384829777380286901408005 2884655583258803794014001)
                    ·
                      refine ⟨2163491687444102845510501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2884655583258803794014001 2163491687444102845510501)
                      ·
                        rfl

theorem cell23_4213385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 4, 2].length) (baseStart_4213385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213385 prefixEnd_4213385 := by exact prefixLift 4213385
  have htrace : WordTrace (prefixWord ++ tailWord_4213385) baseStart_4213385 baseEnd_4213385 := by
    simpa [prefixWord, tailWord_4213385, baseEnd_4213385] using wordTrace_append hprefix tailTrace_4213385
  have hstable : (prefixWord ++ tailWord_4213385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213385).length < 2 ^ (prefixWord ++ tailWord_4213385).sum := by decide
  have hdescent : baseEnd_4213385 < baseStart_4213385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213505 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_4213505 : Nat := 118140960795 + 4213505 * 2 ^ 59
def prefixEnd_4213505 : Nat := 4983230072969 + 3 ^ 40 * 4213505 * 2
def baseEnd_4213505 : Nat := 2163553305122642376009949

theorem tailTrace_4213505 : CollatzResearch.WordTrace tailWord_4213505 prefixEnd_4213505 2163553305122642376009949 := by
  unfold tailWord_4213505
  simp only [CollatzResearch.WordTrace]
  refine ⟨153679152600198469208081969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102452768400132312805387979 153679152600198469208081969)
  ·
    refine ⟨115259364450148851906061477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153679152600198469208081969 115259364450148851906061477)
    ·
      refine ⟨21611130834402909732386527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115259364450148851906061477 21611130834402909732386527)
      ·
        refine ⟨32416696251604364598579791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21611130834402909732386527 32416696251604364598579791)
        ·
          refine ⟨48625044377406546897869687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32416696251604364598579791 48625044377406546897869687)
          ·
            refine ⟨72937566566109820346804531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48625044377406546897869687 72937566566109820346804531)
            ·
              refine ⟨109406349849164730520206797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72937566566109820346804531 109406349849164730520206797)
              ·
                refine ⟨41027381193436773945077549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109406349849164730520206797 41027381193436773945077549)
                ·
                  refine ⟨15385267947538790229404081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41027381193436773945077549 15385267947538790229404081)
                  ·
                    refine ⟨11538950960654092672053061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15385267947538790229404081 11538950960654092672053061)
                    ·
                      refine ⟨2163553305122642376009949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11538950960654092672053061 2163553305122642376009949)
                      ·
                        rfl

theorem cell23_4213505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_4213505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213505 prefixEnd_4213505 := by exact prefixLift 4213505
  have htrace : WordTrace (prefixWord ++ tailWord_4213505) baseStart_4213505 baseEnd_4213505 := by
    simpa [prefixWord, tailWord_4213505, baseEnd_4213505] using wordTrace_append hprefix tailTrace_4213505
  have hstable : (prefixWord ++ tailWord_4213505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213505).length < 2 ^ (prefixWord ++ tailWord_4213505).sum := by decide
  have hdescent : baseEnd_4213505 < baseStart_4213505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213512 : List Nat := [2, 1, 3, 2, 2, 3, 2, 1, 1, 1, 5]
def baseStart_4213512 : Nat := 118140960795 + 4213512 * 2 ^ 59
def prefixEnd_4213512 : Nat := 4983230072969 + 3 ^ 40 * 4213512 * 2
def baseEnd_4213512 : Nat := 2163556899487223848622417

theorem tailTrace_4213512 : CollatzResearch.WordTrace tailWord_4213512 prefixEnd_4213512 2163556899487223848622417 := by
  unfold tailWord_4213512
  simp only [CollatzResearch.WordTrace]
  refine ⟨76839703955586554701793395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102452938607448739602391193 76839703955586554701793395)
  ·
    refine ⟨115259555933379832052690093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76839703955586554701793395 115259555933379832052690093)
    ·
      refine ⟨43222333475017437019758785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115259555933379832052690093 43222333475017437019758785)
      ·
        refine ⟨32416750106263077764819089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43222333475017437019758785 32416750106263077764819089)
        ·
          refine ⟨24312562579697308323614317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32416750106263077764819089 24312562579697308323614317)
          ·
            refine ⟨9117210967386490621355369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24312562579697308323614317 9117210967386490621355369)
            ·
              refine ⟨6837908225539867966016527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9117210967386490621355369 6837908225539867966016527)
              ·
                refine ⟨10256862338309801949024791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6837908225539867966016527 10256862338309801949024791)
                ·
                  refine ⟨15385293507464702923537187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10256862338309801949024791 15385293507464702923537187)
                  ·
                    refine ⟨23077940261197054385305781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15385293507464702923537187 23077940261197054385305781)
                    ·
                      refine ⟨2163556899487223848622417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23077940261197054385305781 2163556899487223848622417)
                      ·
                        rfl

theorem cell23_4213512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_4213512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213512 prefixEnd_4213512 := by exact prefixLift 4213512
  have htrace : WordTrace (prefixWord ++ tailWord_4213512) baseStart_4213512 baseEnd_4213512 := by
    simpa [prefixWord, tailWord_4213512, baseEnd_4213512] using wordTrace_append hprefix tailTrace_4213512
  have hstable : (prefixWord ++ tailWord_4213512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213512).length < 2 ^ (prefixWord ++ tailWord_4213512).sum := by decide
  have hdescent : baseEnd_4213512 < baseStart_4213512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213536 : List Nat := [2, 1, 1, 5, 1, 4, 2, 1, 2, 4]
def baseStart_4213536 : Nat := 118140960795 + 4213536 * 2 ^ 59
def prefixEnd_4213536 : Nat := 4983230072969 + 3 ^ 40 * 4213536 * 2
def baseEnd_4213536 : Nat := 721189741007643918240769

theorem tailTrace_4213536 : CollatzResearch.WordTrace tailWord_4213536 prefixEnd_4213536 721189741007643918240769 := by
  unfold tailWord_4213536
  simp only [CollatzResearch.WordTrace]
  refine ⟨76840141631543080751230231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102453522175390774334973641 76840141631543080751230231)
  ·
    refine ⟨115260212447314621126845347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76840141631543080751230231 115260212447314621126845347)
    ·
      refine ⟨172890318670971931690268021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115260212447314621126845347 172890318670971931690268021)
      ·
        refine ⟨16208467375403618595962627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 172890318670971931690268021 16208467375403618595962627)
        ·
          refine ⟨24312701063105427893943941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16208467375403618595962627 24312701063105427893943941)
          ·
            refine ⟨4558631449332267730114489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24312701063105427893943941 4558631449332267730114489)
            ·
              refine ⟨3418973586999200797585867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4558631449332267730114489 3418973586999200797585867)
              ·
                refine ⟨5128460380498801196378801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3418973586999200797585867 5128460380498801196378801)
                ·
                  refine ⟨3846345285374100897284101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5128460380498801196378801 3846345285374100897284101)
                  ·
                    refine ⟨721189741007643918240769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3846345285374100897284101 721189741007643918240769)
                    ·
                      rfl

theorem cell23_4213536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 2, 4].length) (baseStart_4213536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213536 prefixEnd_4213536 := by exact prefixLift 4213536
  have htrace : WordTrace (prefixWord ++ tailWord_4213536) baseStart_4213536 baseEnd_4213536 := by
    simpa [prefixWord, tailWord_4213536, baseEnd_4213536] using wordTrace_append hprefix tailTrace_4213536
  have hstable : (prefixWord ++ tailWord_4213536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213536).length < 2 ^ (prefixWord ++ tailWord_4213536).sum := by decide
  have hdescent : baseEnd_4213536 < baseStart_4213536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213546 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_4213546 : Nat := 118140960795 + 4213546 * 2 ^ 59
def prefixEnd_4213546 : Nat := 4983230072969 + 3 ^ 40 * 4213546 * 2
def baseEnd_4213546 : Nat := 2163574357829476715597261

theorem tailTrace_4213546 : CollatzResearch.WordTrace tailWord_4213546 prefixEnd_4213546 2163574357829476715597261 := by
  unfold tailWord_4213546
  simp only [CollatzResearch.WordTrace]
  refine ⟨38420161998262483302581123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102453765328699955473549661 38420161998262483302581123)
  ·
    refine ⟨57630242997393724953871685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38420161998262483302581123 57630242997393724953871685)
    ·
      refine ⟨10805670562011323428850941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57630242997393724953871685 10805670562011323428850941)
      ·
        refine ⟨4052126460754246285819103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10805670562011323428850941 4052126460754246285819103)
        ·
          refine ⟨6078189691131369428728655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4052126460754246285819103 6078189691131369428728655)
          ·
            refine ⟨9117284536697054143092983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6078189691131369428728655 9117284536697054143092983)
            ·
              refine ⟨13675926805045581214639475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9117284536697054143092983 13675926805045581214639475)
              ·
                refine ⟨20513890207568371821959213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13675926805045581214639475 20513890207568371821959213)
                ·
                  refine ⟨7692708827838139433234705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20513890207568371821959213 7692708827838139433234705)
                  ·
                    refine ⟨5769531620878604574926029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7692708827838139433234705 5769531620878604574926029)
                    ·
                      refine ⟨2163574357829476715597261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5769531620878604574926029 2163574357829476715597261)
                      ·
                        rfl

theorem cell23_4213546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_4213546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213546 prefixEnd_4213546 := by exact prefixLift 4213546
  have htrace : WordTrace (prefixWord ++ tailWord_4213546) baseStart_4213546 baseEnd_4213546 := by
    simpa [prefixWord, tailWord_4213546, baseEnd_4213546] using wordTrace_append hprefix tailTrace_4213546
  have hstable : (prefixWord ++ tailWord_4213546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213546).length < 2 ^ (prefixWord ++ tailWord_4213546).sum := by decide
  have hdescent : baseEnd_4213546 < baseStart_4213546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213575 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 2, 6]
def baseStart_4213575 : Nat := 118140960795 + 4213575 * 2 ^ 59
def prefixEnd_4213575 : Nat := 4983230072969 + 3 ^ 40 * 4213575 * 2
def baseEnd_4213575 : Nat := 721196416256152367378209

theorem tailTrace_4213575 : CollatzResearch.WordTrace tailWord_4213575 prefixEnd_4213575 721196416256152367378209 := by
  unfold tailWord_4213575
  simp only [CollatzResearch.WordTrace]
  refine ⟨153681705709944871163130179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102454470473296580775420119 153681705709944871163130179)
  ·
    refine ⟨230522558564917306744695269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153681705709944871163130179 230522558564917306744695269)
    ·
      refine ⟨43222979730921995014630363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230522558564917306744695269 43222979730921995014630363)
      ·
        refine ⟨64834469596382992521945545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43222979730921995014630363 64834469596382992521945545)
        ·
          refine ⟨48625852197287244391459159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64834469596382992521945545 48625852197287244391459159)
          ·
            refine ⟨72938778295930866587188739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48625852197287244391459159 72938778295930866587188739)
            ·
              refine ⟨109408167443896299880783109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72938778295930866587188739 109408167443896299880783109)
              ·
                refine ⟨20514031395730556227646833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 109408167443896299880783109 20514031395730556227646833)
                ·
                  refine ⟨15385523546797917170735125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20514031395730556227646833 15385523546797917170735125)
                  ·
                    refine ⟨721196416256152367378209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15385523546797917170735125 721196416256152367378209)
                    ·
                      rfl

theorem cell23_4213575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_4213575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213575 prefixEnd_4213575 := by exact prefixLift 4213575
  have htrace : WordTrace (prefixWord ++ tailWord_4213575) baseStart_4213575 baseEnd_4213575 := by
    simpa [prefixWord, tailWord_4213575, baseEnd_4213575] using wordTrace_append hprefix tailTrace_4213575
  have hstable : (prefixWord ++ tailWord_4213575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213575).length < 2 ^ (prefixWord ++ tailWord_4213575).sum := by decide
  have hdescent : baseEnd_4213575 < baseStart_4213575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213599 : List Nat := [1, 1, 2, 3, 1, 3, 4, 1, 1, 4, 2]
def baseStart_4213599 : Nat := 118140960795 + 4213599 * 2 ^ 59
def prefixEnd_4213599 : Nat := 4983230072969 + 3 ^ 40 * 4213599 * 2
def baseEnd_4213599 : Nat := 2163601572304165008234517

theorem tailTrace_4213599 : CollatzResearch.WordTrace tailWord_4213599 prefixEnd_4213599 2163601572304165008234517 := by
  unfold tailWord_4213599
  simp only [CollatzResearch.WordTrace]
  refine ⟨153682581061857923262003851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102455054041238615508002567 153682581061857923262003851)
  ·
    refine ⟨230523871592786884893005777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153682581061857923262003851 230523871592786884893005777)
    ·
      refine ⟨172892903694590163669754333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230523871592786884893005777 172892903694590163669754333)
      ·
        refine ⟨64834838885471311376157875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172892903694590163669754333 64834838885471311376157875)
        ·
          refine ⟨97252258328206967064236813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64834838885471311376157875 97252258328206967064236813)
          ·
            refine ⟨36469596873077612649088805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 97252258328206967064236813 36469596873077612649088805)
            ·
              refine ⟨6838049413702052371704151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36469596873077612649088805 6838049413702052371704151)
              ·
                refine ⟨10257074120553078557556227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6838049413702052371704151 10257074120553078557556227)
                ·
                  refine ⟨15385611180829617836334341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10257074120553078557556227 15385611180829617836334341)
                  ·
                    refine ⟨2884802096405553344312689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15385611180829617836334341 2884802096405553344312689)
                    ·
                      refine ⟨2163601572304165008234517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2884802096405553344312689 2163601572304165008234517)
                      ·
                        rfl

theorem cell23_4213599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_4213599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213599 prefixEnd_4213599 := by exact prefixLift 4213599
  have htrace : WordTrace (prefixWord ++ tailWord_4213599) baseStart_4213599 baseEnd_4213599 := by
    simpa [prefixWord, tailWord_4213599, baseEnd_4213599] using wordTrace_append hprefix tailTrace_4213599
  have hstable : (prefixWord ++ tailWord_4213599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213599).length < 2 ^ (prefixWord ++ tailWord_4213599).sum := by decide
  have hdescent : baseEnd_4213599 < baseStart_4213599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213605 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 9]
def baseStart_4213605 : Nat := 118140960795 + 4213605 * 2 ^ 59
def prefixEnd_4213605 : Nat := 4983230072969 + 3 ^ 40 * 4213605 * 2
def baseEnd_4213605 : Nat := 240400517020899109417721

theorem tailTrace_4213605 : CollatzResearch.WordTrace tailWord_4213605 prefixEnd_4213605 240400517020899109417721 := by
  unfold tailWord_4213605
  simp only [CollatzResearch.WordTrace]
  refine ⟨153682799899836186286722269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102455199933224124191148179 153682799899836186286722269)
  ·
    refine ⟨57631049962438569857520851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153682799899836186286722269 57631049962438569857520851)
    ·
      refine ⟨86446574943657854786281277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57631049962438569857520851 86446574943657854786281277)
      ·
        refine ⟨32417465603871695544855479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86446574943657854786281277 32417465603871695544855479)
        ·
          refine ⟨48626198405807543317283219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32417465603871695544855479 48626198405807543317283219)
          ·
            refine ⟨72939297608711314975924829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48626198405807543317283219 72939297608711314975924829)
            ·
              refine ⟨27352236603266743115971811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72939297608711314975924829 27352236603266743115971811)
              ·
                refine ⟨41028354904900114673957717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27352236603266743115971811 41028354904900114673957717)
                ·
                  refine ⟨240400517020899109417721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41028354904900114673957717 240400517020899109417721)
                  ·
                    rfl

theorem cell23_4213605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 9].length) (baseStart_4213605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213605 prefixEnd_4213605 := by exact prefixLift 4213605
  have htrace : WordTrace (prefixWord ++ tailWord_4213605) baseStart_4213605 baseEnd_4213605 := by
    simpa [prefixWord, tailWord_4213605, baseEnd_4213605] using wordTrace_append hprefix tailTrace_4213605
  have hstable : (prefixWord ++ tailWord_4213605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213605).length < 2 ^ (prefixWord ++ tailWord_4213605).sum := by decide
  have hdescent : baseEnd_4213605 < baseStart_4213605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213639 : List Nat := [1, 1, 4, 2, 3, 1, 2, 4, 5]
def baseStart_4213639 : Nat := 118140960795 + 4213639 * 2 ^ 59
def prefixEnd_4213639 : Nat := 4983230072969 + 3 ^ 40 * 4213639 * 2
def baseEnd_4213639 : Nat := 240402456836704983526037

theorem tailTrace_4213639 : CollatzResearch.WordTrace tailWord_4213639 prefixEnd_4213639 240402456836704983526037 := by
  unfold tailWord_4213639
  simp only [CollatzResearch.WordTrace]
  refine ⟨153684039981713010093459971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102456026654475340062306647 153684039981713010093459971)
  ·
    refine ⟨230526059972569515140189957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153684039981713010093459971 230526059972569515140189957)
    ·
      refine ⟨43223636244856784088785617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230526059972569515140189957 43223636244856784088785617)
      ·
        refine ⟨32417727183642588066589213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43223636244856784088785617 32417727183642588066589213)
        ·
          refine ⟨12156647693865970524970955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32417727183642588066589213 12156647693865970524970955)
          ·
            refine ⟨18234971540798955787456433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12156647693865970524970955 18234971540798955787456433)
            ·
              refine ⟨13676228655599216840592325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18234971540798955787456433 13676228655599216840592325)
              ·
                refine ⟨2564292872924853157611061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13676228655599216840592325 2564292872924853157611061)
                ·
                  refine ⟨240402456836704983526037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2564292872924853157611061 240402456836704983526037)
                  ·
                    rfl

theorem cell23_4213639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 5].length) (baseStart_4213639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213639 prefixEnd_4213639 := by exact prefixLift 4213639
  have htrace : WordTrace (prefixWord ++ tailWord_4213639) baseStart_4213639 baseEnd_4213639 := by
    simpa [prefixWord, tailWord_4213639, baseEnd_4213639] using wordTrace_append hprefix tailTrace_4213639
  have hstable : (prefixWord ++ tailWord_4213639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213639).length < 2 ^ (prefixWord ++ tailWord_4213639).sum := by decide
  have hdescent : baseEnd_4213639 < baseStart_4213639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213650 : List Nat := [3, 2, 3, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_4213650 : Nat := 118140960795 + 4213650 * 2 ^ 59
def prefixEnd_4213650 : Nat := 4983230072969 + 3 ^ 40 * 4213650 * 2
def baseEnd_4213650 : Nat := 2163627759817544308696783

theorem tailTrace_4213650 : CollatzResearch.WordTrace tailWord_4213650 prefixEnd_4213650 2163627759817544308696783 := by
  unfold tailWord_4213650
  simp only [CollatzResearch.WordTrace]
  refine ⟨38421110296168289743027601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102456294123115439314740269 38421110296168289743027601)
  ·
    refine ⟨28815832722126217307270701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38421110296168289743027601 28815832722126217307270701)
    ·
      refine ⟨10805937270797331490226513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28815832722126217307270701 10805937270797331490226513)
      ·
        refine ⟨8104452953097998617669885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10805937270797331490226513 8104452953097998617669885)
        ·
          refine ⟨3039169857411749481626207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8104452953097998617669885 3039169857411749481626207)
          ·
            refine ⟨4558754786117624222439311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3039169857411749481626207 4558754786117624222439311)
            ·
              refine ⟨6838132179176436333658967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4558754786117624222439311 6838132179176436333658967)
              ·
                refine ⟨10257198268764654500488451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6838132179176436333658967 10257198268764654500488451)
                ·
                  refine ⟨15385797403146981750732677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10257198268764654500488451 15385797403146981750732677)
                  ·
                    refine ⟨2884837013090059078262377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15385797403146981750732677 2884837013090059078262377)
                    ·
                      refine ⟨2163627759817544308696783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2884837013090059078262377 2163627759817544308696783)
                      ·
                        rfl

theorem cell23_4213650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_4213650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213650 prefixEnd_4213650 := by exact prefixLift 4213650
  have htrace : WordTrace (prefixWord ++ tailWord_4213650) baseStart_4213650 baseEnd_4213650 := by
    simpa [prefixWord, tailWord_4213650, baseEnd_4213650] using wordTrace_append hprefix tailTrace_4213650
  have hstable : (prefixWord ++ tailWord_4213650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213650).length < 2 ^ (prefixWord ++ tailWord_4213650).sum := by decide
  have hdescent : baseEnd_4213650 < baseStart_4213650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213652 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_4213652 : Nat := 118140960795 + 4213652 * 2 ^ 59
def prefixEnd_4213652 : Nat := 4983230072969 + 3 ^ 40 * 4213652 * 2
def baseEnd_4213652 : Nat := 721209595592951100290591

theorem tailTrace_4213652 : CollatzResearch.WordTrace tailWord_4213652 prefixEnd_4213652 721209595592951100290591 := by
  unfold tailWord_4213652
  simp only [CollatzResearch.WordTrace]
  refine ⟨76842257065332956656841605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102456342753777275542455473 76842257065332956656841605)
  ·
    refine ⟨14407923199749929373157801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76842257065332956656841605 14407923199749929373157801)
    ·
      refine ⟨10805942399812447029868351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14407923199749929373157801 10805942399812447029868351)
      ·
        refine ⟨16208913599718670544802527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10805942399812447029868351 16208913599718670544802527)
        ·
          refine ⟨24313370399578005817203791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16208913599718670544802527 24313370399578005817203791)
          ·
            refine ⟨36470055599367008725805687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24313370399578005817203791 36470055599367008725805687)
            ·
              refine ⟨54705083399050513088708531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36470055599367008725805687 54705083399050513088708531)
              ·
                refine ⟨82057625098575769633062797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54705083399050513088708531 82057625098575769633062797)
                ·
                  refine ⟨30771609411965913612398549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82057625098575769633062797 30771609411965913612398549)
                  ·
                    refine ⟨721209595592951100290591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30771609411965913612398549 721209595592951100290591)
                    ·
                      rfl

theorem cell23_4213652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_4213652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213652 prefixEnd_4213652 := by exact prefixLift 4213652
  have htrace : WordTrace (prefixWord ++ tailWord_4213652) baseStart_4213652 baseEnd_4213652 := by
    simpa [prefixWord, tailWord_4213652, baseEnd_4213652] using wordTrace_append hprefix tailTrace_4213652
  have hstable : (prefixWord ++ tailWord_4213652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213652).length < 2 ^ (prefixWord ++ tailWord_4213652).sum := by decide
  have hdescent : baseEnd_4213652 < baseStart_4213652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213689 : List Nat := [1, 2, 1, 4, 2, 3, 1, 2, 2, 1, 4]
def baseStart_4213689 : Nat := 118140960795 + 4213689 * 2 ^ 59
def prefixEnd_4213689 : Nat := 4983230072969 + 3 ^ 40 * 4213689 * 2
def baseEnd_4213689 : Nat := 2163647785563069656109103

theorem tailTrace_4213689 : CollatzResearch.WordTrace tailWord_4213689 prefixEnd_4213689 2163647785563069656109103 := by
  unfold tailWord_4213689
  simp only [CollatzResearch.WordTrace]
  refine ⟨153685863631531868632780121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102457242421021245755186747 153685863631531868632780121)
  ·
    refine ⟨115264397723648901474585091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153685863631531868632780121 115264397723648901474585091)
    ·
      refine ⟨172896596585473352211877637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115264397723648901474585091 172896596585473352211877637)
      ·
        refine ⟨32418111859776253539727057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172896596585473352211877637 32418111859776253539727057)
        ·
          refine ⟨24313583894832190154795293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32418111859776253539727057 24313583894832190154795293)
          ·
            refine ⟨9117593960562071308048235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24313583894832190154795293 9117593960562071308048235)
            ·
              refine ⟨13676390940843106962072353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9117593960562071308048235 13676390940843106962072353)
              ·
                refine ⟨10257293205632330221554265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13676390940843106962072353 10257293205632330221554265)
                ·
                  refine ⟨7692969904224247666165699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10257293205632330221554265 7692969904224247666165699)
                  ·
                    refine ⟨11539454856336371499248549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7692969904224247666165699 11539454856336371499248549)
                    ·
                      refine ⟨2163647785563069656109103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11539454856336371499248549 2163647785563069656109103)
                      ·
                        rfl

theorem cell23_4213689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_4213689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213689 prefixEnd_4213689 := by exact prefixLift 4213689
  have htrace : WordTrace (prefixWord ++ tailWord_4213689) baseStart_4213689 baseEnd_4213689 := by
    simpa [prefixWord, tailWord_4213689, baseEnd_4213689] using wordTrace_append hprefix tailTrace_4213689
  have hstable : (prefixWord ++ tailWord_4213689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213689).length < 2 ^ (prefixWord ++ tailWord_4213689).sum := by decide
  have hdescent : baseEnd_4213689 < baseStart_4213689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213750 : List Nat := [5, 1, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_4213750 : Nat := 118140960795 + 4213750 * 2 ^ 59
def prefixEnd_4213750 : Nat := 4983230072969 + 3 ^ 40 * 4213750 * 2
def baseEnd_4213750 : Nat := 721226369294331305815441

theorem tailTrace_4213750 : CollatzResearch.WordTrace tailWord_4213750 prefixEnd_4213750 721226369294331305815441 := by
  unfold tailWord_4213750
  simp only [CollatzResearch.WordTrace]
  refine ⟨9605505530269429753171919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102458725656207250700500469 9605505530269429753171919)
  ·
    refine ⟨14408258295404144629757879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9605505530269429753171919 14408258295404144629757879)
    ·
      refine ⟨21612387443106216944636819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14408258295404144629757879 21612387443106216944636819)
      ·
        refine ⟨32418581164659325416955229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21612387443106216944636819 32418581164659325416955229)
        ·
          refine ⟨12156967936747247031358211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32418581164659325416955229 12156967936747247031358211)
          ·
            refine ⟨18235451905120870547037317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12156967936747247031358211 18235451905120870547037317)
            ·
              refine ⟨3419147232210163227569497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18235451905120870547037317 3419147232210163227569497)
              ·
                refine ⟨2564360424157622420677123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3419147232210163227569497 2564360424157622420677123)
                ·
                  refine ⟨3846540636236433631015685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2564360424157622420677123 3846540636236433631015685)
                  ·
                    refine ⟨721226369294331305815441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3846540636236433631015685 721226369294331305815441)
                    ·
                      rfl

theorem cell23_4213750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_4213750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213750 prefixEnd_4213750 := by exact prefixLift 4213750
  have htrace : WordTrace (prefixWord ++ tailWord_4213750) baseStart_4213750 baseEnd_4213750 := by
    simpa [prefixWord, tailWord_4213750, baseEnd_4213750] using wordTrace_append hprefix tailTrace_4213750
  have hstable : (prefixWord ++ tailWord_4213750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213750).length < 2 ^ (prefixWord ++ tailWord_4213750).sum := by decide
  have hdescent : baseEnd_4213750 < baseStart_4213750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213779 : List Nat := [1, 1, 1, 2, 1, 4, 1, 6, 1, 1, 4]
def baseStart_4213779 : Nat := 118140960795 + 4213779 * 2 ^ 59
def prefixEnd_4213779 : Nat := 4983230072969 + 3 ^ 40 * 4213779 * 2
def baseEnd_4213779 : Nat := 2163693998821974303983689

theorem tailTrace_4213779 : CollatzResearch.WordTrace tailWord_4213779 prefixEnd_4213779 2163693998821974303983689 := by
  unfold tailWord_4213779
  simp only [CollatzResearch.WordTrace]
  refine ⟨153689146201205814003556391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102459430800803876002370927 153689146201205814003556391)
  ·
    refine ⟨230533719301808721005334587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153689146201205814003556391 230533719301808721005334587)
    ·
      refine ⟨345800578952713081508001881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230533719301808721005334587 345800578952713081508001881)
      ·
        refine ⟨259350434214534811131001411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345800578952713081508001881 259350434214534811131001411)
        ·
          refine ⟨389025651321802216696502117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259350434214534811131001411 389025651321802216696502117)
          ·
            refine ⟨72942309622837915630594147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 389025651321802216696502117 72942309622837915630594147)
            ·
              refine ⟨109413464434256873445891221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72942309622837915630594147 109413464434256873445891221)
              ·
                refine ⟨5128756145355790942776151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 109413464434256873445891221 5128756145355790942776151)
                ·
                  refine ⟨7693134218033686414164227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5128756145355790942776151 7693134218033686414164227)
                  ·
                    refine ⟨11539701327050529621246341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7693134218033686414164227 11539701327050529621246341)
                    ·
                      refine ⟨2163693998821974303983689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11539701327050529621246341 2163693998821974303983689)
                      ·
                        rfl

theorem cell23_4213779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 6, 1, 1, 4].length) (baseStart_4213779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213779 prefixEnd_4213779 := by exact prefixLift 4213779
  have htrace : WordTrace (prefixWord ++ tailWord_4213779) baseStart_4213779 baseEnd_4213779 := by
    simpa [prefixWord, tailWord_4213779, baseEnd_4213779] using wordTrace_append hprefix tailTrace_4213779
  have hstable : (prefixWord ++ tailWord_4213779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213779).length < 2 ^ (prefixWord ++ tailWord_4213779).sum := by decide
  have hdescent : baseEnd_4213779 < baseStart_4213779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213783 : List Nat := [1, 1, 3, 5, 1, 1, 3, 1, 2, 3, 2]
def baseStart_4213783 : Nat := 118140960795 + 4213783 * 2 ^ 59
def prefixEnd_4213783 : Nat := 4983230072969 + 3 ^ 40 * 4213783 * 2
def baseEnd_4213783 : Nat := 2163696052744592288333671

theorem tailTrace_4213783 : CollatzResearch.WordTrace tailWord_4213783 prefixEnd_4213783 2163696052744592288333671 := by
  unfold tailWord_4213783
  simp only [CollatzResearch.WordTrace]
  refine ⟨153689292093191322686702003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102459528062127548457801335 153689292093191322686702003)
  ·
    refine ⟨230533938139786984030053005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153689292093191322686702003 230533938139786984030053005)
    ·
      refine ⟨86450226802420119011269877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230533938139786984030053005 86450226802420119011269877)
      ·
        refine ⟨8104708762726886157306551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86450226802420119011269877 8104708762726886157306551)
        ·
          refine ⟨12157063144090329235959827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8104708762726886157306551 12157063144090329235959827)
          ·
            refine ⟨18235594716135493853939741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12157063144090329235959827 18235594716135493853939741)
            ·
              refine ⟨6838348018550810195227403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18235594716135493853939741 6838348018550810195227403)
              ·
                refine ⟨10257522027826215292841105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6838348018550810195227403 10257522027826215292841105)
                ·
                  refine ⟨7693141520869661469630829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10257522027826215292841105 7693141520869661469630829)
                  ·
                    refine ⟨2884928070326123051111561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7693141520869661469630829 2884928070326123051111561)
                    ·
                      refine ⟨2163696052744592288333671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2884928070326123051111561 2163696052744592288333671)
                      ·
                        rfl

theorem cell23_4213783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_4213783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213783 prefixEnd_4213783 := by exact prefixLift 4213783
  have htrace : WordTrace (prefixWord ++ tailWord_4213783) baseStart_4213783 baseEnd_4213783 := by
    simpa [prefixWord, tailWord_4213783, baseEnd_4213783] using wordTrace_append hprefix tailTrace_4213783
  have hstable : (prefixWord ++ tailWord_4213783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213783).length < 2 ^ (prefixWord ++ tailWord_4213783).sum := by decide
  have hdescent : baseEnd_4213783 < baseStart_4213783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213793 : List Nat := [1, 2, 3, 2, 3, 3, 2, 1, 1, 5]
def baseStart_4213793 : Nat := 118140960795 + 4213793 * 2 ^ 59
def prefixEnd_4213793 : Nat := 4983230072969 + 3 ^ 40 * 4213793 * 2
def baseEnd_4213793 : Nat := 721233729183712416402875

theorem tailTrace_4213793 : CollatzResearch.WordTrace tailWord_4213793 prefixEnd_4213793 721233729183712416402875 := by
  unfold tailWord_4213793
  simp only [CollatzResearch.WordTrace]
  refine ⟨153689656823155094394566033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102459771215436729596377355 153689656823155094394566033)
  ·
    refine ⟨115267242617366320795924525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153689656823155094394566033 115267242617366320795924525)
    ·
      refine ⟨43225215981512370298471697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115267242617366320795924525 43225215981512370298471697)
      ·
        refine ⟨32418911986134277723853773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43225215981512370298471697 32418911986134277723853773)
        ·
          refine ⟨12157091994800354146445165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32418911986134277723853773 12157091994800354146445165)
          ·
            refine ⟨4558909498050132804916937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12157091994800354146445165 4558909498050132804916937)
            ·
              refine ⟨3419182123537599603687703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4558909498050132804916937 3419182123537599603687703)
              ·
                refine ⟨5128773185306399405531555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3419182123537599603687703 5128773185306399405531555)
                ·
                  refine ⟨7693159777959599108297333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5128773185306399405531555 7693159777959599108297333)
                  ·
                    refine ⟨721233729183712416402875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7693159777959599108297333 721233729183712416402875)
                    ·
                      rfl

theorem cell23_4213793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_4213793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213793 prefixEnd_4213793 := by exact prefixLift 4213793
  have htrace : WordTrace (prefixWord ++ tailWord_4213793) baseStart_4213793 baseEnd_4213793 := by
    simpa [prefixWord, tailWord_4213793, baseEnd_4213793] using wordTrace_append hprefix tailTrace_4213793
  have hstable : (prefixWord ++ tailWord_4213793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213793).length < 2 ^ (prefixWord ++ tailWord_4213793).sum := by decide
  have hdescent : baseEnd_4213793 < baseStart_4213793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213806 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 4, 4]
def baseStart_4213806 : Nat := 118140960795 + 4213806 * 2 ^ 59
def prefixEnd_4213806 : Nat := 4983230072969 + 3 ^ 40 * 4213806 * 2
def baseEnd_4213806 : Nat := 721235954266548566115355

theorem tailTrace_4213806 : CollatzResearch.WordTrace tailWord_4213806 prefixEnd_4213806 721235954266548566115355 := by
  unfold tailWord_4213806
  simp only [CollatzResearch.WordTrace]
  refine ⟨19211266371513499701848659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102460087314738665076526181 19211266371513499701848659)
  ·
    refine ⟨28816899557270249552772989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19211266371513499701848659 28816899557270249552772989)
    ·
      refine ⟨10806337333976343582289871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28816899557270249552772989 10806337333976343582289871)
      ·
        refine ⟨16209506000964515373434807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10806337333976343582289871 16209506000964515373434807)
        ·
          refine ⟨24314259001446773060152211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16209506000964515373434807 24314259001446773060152211)
          ·
            refine ⟨36471388502170159590228317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24314259001446773060152211 36471388502170159590228317)
            ·
              refine ⟨13676770688313809846335619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36471388502170159590228317 13676770688313809846335619)
              ·
                refine ⟨20515156032470714769503429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13676770688313809846335619 20515156032470714769503429)
                ·
                  refine ⟨3846591756088259019281893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20515156032470714769503429 3846591756088259019281893)
                  ·
                    refine ⟨721235954266548566115355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3846591756088259019281893 721235954266548566115355)
                    ·
                      rfl

theorem cell23_4213806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_4213806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213806 prefixEnd_4213806 := by exact prefixLift 4213806
  have htrace : WordTrace (prefixWord ++ tailWord_4213806) baseStart_4213806 baseEnd_4213806 := by
    simpa [prefixWord, tailWord_4213806, baseEnd_4213806] using wordTrace_append hprefix tailTrace_4213806
  have hstable : (prefixWord ++ tailWord_4213806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213806).length < 2 ^ (prefixWord ++ tailWord_4213806).sum := by decide
  have hdescent : baseEnd_4213806 < baseStart_4213806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213830 : List Nat := [6, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_4213830 : Nat := 118140960795 + 4213830 * 2 ^ 59
def prefixEnd_4213830 : Nat := 4983230072969 + 3 ^ 40 * 4213830 * 2
def baseEnd_4213830 : Nat := 2163720186335353604445955

theorem tailTrace_4213830 : CollatzResearch.WordTrace tailWord_4213830 prefixEnd_4213830 2163720186335353604445955 := by
  unfold tailWord_4213830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4802843947625657803551967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 102460670882680699809108629 4802843947625657803551967)
  ·
    refine ⟨7204265921438486705327951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4802843947625657803551967 7204265921438486705327951)
    ·
      refine ⟨10806398882157730057991927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7204265921438486705327951 10806398882157730057991927)
      ·
        refine ⟨16209598323236595086987891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10806398882157730057991927 16209598323236595086987891)
        ·
          refine ⟨24314397484854892630481837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16209598323236595086987891 24314397484854892630481837)
          ·
            refine ⟨9117899056820584736430689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24314397484854892630481837 9117899056820584736430689)
            ·
              refine ⟨6838424292615438552323017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9117899056820584736430689 6838424292615438552323017)
              ·
                refine ⟨5128818219461578914242263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6838424292615438552323017 5128818219461578914242263)
                ·
                  refine ⟨7693227329192368371363395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5128818219461578914242263 7693227329192368371363395)
                  ·
                    refine ⟨11539840993788552557045093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7693227329192368371363395 11539840993788552557045093)
                    ·
                      refine ⟨2163720186335353604445955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11539840993788552557045093 2163720186335353604445955)
                      ·
                        rfl

theorem cell23_4213830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_4213830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213830 prefixEnd_4213830 := by exact prefixLift 4213830
  have htrace : WordTrace (prefixWord ++ tailWord_4213830) baseStart_4213830 baseEnd_4213830 := by
    simpa [prefixWord, tailWord_4213830, baseEnd_4213830] using wordTrace_append hprefix tailTrace_4213830
  have hstable : (prefixWord ++ tailWord_4213830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213830).length < 2 ^ (prefixWord ++ tailWord_4213830).sum := by decide
  have hdescent : baseEnd_4213830 < baseStart_4213830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213853 : List Nat := [1, 4, 4, 1, 3, 1, 9]
def baseStart_4213853 : Nat := 118140960795 + 4213853 * 2 ^ 59
def prefixEnd_4213853 : Nat := 4983230072969 + 3 ^ 40 * 4213853 * 2
def baseEnd_4213853 : Nat := 26712740696177864376029

theorem tailTrace_4213853 : CollatzResearch.WordTrace tailWord_4213853 prefixEnd_4213853 26712740696177864376029 := by
  unfold tailWord_4213853
  simp only [CollatzResearch.WordTrace]
  refine ⟨153691845202937724641750213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102461230135291816427833475 153691845202937724641750213)
  ·
    refine ⟨28817220975550823370328165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153691845202937724641750213 28817220975550823370328165)
    ·
      refine ⟨5403228932915779381936531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28817220975550823370328165 5403228932915779381936531)
      ·
        refine ⟨8104843399373669072904797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5403228932915779381936531 8104843399373669072904797)
        ·
          refine ⟨3039316274765125902339299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8104843399373669072904797 3039316274765125902339299)
          ·
            refine ⟨4558974412147688853508949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3039316274765125902339299 4558974412147688853508949)
            ·
              refine ⟨26712740696177864376029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4558974412147688853508949 26712740696177864376029)
              ·
                rfl

theorem cell23_4213853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 9].length) (baseStart_4213853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213853 prefixEnd_4213853 := by exact prefixLift 4213853
  have htrace : WordTrace (prefixWord ++ tailWord_4213853) baseStart_4213853 baseEnd_4213853 := by
    simpa [prefixWord, tailWord_4213853, baseEnd_4213853] using wordTrace_append hprefix tailTrace_4213853
  have hstable : (prefixWord ++ tailWord_4213853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213853).length < 2 ^ (prefixWord ++ tailWord_4213853).sum := by decide
  have hdescent : baseEnd_4213853 < baseStart_4213853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213864 : List Nat := [2, 1, 4, 4, 2, 1, 1, 1, 3, 2, 2]
def baseStart_4213864 : Nat := 118140960795 + 4213864 * 2 ^ 59
def prefixEnd_4213864 : Nat := 4983230072969 + 3 ^ 40 * 4213864 * 2
def baseEnd_4213864 : Nat := 2163737644677606471420799

theorem tailTrace_4213864 : CollatzResearch.WordTrace tailWord_4213864 prefixEnd_4213864 2163737644677606471420799 := by
  unfold tailWord_4213864
  simp only [CollatzResearch.WordTrace]
  refine ⟨76846123202948936760200323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102461497603931915680267097 76846123202948936760200323)
  ·
    refine ⟨115269184804423405140300485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76846123202948936760200323 115269184804423405140300485)
    ·
      refine ⟨21612972150829388463806341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115269184804423405140300485 21612972150829388463806341)
      ·
        refine ⟨4052432278280510336963689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21612972150829388463806341 4052432278280510336963689)
        ·
          refine ⟨3039324208710382752722767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4052432278280510336963689 3039324208710382752722767)
          ·
            refine ⟨4558986313065574129084151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3039324208710382752722767 4558986313065574129084151)
            ·
              refine ⟨6838479469598361193626227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4558986313065574129084151 6838479469598361193626227)
              ·
                refine ⟨10257719204397541790439341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6838479469598361193626227 10257719204397541790439341)
                ·
                  refine ⟨3846644701649078171414753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10257719204397541790439341 3846644701649078171414753)
                  ·
                    refine ⟨2884983526236808628561065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3846644701649078171414753 2884983526236808628561065)
                    ·
                      refine ⟨2163737644677606471420799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2884983526236808628561065 2163737644677606471420799)
                      ·
                        rfl

theorem cell23_4213864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_4213864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213864 prefixEnd_4213864 := by exact prefixLift 4213864
  have htrace : WordTrace (prefixWord ++ tailWord_4213864) baseStart_4213864 baseEnd_4213864 := by
    simpa [prefixWord, tailWord_4213864, baseEnd_4213864] using wordTrace_append hprefix tailTrace_4213864
  have hstable : (prefixWord ++ tailWord_4213864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213864).length < 2 ^ (prefixWord ++ tailWord_4213864).sum := by decide
  have hdescent : baseEnd_4213864 < baseStart_4213864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213906 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_4213906 : Nat := 118140960795 + 4213906 * 2 ^ 59
def prefixEnd_4213906 : Nat := 4983230072969 + 3 ^ 40 * 4213906 * 2
def baseEnd_4213906 : Nat := 2163759210865095307095605

theorem tailTrace_4213906 : CollatzResearch.WordTrace tailWord_4213906 prefixEnd_4213906 2163759210865095307095605 := by
  unfold tailWord_4213906
  simp only [CollatzResearch.WordTrace]
  refine ⟨38423444567936428673357393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102462518847830476462286381 38423444567936428673357393)
  ·
    refine ⟨28817583425952321505018045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38423444567936428673357393 28817583425952321505018045)
    ·
      refine ⟨10806593784732120564381767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28817583425952321505018045 10806593784732120564381767)
      ·
        refine ⟨16209890677098180846572651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10806593784732120564381767 16209890677098180846572651)
        ·
          refine ⟨24314836015647271269858977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16209890677098180846572651 24314836015647271269858977)
          ·
            refine ⟨18236127011735453452394233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24314836015647271269858977 18236127011735453452394233)
            ·
              refine ⟨13677095258801590089295675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18236127011735453452394233 13677095258801590089295675)
              ·
                refine ⟨20515642888202385133943513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13677095258801590089295675 20515642888202385133943513)
                ·
                  refine ⟨15386732166151788850457635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20515642888202385133943513 15386732166151788850457635)
                  ·
                    refine ⟨23080098249227683275686453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15386732166151788850457635 23080098249227683275686453)
                    ·
                      refine ⟨2163759210865095307095605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23080098249227683275686453 2163759210865095307095605)
                      ·
                        rfl

theorem cell23_4213906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_4213906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213906 prefixEnd_4213906 := by exact prefixLift 4213906
  have htrace : WordTrace (prefixWord ++ tailWord_4213906) baseStart_4213906 baseEnd_4213906 := by
    simpa [prefixWord, tailWord_4213906, baseEnd_4213906] using wordTrace_append hprefix tailTrace_4213906
  have hstable : (prefixWord ++ tailWord_4213906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213906).length < 2 ^ (prefixWord ++ tailWord_4213906).sum := by decide
  have hdescent : baseEnd_4213906 < baseStart_4213906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213920 : List Nat := [2, 1, 1, 4, 2, 1, 4, 2, 2, 2, 2]
def baseStart_4213920 : Nat := 118140960795 + 4213920 * 2 ^ 59
def prefixEnd_4213920 : Nat := 4983230072969 + 3 ^ 40 * 4213920 * 2
def baseEnd_4213920 : Nat := 2163766399594258252320541

theorem tailTrace_4213920 : CollatzResearch.WordTrace tailWord_4213920 prefixEnd_4213920 2163766399594258252320541 := by
  unfold tailWord_4213920
  simp only [CollatzResearch.WordTrace]
  refine ⟨76847144446847497542219607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102462859262463330056292809 76847144446847497542219607)
  ·
    refine ⟨115270716670271246313329411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76847144446847497542219607 115270716670271246313329411)
    ·
      refine ⟨172906075005406869469994117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115270716670271246313329411 172906075005406869469994117)
      ·
        refine ⟨32419889063513788025623897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172906075005406869469994117 32419889063513788025623897)
        ·
          refine ⟨24314916797635341019217923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32419889063513788025623897 24314916797635341019217923)
          ·
            refine ⟨36472375196453011528826885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24314916797635341019217923 36472375196453011528826885)
            ·
              refine ⟨6838570349334939661655041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36472375196453011528826885 6838570349334939661655041)
              ·
                refine ⟨5128927762001204746241281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6838570349334939661655041 5128927762001204746241281)
                ·
                  refine ⟨3846695821500903559680961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5128927762001204746241281 3846695821500903559680961)
                  ·
                    refine ⟨2885021866125677669760721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3846695821500903559680961 2885021866125677669760721)
                    ·
                      refine ⟨2163766399594258252320541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2885021866125677669760721 2163766399594258252320541)
                      ·
                        rfl

theorem cell23_4213920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_4213920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213920 prefixEnd_4213920 := by exact prefixLift 4213920
  have htrace : WordTrace (prefixWord ++ tailWord_4213920) baseStart_4213920 baseEnd_4213920 := by
    simpa [prefixWord, tailWord_4213920, baseEnd_4213920] using wordTrace_append hprefix tailTrace_4213920
  have hstable : (prefixWord ++ tailWord_4213920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213920).length < 2 ^ (prefixWord ++ tailWord_4213920).sum := by decide
  have hdescent : baseEnd_4213920 < baseStart_4213920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213933 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_4213933 : Nat := 118140960795 + 4213933 * 2 ^ 59
def prefixEnd_4213933 : Nat := 4983230072969 + 3 ^ 40 * 4213933 * 2
def baseEnd_4213933 : Nat := 2163773074842766701457981

theorem tailTrace_4213933 : CollatzResearch.WordTrace tailWord_4213933 prefixEnd_4213933 2163773074842766701457981 := by
  unfold tailWord_4213933
  simp only [CollatzResearch.WordTrace]
  refine ⟨153694763042647898304662453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102463175361765265536441635 153694763042647898304662453)
  ·
    refine ⟨14408884035248240466062105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153694763042647898304662453 14408884035248240466062105)
    ·
      refine ⟨10806663026436180349546579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14408884035248240466062105 10806663026436180349546579)
      ·
        refine ⟨16209994539654270524319869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10806663026436180349546579 16209994539654270524319869)
        ·
          refine ⟨6078747952370351446619951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16209994539654270524319869 6078747952370351446619951)
          ·
            refine ⟨9118121928555527169929927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6078747952370351446619951 9118121928555527169929927)
            ·
              refine ⟨13677182892833290754894891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9118121928555527169929927 13677182892833290754894891)
              ·
                refine ⟨20515774339249936132342337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13677182892833290754894891 20515774339249936132342337)
                ·
                  refine ⟨15386830754437452099256753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20515774339249936132342337 15386830754437452099256753)
                  ·
                    refine ⟨11540123065828089074442565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15386830754437452099256753 11540123065828089074442565)
                    ·
                      refine ⟨2163773074842766701457981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11540123065828089074442565 2163773074842766701457981)
                      ·
                        rfl

theorem cell23_4213933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_4213933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213933 prefixEnd_4213933 := by exact prefixLift 4213933
  have htrace : WordTrace (prefixWord ++ tailWord_4213933) baseStart_4213933 baseEnd_4213933 := by
    simpa [prefixWord, tailWord_4213933, baseEnd_4213933] using wordTrace_append hprefix tailTrace_4213933
  have hstable : (prefixWord ++ tailWord_4213933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213933).length < 2 ^ (prefixWord ++ tailWord_4213933).sum := by decide
  have hdescent : baseEnd_4213933 < baseStart_4213933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213939 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 4, 5]
def baseStart_4213939 : Nat := 118140960795 + 4213939 * 2 ^ 59
def prefixEnd_4213939 : Nat := 4983230072969 + 3 ^ 40 * 4213939 * 2
def baseEnd_4213939 : Nat := 721258718575564559327651

theorem tailTrace_4213939 : CollatzResearch.WordTrace tailWord_4213939 prefixEnd_4213939 721258718575564559327651 := by
  unfold tailWord_4213939
  simp only [CollatzResearch.WordTrace]
  refine ⟨153694981880626161329380871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102463321253750774219587247 153694981880626161329380871)
  ·
    refine ⟨230542472820939241994071307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153694981880626161329380871 230542472820939241994071307)
    ·
      refine ⟨345813709231408862991106961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230542472820939241994071307 345813709231408862991106961)
      ·
        refine ⟨259360281923556647243330221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345813709231408862991106961 259360281923556647243330221)
        ·
          refine ⟨97260105721333742716248833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259360281923556647243330221 97260105721333742716248833)
          ·
            refine ⟨72945079291000307037186625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97260105721333742716248833 72945079291000307037186625)
            ·
              refine ⟨54708809468250230277889969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72945079291000307037186625 54708809468250230277889969)
              ·
                refine ⟨41031607101187672708417477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54708809468250230277889969 41031607101187672708417477)
                ·
                  refine ⟨7693426331472688632828277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41031607101187672708417477 7693426331472688632828277)
                  ·
                    refine ⟨721258718575564559327651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7693426331472688632828277 721258718575564559327651)
                    ·
                      rfl

theorem cell23_4213939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 5].length) (baseStart_4213939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213939 prefixEnd_4213939 := by exact prefixLift 4213939
  have htrace : WordTrace (prefixWord ++ tailWord_4213939) baseStart_4213939 baseEnd_4213939 := by
    simpa [prefixWord, tailWord_4213939, baseEnd_4213939] using wordTrace_append hprefix tailTrace_4213939
  have hstable : (prefixWord ++ tailWord_4213939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213939).length < 2 ^ (prefixWord ++ tailWord_4213939).sum := by decide
  have hdescent : baseEnd_4213939 < baseStart_4213939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213946 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2]
def baseStart_4213946 : Nat := 118140960795 + 4213946 * 2 ^ 59
def prefixEnd_4213946 : Nat := 4983230072969 + 3 ^ 40 * 4213946 * 2
def baseEnd_4213946 : Nat := 2163779750091275150595421

theorem tailTrace_4213946 : CollatzResearch.WordTrace tailWord_4213946 prefixEnd_4213946 2163779750091275150595421 := by
  unfold tailWord_4213946
  simp only [CollatzResearch.WordTrace]
  refine ⟨38423809297900200381221423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102463491461067201016590461 38423809297900200381221423)
  ·
    refine ⟨57635713946850300571832135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38423809297900200381221423 57635713946850300571832135)
    ·
      refine ⟨86453570920275450857748203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57635713946850300571832135 86453570920275450857748203)
      ·
        refine ⟨129680356380413176286622305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86453570920275450857748203 129680356380413176286622305)
        ·
          refine ⟨97260267285309882214966729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129680356380413176286622305 97260267285309882214966729)
          ·
            refine ⟨72945200463982411661225047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97260267285309882214966729 72945200463982411661225047)
            ·
              refine ⟨109417800695973617491837571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72945200463982411661225047 109417800695973617491837571)
              ·
                refine ⟨164126701043960426237756357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109417800695973617491837571 164126701043960426237756357)
                ·
                  refine ⟨30773756445742579919579317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164126701043960426237756357 30773756445742579919579317)
                  ·
                    refine ⟨2885039666788366867460561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30773756445742579919579317 2885039666788366867460561)
                    ·
                      refine ⟨2163779750091275150595421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2885039666788366867460561 2163779750091275150595421)
                      ·
                        rfl

theorem cell23_4213946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2].length) (baseStart_4213946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213946 prefixEnd_4213946 := by exact prefixLift 4213946
  have htrace : WordTrace (prefixWord ++ tailWord_4213946) baseStart_4213946 baseEnd_4213946 := by
    simpa [prefixWord, tailWord_4213946, baseEnd_4213946] using wordTrace_append hprefix tailTrace_4213946
  have hstable : (prefixWord ++ tailWord_4213946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213946).length < 2 ^ (prefixWord ++ tailWord_4213946).sum := by decide
  have hdescent : baseEnd_4213946 < baseStart_4213946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213949 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_4213949 : Nat := 118140960795 + 4213949 * 2 ^ 59
def prefixEnd_4213949 : Nat := 4983230072969 + 3 ^ 40 * 4213949 * 2
def baseEnd_4213949 : Nat := 2163781290533238638857907

theorem tailTrace_4213949 : CollatzResearch.WordTrace tailWord_4213949 prefixEnd_4213949 2163781290533238638857907 := by
  unfold tailWord_4213949
  simp only [CollatzResearch.WordTrace]
  refine ⟨153695346610589933037244901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102463564407059955358163267 153695346610589933037244901)
  ·
    refine ⟨28817877489485612444483419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153695346610589933037244901 28817877489485612444483419)
    ·
      refine ⟨43226816234228418666725129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28817877489485612444483419 43226816234228418666725129)
      ·
        refine ⟨32420112175671314000043847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43226816234228418666725129 32420112175671314000043847)
        ·
          refine ⟨48630168263506971000065771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32420112175671314000043847 48630168263506971000065771)
          ·
            refine ⟨72945252395260456500098657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48630168263506971000065771 72945252395260456500098657)
            ·
              refine ⟨54708939296445342375073993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72945252395260456500098657 54708939296445342375073993)
              ·
                refine ⟨41031704472334006781305495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54708939296445342375073993 41031704472334006781305495)
                ·
                  refine ⟨61547556708501010171958243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41031704472334006781305495 61547556708501010171958243)
                  ·
                    refine ⟨92321335062751515257937365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61547556708501010171958243 92321335062751515257937365)
                    ·
                      refine ⟨2163781290533238638857907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92321335062751515257937365 2163781290533238638857907)
                      ·
                        rfl

theorem cell23_4213949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_4213949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213949 prefixEnd_4213949 := by exact prefixLift 4213949
  have htrace : WordTrace (prefixWord ++ tailWord_4213949) baseStart_4213949 baseEnd_4213949 := by
    simpa [prefixWord, tailWord_4213949, baseEnd_4213949] using wordTrace_append hprefix tailTrace_4213949
  have hstable : (prefixWord ++ tailWord_4213949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213949).length < 2 ^ (prefixWord ++ tailWord_4213949).sum := by decide
  have hdescent : baseEnd_4213949 < baseStart_4213949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213958 : List Nat := [6, 1, 2, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_4213958 : Nat := 118140960795 + 4213958 * 2 ^ 59
def prefixEnd_4213958 : Nat := 4983230072969 + 3 ^ 40 * 4213958 * 2
def baseEnd_4213958 : Nat := 2163785911859129103645367

theorem tailTrace_4213958 : CollatzResearch.WordTrace tailWord_4213958 prefixEnd_4213958 2163785911859129103645367 := by
  unfold tailWord_4213958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4802989839611166486697579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 102463783245038218382881685 4802989839611166486697579)
  ·
    refine ⟨7204484759416749730046369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4802989839611166486697579 7204484759416749730046369)
    ·
      refine ⟨5403363569562562297534777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7204484759416749730046369 5403363569562562297534777)
      ·
        refine ⟨4052522677171921723151083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5403363569562562297534777 4052522677171921723151083)
        ·
          refine ⟨6078784015757882584726625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4052522677171921723151083 6078784015757882584726625)
          ·
            refine ⟨4559088011818411938544969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6078784015757882584726625 4559088011818411938544969)
            ·
              refine ⟨3419316008863808953908727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4559088011818411938544969 3419316008863808953908727)
              ·
                refine ⟨5128974013295713430863091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3419316008863808953908727 5128974013295713430863091)
                ·
                  refine ⟨7693461019943570146294637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5128974013295713430863091 7693461019943570146294637)
                  ·
                    refine ⟨2885047882478838804860489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7693461019943570146294637 2885047882478838804860489)
                    ·
                      refine ⟨2163785911859129103645367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2885047882478838804860489 2163785911859129103645367)
                      ·
                        rfl

theorem cell23_4213958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_4213958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213958 prefixEnd_4213958 := by exact prefixLift 4213958
  have htrace : WordTrace (prefixWord ++ tailWord_4213958) baseStart_4213958 baseEnd_4213958 := by
    simpa [prefixWord, tailWord_4213958, baseEnd_4213958] using wordTrace_append hprefix tailTrace_4213958
  have hstable : (prefixWord ++ tailWord_4213958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213958).length < 2 ^ (prefixWord ++ tailWord_4213958).sum := by decide
  have hdescent : baseEnd_4213958 < baseStart_4213958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4213996 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 3]
def baseStart_4213996 : Nat := 118140960795 + 4213996 * 2 ^ 59
def prefixEnd_4213996 : Nat := 4983230072969 + 3 ^ 40 * 4213996 * 2
def baseEnd_4213996 : Nat := 2163805424123999954970191

theorem tailTrace_4213996 : CollatzResearch.WordTrace tailWord_4213996 prefixEnd_4213996 2163805424123999954970191 := by
  unfold tailWord_4213996
  simp only [CollatzResearch.WordTrace]
  refine ⟨76848530420709830032102921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102464707227613106709470561 76848530420709830032102921)
  ·
    refine ⟨57636397815532372524077191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76848530420709830032102921 57636397815532372524077191)
    ·
      refine ⟨86454596723298558786115787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57636397815532372524077191 86454596723298558786115787)
      ·
        refine ⟨129681895084947838179173681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86454596723298558786115787 129681895084947838179173681)
        ·
          refine ⟨97261421313710878634380261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129681895084947838179173681 97261421313710878634380261)
          ·
            refine ⟨18236516496320789743946299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97261421313710878634380261 18236516496320789743946299)
            ·
              refine ⟨27354774744481184615919449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18236516496320789743946299 27354774744481184615919449)
              ·
                refine ⟨20516081058360888461939587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27354774744481184615919449 20516081058360888461939587)
                ·
                  refine ⟨30774121587541332692909381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20516081058360888461939587 30774121587541332692909381)
                  ·
                    refine ⟨5770147797663999879920509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30774121587541332692909381 5770147797663999879920509)
                    ·
                      refine ⟨2163805424123999954970191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5770147797663999879920509 2163805424123999954970191)
                      ·
                        rfl

theorem cell23_4213996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_4213996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4213996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4213996 prefixEnd_4213996 := by exact prefixLift 4213996
  have htrace : WordTrace (prefixWord ++ tailWord_4213996) baseStart_4213996 baseEnd_4213996 := by
    simpa [prefixWord, tailWord_4213996, baseEnd_4213996] using wordTrace_append hprefix tailTrace_4213996
  have hstable : (prefixWord ++ tailWord_4213996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4213996).length < 2 ^ (prefixWord ++ tailWord_4213996).sum := by decide
  have hdescent : baseEnd_4213996 < baseStart_4213996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4213996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214006 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_4214006 : Nat := 118140960795 + 4214006 * 2 ^ 59
def prefixEnd_4214006 : Nat := 4983230072969 + 3 ^ 40 * 4214006 * 2
def baseEnd_4214006 : Nat := 2163810558930544915845145

theorem tailTrace_4214006 : CollatzResearch.WordTrace tailWord_4214006 prefixEnd_4214006 2163810558930544915845145 := by
  unfold tailWord_4214006
  simp only [CollatzResearch.WordTrace]
  refine ⟨9606089098211464485754367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102464950380922287848046581 9606089098211464485754367)
  ·
    refine ⟨14409133647317196728631551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9606089098211464485754367 14409133647317196728631551)
    ·
      refine ⟨21613700470975795092947327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14409133647317196728631551 21613700470975795092947327)
      ·
        refine ⟨32420550706463692639420991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21613700470975795092947327 32420550706463692639420991)
        ·
          refine ⟨48630826059695538959131487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32420550706463692639420991 48630826059695538959131487)
          ·
            refine ⟨72946239089543308438697231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48630826059695538959131487 72946239089543308438697231)
            ·
              refine ⟨109419358634314962658045847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72946239089543308438697231 109419358634314962658045847)
              ·
                refine ⟨164129037951472443987068771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109419358634314962658045847 164129037951472443987068771)
                ·
                  refine ⟨246193556927208665980603157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164129037951472443987068771 246193556927208665980603157)
                  ·
                    refine ⟨11540322980962906217840773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 246193556927208665980603157 11540322980962906217840773)
                    ·
                      refine ⟨2163810558930544915845145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11540322980962906217840773 2163810558930544915845145)
                      ·
                        rfl

theorem cell23_4214006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_4214006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214006 prefixEnd_4214006 := by exact prefixLift 4214006
  have htrace : WordTrace (prefixWord ++ tailWord_4214006) baseStart_4214006 baseEnd_4214006 := by
    simpa [prefixWord, tailWord_4214006, baseEnd_4214006] using wordTrace_append hprefix tailTrace_4214006
  have hstable : (prefixWord ++ tailWord_4214006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214006).length < 2 ^ (prefixWord ++ tailWord_4214006).sum := by decide
  have hdescent : baseEnd_4214006 < baseStart_4214006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214076 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 3, 6]
def baseStart_4214076 : Nat := 118140960795 + 4214076 * 2 ^ 59
def prefixEnd_4214076 : Nat := 4983230072969 + 3 ^ 40 * 4214076 * 2
def baseEnd_4214076 : Nat := 721282167525453213989941

theorem tailTrace_4214076 : CollatzResearch.WordTrace tailWord_4214076 prefixEnd_4214076 721282167525453213989941 := by
  unfold tailWord_4214076
  simp only [CollatzResearch.WordTrace]
  refine ⟨76849989340564916863559041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102466652454086555818078721 76849989340564916863559041)
  ·
    refine ⟨57637492005423687647669281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76849989340564916863559041 57637492005423687647669281)
    ·
      refine ⟨43228119004067765735751961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57637492005423687647669281 43228119004067765735751961)
      ·
        refine ⟨32421089253050824301813971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43228119004067765735751961 32421089253050824301813971)
        ·
          refine ⟨48631633879576236452720957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32421089253050824301813971 48631633879576236452720957)
          ·
            refine ⟨18236862704841088669770359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48631633879576236452720957 18236862704841088669770359)
            ·
              refine ⟨27355294057261633004655539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18236862704841088669770359 27355294057261633004655539)
              ·
                refine ⟨41032941085892449506983309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27355294057261633004655539 41032941085892449506983309)
                ·
                  refine ⟨15387352907209668565118741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41032941085892449506983309 15387352907209668565118741)
                  ·
                    refine ⟨721282167525453213989941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15387352907209668565118741 721282167525453213989941)
                    ·
                      rfl

theorem cell23_4214076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_4214076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214076 prefixEnd_4214076 := by exact prefixLift 4214076
  have htrace : WordTrace (prefixWord ++ tailWord_4214076) baseStart_4214076 baseEnd_4214076 := by
    simpa [prefixWord, tailWord_4214076, baseEnd_4214076] using wordTrace_append hprefix tailTrace_4214076
  have hstable : (prefixWord ++ tailWord_4214076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214076).length < 2 ^ (prefixWord ++ tailWord_4214076).sum := by decide
  have hdescent : baseEnd_4214076 < baseStart_4214076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214096 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 4]
def baseStart_4214096 : Nat := 118140960795 + 4214096 * 2 ^ 59
def prefixEnd_4214096 : Nat := 4983230072969 + 3 ^ 40 * 4214096 * 2
def baseEnd_4214096 : Nat := 2163856772189449563719731

theorem tailTrace_4214096 : CollatzResearch.WordTrace tailWord_4214096 prefixEnd_4214096 2163856772189449563719731 := by
  unfold tailWord_4214096
  simp only [CollatzResearch.WordTrace]
  refine ⟨76850354070528688571423071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102467138760704918095230761 76850354070528688571423071)
  ·
    refine ⟨115275531105793032857134607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76850354070528688571423071 115275531105793032857134607)
    ·
      refine ⟨172913296658689549285701911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115275531105793032857134607 172913296658689549285701911)
      ·
        refine ⟨259369944988034323928552867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172913296658689549285701911 259369944988034323928552867)
        ·
          refine ⟨389054917482051485892829301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259369944988034323928552867 389054917482051485892829301)
          ·
            refine ⟨36473898513942326802452747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 389054917482051485892829301 36473898513942326802452747)
            ·
              refine ⟨54710847770913490203679121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36473898513942326802452747 54710847770913490203679121)
              ·
                refine ⟨41033135828185117652759341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54710847770913490203679121 41033135828185117652759341)
                ·
                  refine ⟨15387425935569419119784753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41033135828185117652759341 15387425935569419119784753)
                  ·
                    refine ⟨11540569451677064339838565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15387425935569419119784753 11540569451677064339838565)
                    ·
                      refine ⟨2163856772189449563719731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11540569451677064339838565 2163856772189449563719731)
                      ·
                        rfl

theorem cell23_4214096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_4214096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214096 prefixEnd_4214096 := by exact prefixLift 4214096
  have htrace : WordTrace (prefixWord ++ tailWord_4214096) baseStart_4214096 baseEnd_4214096 := by
    simpa [prefixWord, tailWord_4214096, baseEnd_4214096] using wordTrace_append hprefix tailTrace_4214096
  have hstable : (prefixWord ++ tailWord_4214096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214096).length < 2 ^ (prefixWord ++ tailWord_4214096).sum := by decide
  have hdescent : baseEnd_4214096 < baseStart_4214096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214103 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 3]
def baseStart_4214103 : Nat := 118140960795 + 4214103 * 2 ^ 59
def prefixEnd_4214103 : Nat := 4983230072969 + 3 ^ 40 * 4214103 * 2
def baseEnd_4214103 : Nat := 2163860366554031036332199

theorem tailTrace_4214103 : CollatzResearch.WordTrace tailWord_4214103 prefixEnd_4214103 2163860366554031036332199 := by
  unfold tailWord_4214103
  simp only [CollatzResearch.WordTrace]
  refine ⟨153700963452032017338350963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102467308968021344892233975 153700963452032017338350963)
  ·
    refine ⟨230551445178048026007526445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153700963452032017338350963 230551445178048026007526445)
    ·
      refine ⟨86456791941768009752822417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230551445178048026007526445 86456791941768009752822417)
      ·
        refine ⟨64842593956326007314616813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86456791941768009752822417 64842593956326007314616813)
        ·
          refine ⟨24315972733622252742981305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64842593956326007314616813 24315972733622252742981305)
          ·
            refine ⟨18236979550216689557235979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24315972733622252742981305 18236979550216689557235979)
            ·
              refine ⟨27355469325325034335853969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18236979550216689557235979 27355469325325034335853969)
              ·
                refine ⟨20516601993993775751890477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27355469325325034335853969 20516601993993775751890477)
                ·
                  refine ⟨7693725747747665906958929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20516601993993775751890477 7693725747747665906958929)
                  ·
                    refine ⟨5770294310810749430219197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7693725747747665906958929 5770294310810749430219197)
                    ·
                      refine ⟨2163860366554031036332199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5770294310810749430219197 2163860366554031036332199)
                      ·
                        rfl

theorem cell23_4214103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_4214103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214103 prefixEnd_4214103 := by exact prefixLift 4214103
  have htrace : WordTrace (prefixWord ++ tailWord_4214103) baseStart_4214103 baseEnd_4214103 := by
    simpa [prefixWord, tailWord_4214103, baseEnd_4214103] using wordTrace_append hprefix tailTrace_4214103
  have hstable : (prefixWord ++ tailWord_4214103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214103).length < 2 ^ (prefixWord ++ tailWord_4214103).sum := by decide
  have hdescent : baseEnd_4214103 < baseStart_4214103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214106 : List Nat := [3, 1, 1, 2, 1, 2, 5, 8]
def baseStart_4214106 : Nat := 118140960795 + 4214106 * 2 ^ 59
def prefixEnd_4214106 : Nat := 4983230072969 + 3 ^ 40 * 4214106 * 2
def baseEnd_4214106 : Nat := 80143033592444241651655

theorem tailTrace_4214106 : CollatzResearch.WordTrace tailWord_4214106 prefixEnd_4214106 80143033592444241651655 := by
  unfold tailWord_4214106
  simp only [CollatzResearch.WordTrace]
  refine ⟨38425268217755287212677543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102467381914014099233806781 38425268217755287212677543)
  ·
    refine ⟨57637902326632930819016315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38425268217755287212677543 57637902326632930819016315)
    ·
      refine ⟨86456853489949396228524473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57637902326632930819016315 86456853489949396228524473)
      ·
        refine ⟨64842640117462047171393355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86456853489949396228524473 64842640117462047171393355)
        ·
          refine ⟨97263960176193070757090033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64842640117462047171393355 97263960176193070757090033)
          ·
            refine ⟨72947970132144803067817525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97263960176193070757090033 72947970132144803067817525)
            ·
              refine ⟨6838872199888575287607893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72947970132144803067817525 6838872199888575287607893)
              ·
                refine ⟨80143033592444241651655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6838872199888575287607893 80143033592444241651655)
                ·
                  rfl

theorem cell23_4214106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 8].length) (baseStart_4214106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214106 prefixEnd_4214106 := by exact prefixLift 4214106
  have htrace : WordTrace (prefixWord ++ tailWord_4214106) baseStart_4214106 baseEnd_4214106 := by
    simpa [prefixWord, tailWord_4214106, baseEnd_4214106] using wordTrace_append hprefix tailTrace_4214106
  have hstable : (prefixWord ++ tailWord_4214106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214106).length < 2 ^ (prefixWord ++ tailWord_4214106).sum := by decide
  have hdescent : baseEnd_4214106 < baseStart_4214106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214174 : List Nat := [4, 3, 1, 2, 3, 1, 2, 7]
def baseStart_4214174 : Nat := 118140960795 + 4214174 * 2 ^ 59
def prefixEnd_4214174 : Nat := 4983230072969 + 3 ^ 40 * 4214174 * 2
def baseEnd_4214174 : Nat := 80144326802981491057199

theorem tailTrace_4214174 : CollatzResearch.WordTrace tailWord_4214174 prefixEnd_4214174 80144326802981491057199 := by
  unfold tailWord_4214174
  simp only [CollatzResearch.WordTrace]
  refine ⟨19212944129346849558023197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102469035356516530976123717 19212944129346849558023197)
  ·
    refine ⟨7204854048505068584258699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19212944129346849558023197 7204854048505068584258699)
    ·
      refine ⟨10807281072757602876388049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7204854048505068584258699 10807281072757602876388049)
      ·
        refine ⟨8105460804568202157291037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10807281072757602876388049 8105460804568202157291037)
        ·
          refine ⟨3039547801713075808984139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8105460804568202157291037 3039547801713075808984139)
          ·
            refine ⟨4559321702569613713476209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3039547801713075808984139 4559321702569613713476209)
            ·
              refine ⟨3419491276927210285107157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4559321702569613713476209 3419491276927210285107157)
              ·
                refine ⟨80144326802981491057199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3419491276927210285107157 80144326802981491057199)
                ·
                  rfl

theorem cell23_4214174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 7].length) (baseStart_4214174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214174 prefixEnd_4214174 := by exact prefixLift 4214174
  have htrace : WordTrace (prefixWord ++ tailWord_4214174) baseStart_4214174 baseEnd_4214174 := by
    simpa [prefixWord, tailWord_4214174, baseEnd_4214174] using wordTrace_append hprefix tailTrace_4214174
  have hstable : (prefixWord ++ tailWord_4214174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214174).length < 2 ^ (prefixWord ++ tailWord_4214174).sum := by decide
  have hdescent : baseEnd_4214174 < baseStart_4214174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214193 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 2, 1, 5]
def baseStart_4214193 : Nat := 118140960795 + 4214193 * 2 ^ 59
def prefixEnd_4214193 : Nat := 4983230072969 + 3 ^ 40 * 4214193 * 2
def baseEnd_4214193 : Nat := 2163906579812935684206785

theorem tailTrace_4214193 : CollatzResearch.WordTrace tailWord_4214193 prefixEnd_4214193 2163906579812935684206785 := by
  unfold tailWord_4214193
  simp only [CollatzResearch.WordTrace]
  refine ⟨153704246021705962709127233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102469497347803975139418155 153704246021705962709127233)
  ·
    refine ⟨115278184516279472031845425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153704246021705962709127233 115278184516279472031845425)
    ·
      refine ⟨86458638387209604023884069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115278184516279472031845425 86458638387209604023884069)
      ·
        refine ⟨16210994697601800754478263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86458638387209604023884069 16210994697601800754478263)
        ·
          refine ⟨24316492046402701131717395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16210994697601800754478263 24316492046402701131717395)
          ·
            refine ⟨36474738069604051697576093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24316492046402701131717395 36474738069604051697576093)
            ·
              refine ⟨13678026776101519386591035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36474738069604051697576093 13678026776101519386591035)
              ·
                refine ⟨20517040164152279079886553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13678026776101519386591035 20517040164152279079886553)
                ·
                  refine ⟨15387780123114209309914915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20517040164152279079886553 15387780123114209309914915)
                  ·
                    refine ⟨23081670184671313964872373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15387780123114209309914915 23081670184671313964872373)
                    ·
                      refine ⟨2163906579812935684206785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23081670184671313964872373 2163906579812935684206785)
                      ·
                        rfl

theorem cell23_4214193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_4214193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214193 prefixEnd_4214193 := by exact prefixLift 4214193
  have htrace : WordTrace (prefixWord ++ tailWord_4214193) baseStart_4214193 baseEnd_4214193 := by
    simpa [prefixWord, tailWord_4214193, baseEnd_4214193] using wordTrace_append hprefix tailTrace_4214193
  have hstable : (prefixWord ++ tailWord_4214193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214193).length < 2 ^ (prefixWord ++ tailWord_4214193).sum := by decide
  have hdescent : baseEnd_4214193 < baseStart_4214193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214223 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 3]
def baseStart_4214223 : Nat := 118140960795 + 4214223 * 2 ^ 59
def prefixEnd_4214223 : Nat := 4983230072969 + 3 ^ 40 * 4214223 * 2
def baseEnd_4214223 : Nat := 2163921984232570566831647

theorem tailTrace_4214223 : CollatzResearch.WordTrace tailWord_4214223 prefixEnd_4214223 2163921984232570566831647 := by
  unfold tailWord_4214223
  simp only [CollatzResearch.WordTrace]
  refine ⟨153705340211597277832719323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102470226807731518555146215 153705340211597277832719323)
  ·
    refine ⟨230558010317395916749078985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153705340211597277832719323 230558010317395916749078985)
    ·
      refine ⟨172918507738046937561809239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230558010317395916749078985 172918507738046937561809239)
      ·
        refine ⟨259377761607070406342713859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172918507738046937561809239 259377761607070406342713859)
        ·
          refine ⟨389066642410605609514070789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259377761607070406342713859 389066642410605609514070789)
          ·
            refine ⟨72949995451988551783888273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 389066642410605609514070789 72949995451988551783888273)
            ·
              refine ⟨54712496588991413837916205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72949995451988551783888273 54712496588991413837916205)
              ·
                refine ⟨20517186220871780189218577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54712496588991413837916205 20517186220871780189218577)
                ·
                  refine ⟨15387889665653835141913933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20517186220871780189218577 15387889665653835141913933)
                  ·
                    refine ⟨5770458624620188178217725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15387889665653835141913933 5770458624620188178217725)
                    ·
                      refine ⟨2163921984232570566831647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5770458624620188178217725 2163921984232570566831647)
                      ·
                        rfl

theorem cell23_4214223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3, 3].length) (baseStart_4214223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214223 prefixEnd_4214223 := by exact prefixLift 4214223
  have htrace : WordTrace (prefixWord ++ tailWord_4214223) baseStart_4214223 baseEnd_4214223 := by
    simpa [prefixWord, tailWord_4214223, baseEnd_4214223] using wordTrace_append hprefix tailTrace_4214223
  have hstable : (prefixWord ++ tailWord_4214223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214223).length < 2 ^ (prefixWord ++ tailWord_4214223).sum := by decide
  have hdescent : baseEnd_4214223 < baseStart_4214223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214263 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 4]
def baseStart_4214263 : Nat := 118140960795 + 4214263 * 2 ^ 59
def prefixEnd_4214263 : Nat := 4983230072969 + 3 ^ 40 * 4214263 * 2
def baseEnd_4214263 : Nat := 2163942523458750410331463

theorem tailTrace_4214263 : CollatzResearch.WordTrace tailWord_4214263 prefixEnd_4214263 2163942523458750410331463 := by
  unfold tailWord_4214263
  simp only [CollatzResearch.WordTrace]
  refine ⟨153706799131452364664175443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102471199420968243109450295 153706799131452364664175443)
  ·
    refine ⟨230560198697178546996263165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153706799131452364664175443 230560198697178546996263165)
    ·
      refine ⟨86460074511441955123598687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230560198697178546996263165 86460074511441955123598687)
      ·
        refine ⟨129690111767162932685398031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86460074511441955123598687 129690111767162932685398031)
        ·
          refine ⟨194535167650744399028097047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129690111767162932685398031 194535167650744399028097047)
          ·
            refine ⟨291802751476116598542145571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 194535167650744399028097047 291802751476116598542145571)
            ·
              refine ⟨437704127214174897813218357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291802751476116598542145571 437704127214174897813218357)
              ·
                refine ⟨41034761926328896669989221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 437704127214174897813218357 41034761926328896669989221)
                ·
                  refine ⟨7694017861186668125622979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41034761926328896669989221 7694017861186668125622979)
                  ·
                    refine ⟨11541026791780002188434469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7694017861186668125622979 11541026791780002188434469)
                    ·
                      refine ⟨2163942523458750410331463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11541026791780002188434469 2163942523458750410331463)
                      ·
                        rfl

theorem cell23_4214263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_4214263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214263 prefixEnd_4214263 := by exact prefixLift 4214263
  have htrace : WordTrace (prefixWord ++ tailWord_4214263) baseStart_4214263 baseEnd_4214263 := by
    simpa [prefixWord, tailWord_4214263, baseEnd_4214263] using wordTrace_append hprefix tailTrace_4214263
  have hstable : (prefixWord ++ tailWord_4214263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214263).length < 2 ^ (prefixWord ++ tailWord_4214263).sum := by decide
  have hdescent : baseEnd_4214263 < baseStart_4214263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214280 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 1, 6, 2]
def baseStart_4214280 : Nat := 118140960795 + 4214280 * 2 ^ 59
def prefixEnd_4214280 : Nat := 4983230072969 + 3 ^ 40 * 4214280 * 2
def baseEnd_4214280 : Nat := 2163951252629876843818885

theorem tailTrace_4214280 : CollatzResearch.WordTrace tailWord_4214280 prefixEnd_4214280 2163951252629876843818885 := by
  unfold tailWord_4214280
  simp only [CollatzResearch.WordTrace]
  refine ⟨76853709586195388283772147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102471612781593851045029529 76853709586195388283772147)
  ·
    refine ⟨115280564379293082425658221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76853709586195388283772147 115280564379293082425658221)
    ·
      refine ⟨43230211642234905909621833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 115280564379293082425658221 43230211642234905909621833)
      ·
        refine ⟨32422658731676179432216375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43230211642234905909621833 32422658731676179432216375)
        ·
          refine ⟨48633988097514269148324563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32422658731676179432216375 48633988097514269148324563)
          ·
            refine ⟨72950982146271403722486845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48633988097514269148324563 72950982146271403722486845)
            ·
              refine ⟨27356618304851776395932567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72950982146271403722486845 27356618304851776395932567)
              ·
                refine ⟨41034927457277664593898851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27356618304851776395932567 41034927457277664593898851)
                ·
                  refine ⟨61552391185916496890848277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41034927457277664593898851 61552391185916496890848277)
                  ·
                    refine ⟨2885268336839835791758513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61552391185916496890848277 2885268336839835791758513)
                    ·
                      refine ⟨2163951252629876843818885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2885268336839835791758513 2163951252629876843818885)
                      ·
                        rfl

theorem cell23_4214280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_4214280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214280 prefixEnd_4214280 := by exact prefixLift 4214280
  have htrace : WordTrace (prefixWord ++ tailWord_4214280) baseStart_4214280 baseEnd_4214280 := by
    simpa [prefixWord, tailWord_4214280, baseEnd_4214280] using wordTrace_append hprefix tailTrace_4214280
  have hstable : (prefixWord ++ tailWord_4214280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214280).length < 2 ^ (prefixWord ++ tailWord_4214280).sum := by decide
  have hdescent : baseEnd_4214280 < baseStart_4214280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214300 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_4214300 : Nat := 118140960795 + 4214300 * 2 ^ 59
def prefixEnd_4214300 : Nat := 4983230072969 + 3 ^ 40 * 4214300 * 2
def baseEnd_4214300 : Nat := 2163961522242966765568793

theorem tailTrace_4214300 : CollatzResearch.WordTrace tailWord_4214300 prefixEnd_4214300 2163961522242966765568793 := by
  unfold tailWord_4214300
  simp only [CollatzResearch.WordTrace]
  refine ⟨76854074316159159991636177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102472099088212213322181569 76854074316159159991636177)
  ·
    refine ⟨57640555737119369993727133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76854074316159159991636177 57640555737119369993727133)
    ·
      refine ⟨21615208401419763747647675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57640555737119369993727133 21615208401419763747647675)
      ·
        refine ⟨32422812602129645621471513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21615208401419763747647675 32422812602129645621471513)
        ·
          refine ⟨24317109451597234216103635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32422812602129645621471513 24317109451597234216103635)
          ·
            refine ⟨36475664177395851324155453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24317109451597234216103635 36475664177395851324155453)
            ·
              refine ⟨13678374066523444246558295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36475664177395851324155453 13678374066523444246558295)
              ·
                refine ⟨20517561099785166369837443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13678374066523444246558295 20517561099785166369837443)
                ·
                  refine ⟨30776341649677749554756165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20517561099785166369837443 30776341649677749554756165)
                  ·
                    refine ⟨5770564059314578041516781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30776341649677749554756165 5770564059314578041516781)
                    ·
                      refine ⟨2163961522242966765568793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5770564059314578041516781 2163961522242966765568793)
                      ·
                        rfl

theorem cell23_4214300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_4214300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214300 prefixEnd_4214300 := by exact prefixLift 4214300
  have htrace : WordTrace (prefixWord ++ tailWord_4214300) baseStart_4214300 baseEnd_4214300 := by
    simpa [prefixWord, tailWord_4214300, baseEnd_4214300] using wordTrace_append hprefix tailTrace_4214300
  have hstable : (prefixWord ++ tailWord_4214300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214300).length < 2 ^ (prefixWord ++ tailWord_4214300).sum := by decide
  have hdescent : baseEnd_4214300 < baseStart_4214300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214323 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 6]
def baseStart_4214323 : Nat := 118140960795 + 4214323 * 2 ^ 59
def prefixEnd_4214323 : Nat := 4983230072969 + 3 ^ 40 * 4214323 * 2
def baseEnd_4214323 : Nat := 2163973332298020175581187

theorem tailTrace_4214323 : CollatzResearch.WordTrace tailWord_4214323 prefixEnd_4214323 2163973332298020175581187 := by
  unfold tailWord_4214323
  simp only [CollatzResearch.WordTrace]
  refine ⟨153708987511234994911359623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102472658340823329940906415 153708987511234994911359623)
  ·
    refine ⟨230563481266852492367039435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153708987511234994911359623 230563481266852492367039435)
    ·
      refine ⟨345845221900278738550559153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230563481266852492367039435 345845221900278738550559153)
      ·
        refine ⟨259383916425209053912919365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345845221900278738550559153 259383916425209053912919365)
        ·
          refine ⟨48634484329726697608672381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 259383916425209053912919365 48634484329726697608672381)
          ·
            refine ⟨18237931623647511603252143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48634484329726697608672381 18237931623647511603252143)
            ·
              refine ⟨27356897435471267404878215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18237931623647511603252143 27356897435471267404878215)
              ·
                refine ⟨41035346153206901107317323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27356897435471267404878215 41035346153206901107317323)
                ·
                  refine ⟨61553019229810351660975985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41035346153206901107317323 61553019229810351660975985)
                  ·
                    refine ⟨46164764422357763745731989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61553019229810351660975985 46164764422357763745731989)
                    ·
                      refine ⟨2163973332298020175581187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46164764422357763745731989 2163973332298020175581187)
                      ·
                        rfl

theorem cell23_4214323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_4214323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214323 prefixEnd_4214323 := by exact prefixLift 4214323
  have htrace : WordTrace (prefixWord ++ tailWord_4214323) baseStart_4214323 baseEnd_4214323 := by
    simpa [prefixWord, tailWord_4214323, baseEnd_4214323] using wordTrace_append hprefix tailTrace_4214323
  have hstable : (prefixWord ++ tailWord_4214323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214323).length < 2 ^ (prefixWord ++ tailWord_4214323).sum := by decide
  have hdescent : baseEnd_4214323 < baseStart_4214323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214337 : List Nat := [1, 2, 5, 1, 1, 1, 5, 1, 6]
def baseStart_4214337 : Nat := 118140960795 + 4214337 * 2 ^ 59
def prefixEnd_4214337 : Nat := 4983230072969 + 3 ^ 40 * 4214337 * 2
def baseEnd_4214337 : Nat := 240442280114131457867347

theorem tailTrace_4214337 : CollatzResearch.WordTrace tailWord_4214337 prefixEnd_4214337 240442280114131457867347 := by
  unfold tailWord_4214337
  simp only [CollatzResearch.WordTrace]
  refine ⟨153709498133184275302369265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102472998755456183534912843 153709498133184275302369265)
  ·
    refine ⟨115282123599888206476776949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153709498133184275302369265 115282123599888206476776949)
    ·
      refine ⟨10807699087489519357197839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 115282123599888206476776949 10807699087489519357197839)
      ·
        refine ⟨16211548631234279035796759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10807699087489519357197839 16211548631234279035796759)
        ·
          refine ⟨24317322946851418553695139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16211548631234279035796759 24317322946851418553695139)
          ·
            refine ⟨36475984420277127830542709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24317322946851418553695139 36475984420277127830542709)
            ·
              refine ⟨3419623539400980734113379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36475984420277127830542709 3419623539400980734113379)
              ·
                refine ⟨5129435309101471101170069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3419623539400980734113379 5129435309101471101170069)
                ·
                  refine ⟨240442280114131457867347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5129435309101471101170069 240442280114131457867347)
                  ·
                    rfl

theorem cell23_4214337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 1, 6].length) (baseStart_4214337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214337 prefixEnd_4214337 := by exact prefixLift 4214337
  have htrace : WordTrace (prefixWord ++ tailWord_4214337) baseStart_4214337 baseEnd_4214337 := by
    simpa [prefixWord, tailWord_4214337, baseEnd_4214337] using wordTrace_append hprefix tailTrace_4214337
  have hstable : (prefixWord ++ tailWord_4214337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214337).length < 2 ^ (prefixWord ++ tailWord_4214337).sum := by decide
  have hdescent : baseEnd_4214337 < baseStart_4214337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214357 : List Nat := [1, 3, 2, 2, 1, 1, 1, 5, 2, 3, 2]
def baseStart_4214357 : Nat := 118140960795 + 4214357 * 2 ^ 59
def prefixEnd_4214357 : Nat := 4983230072969 + 3 ^ 40 * 4214357 * 2
def baseEnd_4214357 : Nat := 2163990790640273042556031

theorem tailTrace_4214357 : CollatzResearch.WordTrace tailWord_4214357 prefixEnd_4214357 2163990790640273042556031 := by
  unfold tailWord_4214357
  simp only [CollatzResearch.WordTrace]
  refine ⟨153710227593111818718097325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102473485062074545812064883 153710227593111818718097325)
  ·
    refine ⟨57641335347416932019286497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153710227593111818718097325 57641335347416932019286497)
    ·
      refine ⟨43231001510562699014464873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57641335347416932019286497 43231001510562699014464873)
      ·
        refine ⟨32423251132922024260848655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43231001510562699014464873 32423251132922024260848655)
        ·
          refine ⟨48634876699383036391272983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32423251132922024260848655 48634876699383036391272983)
          ·
            refine ⟨72952315049074554586909475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48634876699383036391272983 72952315049074554586909475)
            ·
              refine ⟨109428472573611831880364213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72952315049074554586909475 109428472573611831880364213)
              ·
                refine ⟨10258919303776109238784145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109428472573611831880364213 10258919303776109238784145)
                ·
                  refine ⟨7694189477832081929088109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10258919303776109238784145 7694189477832081929088109)
                  ·
                    refine ⟨2885321054187030723408041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7694189477832081929088109 2885321054187030723408041)
                    ·
                      refine ⟨2163990790640273042556031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2885321054187030723408041 2163990790640273042556031)
                      ·
                        rfl

theorem cell23_4214357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_4214357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214357 prefixEnd_4214357 := by exact prefixLift 4214357
  have htrace : WordTrace (prefixWord ++ tailWord_4214357) baseStart_4214357 baseEnd_4214357 := by
    simpa [prefixWord, tailWord_4214357, baseEnd_4214357] using wordTrace_append hprefix tailTrace_4214357
  have hstable : (prefixWord ++ tailWord_4214357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214357).length < 2 ^ (prefixWord ++ tailWord_4214357).sum := by decide
  have hdescent : baseEnd_4214357 < baseStart_4214357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214381 : List Nat := [1, 5, 1, 1, 4, 2, 1, 1, 3, 1, 3]
def baseStart_4214381 : Nat := 118140960795 + 4214381 * 2 ^ 59
def prefixEnd_4214381 : Nat := 4983230072969 + 3 ^ 40 * 4214381 * 2
def baseEnd_4214381 : Nat := 2164003114175980948655921

theorem tailTrace_4214381 : CollatzResearch.WordTrace tailWord_4214381 prefixEnd_4214381 2164003114175980948655921 := by
  unfold tailWord_4214381
  simp only [CollatzResearch.WordTrace]
  refine ⟨153711102945024870816970997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102474068630016580544647331 153711102945024870816970997)
  ·
    refine ⟨14410415901096081639091031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153711102945024870816970997 14410415901096081639091031)
    ·
      refine ⟨21615623851644122458636547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14410415901096081639091031 21615623851644122458636547)
      ·
        refine ⟨32423435777466183687954821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21615623851644122458636547 32423435777466183687954821)
        ·
          refine ⟨6079394208274909441491529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32423435777466183687954821 6079394208274909441491529)
          ·
            refine ⟨4559545656206182081118647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6079394208274909441491529 4559545656206182081118647)
            ·
              refine ⟨6839318484309273121677971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4559545656206182081118647 6839318484309273121677971)
              ·
                refine ⟨10258977726463909682516957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6839318484309273121677971 10258977726463909682516957)
                ·
                  refine ⟨3847116647423966130943859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10258977726463909682516957 3847116647423966130943859)
                  ·
                    refine ⟨5770674971135949196415789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3847116647423966130943859 5770674971135949196415789)
                    ·
                      refine ⟨2164003114175980948655921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5770674971135949196415789 2164003114175980948655921)
                      ·
                        rfl

theorem cell23_4214381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_4214381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214381 prefixEnd_4214381 := by exact prefixLift 4214381
  have htrace : WordTrace (prefixWord ++ tailWord_4214381) baseStart_4214381 baseEnd_4214381 := by
    simpa [prefixWord, tailWord_4214381, baseEnd_4214381] using wordTrace_append hprefix tailTrace_4214381
  have hstable : (prefixWord ++ tailWord_4214381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214381).length < 2 ^ (prefixWord ++ tailWord_4214381).sum := by decide
  have hdescent : baseEnd_4214381 < baseStart_4214381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214400 : List Nat := [2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 4]
def baseStart_4214400 : Nat := 118140960795 + 4214400 * 2 ^ 59
def prefixEnd_4214400 : Nat := 4983230072969 + 3 ^ 40 * 4214400 * 2
def baseEnd_4214400 : Nat := 2164012870308416374318333

theorem tailTrace_4214400 : CollatzResearch.WordTrace tailWord_4214400 prefixEnd_4214400 2164012870308416374318333 := by
  unfold tailWord_4214400
  simp only [CollatzResearch.WordTrace]
  refine ⟨76855897965978018530956327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102474530621304024707941769 76855897965978018530956327)
  ·
    refine ⟨115283846948967027796434491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76855897965978018530956327 115283846948967027796434491)
    ·
      refine ⟨172925770423450541694651737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115283846948967027796434491 172925770423450541694651737)
      ·
        refine ⟨129694327817587906270988803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172925770423450541694651737 129694327817587906270988803)
        ·
          refine ⟨194541491726381859406483205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129694327817587906270988803 194541491726381859406483205)
          ·
            refine ⟨36476529698696598638715601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 194541491726381859406483205 36476529698696598638715601)
            ·
              refine ⟨27357397274022448979036701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36476529698696598638715601 27357397274022448979036701)
              ·
                refine ⟨10259023977758418367138763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27357397274022448979036701 10259023977758418367138763)
                ·
                  refine ⟨15388535966637627550708145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10259023977758418367138763 15388535966637627550708145)
                  ·
                    refine ⟨11541401974978220663031109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15388535966637627550708145 11541401974978220663031109)
                    ·
                      refine ⟨2164012870308416374318333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11541401974978220663031109 2164012870308416374318333)
                      ·
                        rfl

theorem cell23_4214400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_4214400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214400 prefixEnd_4214400 := by exact prefixLift 4214400
  have htrace : WordTrace (prefixWord ++ tailWord_4214400) baseStart_4214400 baseEnd_4214400 := by
    simpa [prefixWord, tailWord_4214400, baseEnd_4214400] using wordTrace_append hprefix tailTrace_4214400
  have hstable : (prefixWord ++ tailWord_4214400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214400).length < 2 ^ (prefixWord ++ tailWord_4214400).sum := by decide
  have hdescent : baseEnd_4214400 < baseStart_4214400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214407 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 3]
def baseStart_4214407 : Nat := 118140960795 + 4214407 * 2 ^ 59
def prefixEnd_4214407 : Nat := 4983230072969 + 3 ^ 40 * 4214407 * 2
def baseEnd_4214407 : Nat := 2164016464672997846930801

theorem tailTrace_4214407 : CollatzResearch.WordTrace tailWord_4214407 prefixEnd_4214407 2164016464672997846930801 := by
  unfold tailWord_4214407
  simp only [CollatzResearch.WordTrace]
  refine ⟨153712051242930677257417475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102474700828620451504944983 153712051242930677257417475)
  ·
    refine ⟨230568076864396015886126213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153712051242930677257417475 230568076864396015886126213)
    ·
      refine ⟨43231514412074252978648665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230568076864396015886126213 43231514412074252978648665)
      ·
        refine ⟨32423635809055689733986499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43231514412074252978648665 32423635809055689733986499)
        ·
          refine ⟨48635453713583534600979749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32423635809055689733986499 48635453713583534600979749)
          ·
            refine ⟨9119147571296912737683703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48635453713583534600979749 9119147571296912737683703)
            ·
              refine ⟨13678721356945369106525555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9119147571296912737683703 13678721356945369106525555)
              ·
                refine ⟨20518082035418053659788333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13678721356945369106525555 20518082035418053659788333)
                ·
                  refine ⟨7694280763281770122420625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20518082035418053659788333 7694280763281770122420625)
                  ·
                    refine ⟨5770710572461327591815469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7694280763281770122420625 5770710572461327591815469)
                    ·
                      refine ⟨2164016464672997846930801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5770710572461327591815469 2164016464672997846930801)
                      ·
                        rfl

theorem cell23_4214407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_4214407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214407 prefixEnd_4214407 := by exact prefixLift 4214407
  have htrace : WordTrace (prefixWord ++ tailWord_4214407) baseStart_4214407 baseEnd_4214407 := by
    simpa [prefixWord, tailWord_4214407, baseEnd_4214407] using wordTrace_append hprefix tailTrace_4214407
  have hstable : (prefixWord ++ tailWord_4214407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214407).length < 2 ^ (prefixWord ++ tailWord_4214407).sum := by decide
  have hdescent : baseEnd_4214407 < baseStart_4214407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214410 : List Nat := [3, 1, 2, 3, 2, 1, 2, 9]
def baseStart_4214410 : Nat := 118140960795 + 4214410 * 2 ^ 59
def prefixEnd_4214410 : Nat := 4983230072969 + 3 ^ 40 * 4214410 * 2
def baseEnd_4214410 : Nat := 80148815004257827229381

theorem tailTrace_4214410 : CollatzResearch.WordTrace tailWord_4214410 prefixEnd_4214410 80148815004257827229381 := by
  unfold tailWord_4214410
  simp only [CollatzResearch.WordTrace]
  refine ⟨38428040165479952192444171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102474773774613205846517789 38428040165479952192444171)
  ·
    refine ⟨57642060248219928288666257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38428040165479952192444171 57642060248219928288666257)
    ·
      refine ⟨43231545186164946216499693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57642060248219928288666257 43231545186164946216499693)
      ·
        refine ⟨16211829444811854831187385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43231545186164946216499693 16211829444811854831187385)
        ·
          refine ⟨12158872083608891123390539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16211829444811854831187385 12158872083608891123390539)
          ·
            refine ⟨18238308125413336685085809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12158872083608891123390539 18238308125413336685085809)
            ·
              refine ⟨13678731094060002513814357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18238308125413336685085809 13678731094060002513814357)
              ·
                refine ⟨80148815004257827229381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13678731094060002513814357 80148815004257827229381)
                ·
                  rfl

theorem cell23_4214410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 9].length) (baseStart_4214410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214410 prefixEnd_4214410 := by exact prefixLift 4214410
  have htrace : WordTrace (prefixWord ++ tailWord_4214410) baseStart_4214410 baseEnd_4214410 := by
    simpa [prefixWord, tailWord_4214410, baseEnd_4214410] using wordTrace_append hprefix tailTrace_4214410
  have hstable : (prefixWord ++ tailWord_4214410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214410).length < 2 ^ (prefixWord ++ tailWord_4214410).sum := by decide
  have hdescent : baseEnd_4214410 < baseStart_4214410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214431 : List Nat := [1, 1, 2, 7, 1, 1, 2, 2, 2, 4]
def baseStart_4214431 : Nat := 118140960795 + 4214431 * 2 ^ 59
def prefixEnd_4214431 : Nat := 4983230072969 + 3 ^ 40 * 4214431 * 2
def baseEnd_4214431 : Nat := 721342929402901917676897

theorem tailTrace_4214431 : CollatzResearch.WordTrace tailWord_4214431 prefixEnd_4214431 721342929402901917676897 := by
  unfold tailWord_4214431
  simp only [CollatzResearch.WordTrace]
  refine ⟨153712926594843729356291147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102475284396562486237527431 153712926594843729356291147)
  ·
    refine ⟨230569389892265594034436721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153712926594843729356291147 230569389892265594034436721)
    ·
      refine ⟨172927042419199195525827541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230569389892265594034436721 172927042419199195525827541)
      ·
        refine ⟨4052977556699981145136583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 172927042419199195525827541 4052977556699981145136583)
        ·
          refine ⟨6079466335049971717704875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4052977556699981145136583 6079466335049971717704875)
          ·
            refine ⟨9119199502574957576557313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6079466335049971717704875 9119199502574957576557313)
            ·
              refine ⟨6839399626931218182417985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9119199502574957576557313 6839399626931218182417985)
              ·
                refine ⟨5129549720198413636813489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6839399626931218182417985 5129549720198413636813489)
                ·
                  refine ⟨3847162290148810227610117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5129549720198413636813489 3847162290148810227610117)
                  ·
                    refine ⟨721342929402901917676897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3847162290148810227610117 721342929402901917676897)
                    ·
                      rfl

theorem cell23_4214431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 4].length) (baseStart_4214431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214431 prefixEnd_4214431 := by exact prefixLift 4214431
  have htrace : WordTrace (prefixWord ++ tailWord_4214431) baseStart_4214431 baseEnd_4214431 := by
    simpa [prefixWord, tailWord_4214431, baseEnd_4214431] using wordTrace_append hprefix tailTrace_4214431
  have hstable : (prefixWord ++ tailWord_4214431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214431).length < 2 ^ (prefixWord ++ tailWord_4214431).sum := by decide
  have hdescent : baseEnd_4214431 < baseStart_4214431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214437 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 4, 1, 3]
def baseStart_4214437 : Nat := 118140960795 + 4214437 * 2 ^ 59
def prefixEnd_4214437 : Nat := 4983230072969 + 3 ^ 40 * 4214437 * 2
def baseEnd_4214437 : Nat := 2164031869092632729555663

theorem tailTrace_4214437 : CollatzResearch.WordTrace tailWord_4214437 prefixEnd_4214437 2164031869092632729555663 := by
  unfold tailWord_4214437
  simp only [CollatzResearch.WordTrace]
  refine ⟨153713145432821992381009565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102475430288547994920673043 153713145432821992381009565)
  ·
    refine ⟨57642429537308247142878587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153713145432821992381009565 57642429537308247142878587)
    ·
      refine ⟨86463644305962370714317881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57642429537308247142878587 86463644305962370714317881)
      ·
        refine ⟨64847733229471778035738411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86463644305962370714317881 64847733229471778035738411)
        ·
          refine ⟨97271599844207667053607617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64847733229471778035738411 97271599844207667053607617)
          ·
            refine ⟨72953699883155750290205713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97271599844207667053607617 72953699883155750290205713)
            ·
              refine ⟨54715274912366812717654285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72953699883155750290205713 54715274912366812717654285)
              ·
                refine ⟨20518228092137554769120357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54715274912366812717654285 20518228092137554769120357)
                ·
                  refine ⟨3847167767275791519210067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20518228092137554769120357 3847167767275791519210067)
                  ·
                    refine ⟨5770751650913687278815101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3847167767275791519210067 5770751650913687278815101)
                    ·
                      refine ⟨2164031869092632729555663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5770751650913687278815101 2164031869092632729555663)
                      ·
                        rfl

theorem cell23_4214437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_4214437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214437 prefixEnd_4214437 := by exact prefixLift 4214437
  have htrace : WordTrace (prefixWord ++ tailWord_4214437) baseStart_4214437 baseEnd_4214437 := by
    simpa [prefixWord, tailWord_4214437, baseEnd_4214437] using wordTrace_append hprefix tailTrace_4214437
  have hstable : (prefixWord ++ tailWord_4214437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214437).length < 2 ^ (prefixWord ++ tailWord_4214437).sum := by decide
  have hdescent : baseEnd_4214437 < baseStart_4214437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214447 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 5, 3, 2]
def baseStart_4214447 : Nat := 118140960795 + 4214447 * 2 ^ 59
def prefixEnd_4214447 : Nat := 4983230072969 + 3 ^ 40 * 4214447 * 2
def baseEnd_4214447 : Nat := 2164037003899177690430617

theorem tailTrace_4214447 : CollatzResearch.WordTrace tailWord_4214447 prefixEnd_4214447 2164037003899177690430617 := by
  unfold tailWord_4214447
  simp only [CollatzResearch.WordTrace]
  refine ⟨153713510162785764088873595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102475673441857176059249063 153713510162785764088873595)
  ·
    refine ⟨230570265244178646133310393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153713510162785764088873595 230570265244178646133310393)
    ·
      refine ⟨172927698933133984599982795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230570265244178646133310393 172927698933133984599982795)
      ·
        refine ⟨259391548399700976899974193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172927698933133984599982795 259391548399700976899974193)
        ·
          refine ⟨194543661299775732674980645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 259391548399700976899974193 194543661299775732674980645)
          ·
            refine ⟨36476936493707949876558871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 194543661299775732674980645 36476936493707949876558871)
            ·
              refine ⟨54715404740561924814838307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36476936493707949876558871 54715404740561924814838307)
              ·
                refine ⟨82073107110842887222257461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54715404740561924814838307 82073107110842887222257461)
                ·
                  refine ⟨7694353791641520677086637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 82073107110842887222257461 7694353791641520677086637)
                  ·
                    refine ⟨2885382671865570253907489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7694353791641520677086637 2885382671865570253907489)
                    ·
                      refine ⟨2164037003899177690430617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2885382671865570253907489 2164037003899177690430617)
                      ·
                        rfl

theorem cell23_4214447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 3, 2].length) (baseStart_4214447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214447 prefixEnd_4214447 := by exact prefixLift 4214447
  have htrace : WordTrace (prefixWord ++ tailWord_4214447) baseStart_4214447 baseEnd_4214447 := by
    simpa [prefixWord, tailWord_4214447, baseEnd_4214447] using wordTrace_append hprefix tailTrace_4214447
  have hstable : (prefixWord ++ tailWord_4214447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214447).length < 2 ^ (prefixWord ++ tailWord_4214447).sum := by decide
  have hdescent : baseEnd_4214447 < baseStart_4214447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214464 : List Nat := [2, 1, 1, 2, 4, 1, 2, 4, 1, 3, 2]
def baseStart_4214464 : Nat := 118140960795 + 4214464 * 2 ^ 59
def prefixEnd_4214464 : Nat := 4983230072969 + 3 ^ 40 * 4214464 * 2
def baseEnd_4214464 : Nat := 2164045733070304123918039

theorem tailTrace_4214464 : CollatzResearch.WordTrace tailWord_4214464 prefixEnd_4214464 2164045733070304123918039 := by
  unfold tailWord_4214464
  simp only [CollatzResearch.WordTrace]
  refine ⟨76857065101862087996121223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102476086802482783994828297 76857065101862087996121223)
  ·
    refine ⟨115285597652793131994181835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76857065101862087996121223 115285597652793131994181835)
    ·
      refine ⟨172928396479189697991272753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115285597652793131994181835 172928396479189697991272753)
      ·
        refine ⟨129696297359392273493454565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172928396479189697991272753 129696297359392273493454565)
        ·
          refine ⟨24318055754886051280022731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129696297359392273493454565 24318055754886051280022731)
          ·
            refine ⟨36477083632329076920034097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24318055754886051280022731 36477083632329076920034097)
            ·
              refine ⟨27357812724246807690025573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36477083632329076920034097 27357812724246807690025573)
              ·
                refine ⟨5129589885796276441879795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27357812724246807690025573 5129589885796276441879795)
                ·
                  refine ⟨7694384828694414662819693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5129589885796276441879795 7694384828694414662819693)
                  ·
                    refine ⟨2885394310760405498557385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7694384828694414662819693 2885394310760405498557385)
                    ·
                      refine ⟨2164045733070304123918039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2885394310760405498557385 2164045733070304123918039)
                      ·
                        rfl

theorem cell23_4214464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 1, 3, 2].length) (baseStart_4214464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214464 prefixEnd_4214464 := by exact prefixLift 4214464
  have htrace : WordTrace (prefixWord ++ tailWord_4214464) baseStart_4214464 baseEnd_4214464 := by
    simpa [prefixWord, tailWord_4214464, baseEnd_4214464] using wordTrace_append hprefix tailTrace_4214464
  have hstable : (prefixWord ++ tailWord_4214464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214464).length < 2 ^ (prefixWord ++ tailWord_4214464).sum := by decide
  have hdescent : baseEnd_4214464 < baseStart_4214464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214480 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 3]
def baseStart_4214480 : Nat := 118140960795 + 4214480 * 2 ^ 59
def prefixEnd_4214480 : Nat := 4983230072969 + 3 ^ 40 * 4214480 * 2
def baseEnd_4214480 : Nat := 2164053948760776061317965

theorem tailTrace_4214480 : CollatzResearch.WordTrace tailWord_4214480 prefixEnd_4214480 2164053948760776061317965 := by
  unfold tailWord_4214480
  simp only [CollatzResearch.WordTrace]
  refine ⟨76857356885833105362412447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102476475847777473816549929 76857356885833105362412447)
  ·
    refine ⟨115286035328749658043618671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76857356885833105362412447 115286035328749658043618671)
    ·
      refine ⟨172929052993124487065428007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115286035328749658043618671 172929052993124487065428007)
      ·
        refine ⟨259393579489686730598142011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172929052993124487065428007 259393579489686730598142011)
        ·
          refine ⟨389090369234530095897213017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259393579489686730598142011 389090369234530095897213017)
          ·
            refine ⟨291817776925897571922909763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 389090369234530095897213017 291817776925897571922909763)
            ·
              refine ⟨437726665388846357884364645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 291817776925897571922909763 437726665388846357884364645)
              ·
                refine ⟨82073749760408692103318371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 437726665388846357884364645 82073749760408692103318371)
                ·
                  refine ⟨123110624640613038154977557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82073749760408692103318371 123110624640613038154977557)
                  ·
                    refine ⟨5770810530028736163514573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 123110624640613038154977557 5770810530028736163514573)
                    ·
                      refine ⟨2164053948760776061317965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5770810530028736163514573 2164053948760776061317965)
                      ·
                        rfl

theorem cell23_4214480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 3].length) (baseStart_4214480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214480 prefixEnd_4214480 := by exact prefixLift 4214480
  have htrace : WordTrace (prefixWord ++ tailWord_4214480) baseStart_4214480 baseEnd_4214480 := by
    simpa [prefixWord, tailWord_4214480, baseEnd_4214480] using wordTrace_append hprefix tailTrace_4214480
  have hstable : (prefixWord ++ tailWord_4214480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214480).length < 2 ^ (prefixWord ++ tailWord_4214480).sum := by decide
  have hdescent : baseEnd_4214480 < baseStart_4214480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214481 : List Nat := [1, 2, 2, 1, 2, 4, 4, 1, 1, 3, 2]
def baseStart_4214481 : Nat := 118140960795 + 4214481 * 2 ^ 59
def prefixEnd_4214481 : Nat := 4983230072969 + 3 ^ 40 * 4214481 * 2
def baseEnd_4214481 : Nat := 2164054462241430557405461

theorem tailTrace_4214481 : CollatzResearch.WordTrace tailWord_4214481 prefixEnd_4214481 2164054462241430557405461 := by
  unfold tailWord_4214481
  simp only [CollatzResearch.WordTrace]
  refine ⟨153714750244662587895611297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102476500163108391930407531 153714750244662587895611297)
  ·
    refine ⟨115286062683496940921708473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153714750244662587895611297 115286062683496940921708473)
    ·
      refine ⟨86464547012622705691281355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115286062683496940921708473 86464547012622705691281355)
      ·
        refine ⟨129696820518934058536922033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86464547012622705691281355 129696820518934058536922033)
        ·
          refine ⟨97272615389200543902691525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129696820518934058536922033 97272615389200543902691525)
          ·
            refine ⟨18238615385475101981754661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 97272615389200543902691525 18238615385475101981754661)
            ·
              refine ⟨3419740384776581621578999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18238615385475101981754661 3419740384776581621578999)
              ·
                refine ⟨5129610577164872432368499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3419740384776581621578999 5129610577164872432368499)
                ·
                  refine ⟨7694415865747308648552749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5129610577164872432368499 7694415865747308648552749)
                  ·
                    refine ⟨2885405949655240743207281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7694415865747308648552749 2885405949655240743207281)
                    ·
                      refine ⟨2164054462241430557405461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2885405949655240743207281 2164054462241430557405461)
                      ·
                        rfl

theorem cell23_4214481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 1, 3, 2].length) (baseStart_4214481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214481 prefixEnd_4214481 := by exact prefixLift 4214481
  have htrace : WordTrace (prefixWord ++ tailWord_4214481) baseStart_4214481 baseEnd_4214481 := by
    simpa [prefixWord, tailWord_4214481, baseEnd_4214481] using wordTrace_append hprefix tailTrace_4214481
  have hstable : (prefixWord ++ tailWord_4214481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214481).length < 2 ^ (prefixWord ++ tailWord_4214481).sum := by decide
  have hdescent : baseEnd_4214481 < baseStart_4214481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214537 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 1, 7, 2]
def baseStart_4214537 : Nat := 118140960795 + 4214537 * 2 ^ 59
def prefixEnd_4214537 : Nat := 4983230072969 + 3 ^ 40 * 4214537 * 2
def baseEnd_4214537 : Nat := 2164083217158082338305203

theorem tailTrace_4214537 : CollatzResearch.WordTrace tailWord_4214537 prefixEnd_4214537 2164083217158082338305203 := by
  unfold tailWord_4214537
  simp only [CollatzResearch.WordTrace]
  refine ⟨153716792732459709459649865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102477861821639806306433243 153716792732459709459649865)
  ·
    refine ⟨115287594549344782094737399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153716792732459709459649865 115287594549344782094737399)
    ·
      refine ⟨172931391824017173142106099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115287594549344782094737399 172931391824017173142106099)
      ·
        refine ⟨259397087736025759713159149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172931391824017173142106099 259397087736025759713159149)
        ·
          refine ⟨97273907901009659892434681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259397087736025759713159149 97273907901009659892434681)
          ·
            refine ⟨72955430925757244919326011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97273907901009659892434681 72955430925757244919326011)
            ·
              refine ⟨109433146388635867378989017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72955430925757244919326011 109433146388635867378989017)
              ·
                refine ⟨82074859791476900534241763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109433146388635867378989017 82074859791476900534241763)
                ·
                  refine ⟨123112289687215350801362645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82074859791476900534241763 123112289687215350801362645)
                  ·
                    refine ⟨2885444289544109784406937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 123112289687215350801362645 2885444289544109784406937)
                    ·
                      refine ⟨2164083217158082338305203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2885444289544109784406937 2164083217158082338305203)
                      ·
                        rfl

theorem cell23_4214537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 7, 2].length) (baseStart_4214537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214537 prefixEnd_4214537 := by exact prefixLift 4214537
  have htrace : WordTrace (prefixWord ++ tailWord_4214537) baseStart_4214537 baseEnd_4214537 := by
    simpa [prefixWord, tailWord_4214537, baseEnd_4214537] using wordTrace_append hprefix tailTrace_4214537
  have hstable : (prefixWord ++ tailWord_4214537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214537).length < 2 ^ (prefixWord ++ tailWord_4214537).sum := by decide
  have hdescent : baseEnd_4214537 < baseStart_4214537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214551 : List Nat := [1, 1, 3, 4, 2, 2, 3, 2, 5]
def baseStart_4214551 : Nat := 118140960795 + 4214551 * 2 ^ 59
def prefixEnd_4214551 : Nat := 4983230072969 + 3 ^ 40 * 4214551 * 2
def baseEnd_4214551 : Nat := 240454489543027253725571

theorem tailTrace_4214551 : CollatzResearch.WordTrace tailWord_4214551 prefixEnd_4214551 240454489543027253725571 := by
  unfold tailWord_4214551
  simp only [CollatzResearch.WordTrace]
  refine ⟨153717303354408989850659507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102478202236272659900439671 153717303354408989850659507)
  ·
    refine ⟨230575955031613484775989261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153717303354408989850659507 230575955031613484775989261)
    ·
      refine ⟨86465983136855056790995973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230575955031613484775989261 86465983136855056790995973)
      ·
        refine ⟨16212371838160323148311745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86465983136855056790995973 16212371838160323148311745)
        ·
          refine ⟨12159278878620242361233809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16212371838160323148311745 12159278878620242361233809)
          ·
            refine ⟨9119459158965181770925357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12159278878620242361233809 9119459158965181770925357)
            ·
              refine ⟨3419797184611943164097009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9119459158965181770925357 3419797184611943164097009)
              ·
                refine ⟨2564847888458957373072757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3419797184611943164097009 2564847888458957373072757)
                ·
                  refine ⟨240454489543027253725571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2564847888458957373072757 240454489543027253725571)
                  ·
                    rfl

theorem cell23_4214551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 5].length) (baseStart_4214551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214551 prefixEnd_4214551 := by exact prefixLift 4214551
  have htrace : WordTrace (prefixWord ++ tailWord_4214551) baseStart_4214551 baseEnd_4214551 := by
    simpa [prefixWord, tailWord_4214551, baseEnd_4214551] using wordTrace_append hprefix tailTrace_4214551
  have hstable : (prefixWord ++ tailWord_4214551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214551).length < 2 ^ (prefixWord ++ tailWord_4214551).sum := by decide
  have hdescent : baseEnd_4214551 < baseStart_4214551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214584 : List Nat := [2, 1, 2, 1, 3, 4, 2, 1, 2, 1, 4]
def baseStart_4214584 : Nat := 118140960795 + 4214584 * 2 ^ 59
def prefixEnd_4214584 : Nat := 4983230072969 + 3 ^ 40 * 4214584 * 2
def baseEnd_4214584 : Nat := 2164107350748843654417487

theorem tailTrace_4214584 : CollatzResearch.WordTrace tailWord_4214584 prefixEnd_4214584 2164107350748843654417487 := by
  unfold tailWord_4214584
  simp only [CollatzResearch.WordTrace]
  refine ⟨76859253481644718243305403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102479004642192957657740537 76859253481644718243305403)
  ·
    refine ⟨115288880222467077364958105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76859253481644718243305403 115288880222467077364958105)
    ·
      refine ⟨86466660166850308023718579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115288880222467077364958105 86466660166850308023718579)
      ·
        refine ⟨129699990250275462035577869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86466660166850308023718579 129699990250275462035577869)
        ·
          refine ⟨48637496343853298263341701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129699990250275462035577869 48637496343853298263341701)
          ·
            refine ⟨9119530564472493424376569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48637496343853298263341701 9119530564472493424376569)
            ·
              refine ⟨6839647923354370068282427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9119530564472493424376569 6839647923354370068282427)
              ·
                refine ⟨10259471885031555102423641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6839647923354370068282427 10259471885031555102423641)
                ·
                  refine ⟨7694603913773666326817731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10259471885031555102423641 7694603913773666326817731)
                  ·
                    refine ⟨11541905870660499490226597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7694603913773666326817731 11541905870660499490226597)
                    ·
                      refine ⟨2164107350748843654417487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11541905870660499490226597 2164107350748843654417487)
                      ·
                        rfl

theorem cell23_4214584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_4214584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214584 prefixEnd_4214584 := by exact prefixLift 4214584
  have htrace : WordTrace (prefixWord ++ tailWord_4214584) baseStart_4214584 baseEnd_4214584 := by
    simpa [prefixWord, tailWord_4214584, baseEnd_4214584] using wordTrace_append hprefix tailTrace_4214584
  have hstable : (prefixWord ++ tailWord_4214584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214584).length < 2 ^ (prefixWord ++ tailWord_4214584).sum := by decide
  have hdescent : baseEnd_4214584 < baseStart_4214584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214638 : List Nat := [4, 1, 2, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_4214638 : Nat := 118140960795 + 4214638 * 2 ^ 59
def prefixEnd_4214638 : Nat := 4983230072969 + 3 ^ 40 * 4214638 * 2
def baseEnd_4214638 : Nat := 2164135078704186443142239

theorem tailTrace_4214638 : CollatzResearch.WordTrace tailWord_4214638 prefixEnd_4214638 2164135078704186443142239 := by
  unfold tailWord_4214638
  simp only [CollatzResearch.WordTrace]
  refine ⟨19215059563136725463634571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102480317670062535806051045 19215059563136725463634571)
  ·
    refine ⟨28822589344705088195451857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19215059563136725463634571 28822589344705088195451857)
    ·
      refine ⟨21616942008528816146588893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28822589344705088195451857 21616942008528816146588893)
      ·
        refine ⟨8106353253198306054970835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21616942008528816146588893 8106353253198306054970835)
        ·
          refine ⟨12159529879797459082456253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8106353253198306054970835 12159529879797459082456253)
          ·
            refine ⟨4559823704924047155921095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12159529879797459082456253 4559823704924047155921095)
            ·
              refine ⟨6839735557386070733881643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4559823704924047155921095 6839735557386070733881643)
              ·
                refine ⟨10259603336079106100822465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6839735557386070733881643 10259603336079106100822465)
                ·
                  refine ⟨7694702502059329575616849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10259603336079106100822465 7694702502059329575616849)
                  ·
                    refine ⟨5771026876544497181712637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7694702502059329575616849 5771026876544497181712637)
                    ·
                      refine ⟨2164135078704186443142239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5771026876544497181712637 2164135078704186443142239)
                      ·
                        rfl

theorem cell23_4214638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_4214638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214638 prefixEnd_4214638 := by exact prefixLift 4214638
  have htrace : WordTrace (prefixWord ++ tailWord_4214638) baseStart_4214638 baseEnd_4214638 := by
    simpa [prefixWord, tailWord_4214638, baseEnd_4214638] using wordTrace_append hprefix tailTrace_4214638
  have hstable : (prefixWord ++ tailWord_4214638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214638).length < 2 ^ (prefixWord ++ tailWord_4214638).sum := by decide
  have hdescent : baseEnd_4214638 < baseStart_4214638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214727 : List Nat := [1, 1, 4, 1, 1, 2, 1, 3, 2, 7]
def baseStart_4214727 : Nat := 118140960795 + 4214727 * 2 ^ 59
def prefixEnd_4214727 : Nat := 4983230072969 + 3 ^ 40 * 4214727 * 2
def baseEnd_4214727 : Nat := 721393592827478864976443

theorem tailTrace_4214727 : CollatzResearch.WordTrace tailWord_4214727 prefixEnd_4214727 721393592827478864976443 := by
  unfold tailWord_4214727
  simp only [CollatzResearch.WordTrace]
  refine ⟨153723722601771371909066435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102482481734514247939377623 153723722601771371909066435)
  ·
    refine ⟨230585583902657057863599653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153723722601771371909066435 230585583902657057863599653)
    ·
      refine ⟨43234796981748198349424935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230585583902657057863599653 43234796981748198349424935)
      ·
        refine ⟨64852195472622297524137403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43234796981748198349424935 64852195472622297524137403)
        ·
          refine ⟨97278293208933446286206105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64852195472622297524137403 97278293208933446286206105)
          ·
            refine ⟨72958719906700084714654579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97278293208933446286206105 72958719906700084714654579)
            ·
              refine ⟨109438079860050127071981869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72958719906700084714654579 109438079860050127071981869)
              ·
                refine ⟨41039279947518797651993201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109438079860050127071981869 41039279947518797651993201)
                ·
                  refine ⟨30779459960639098238994901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41039279947518797651993201 30779459960639098238994901)
                  ·
                    refine ⟨721393592827478864976443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30779459960639098238994901 721393592827478864976443)
                    ·
                      rfl

theorem cell23_4214727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_4214727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214727 prefixEnd_4214727 := by exact prefixLift 4214727
  have htrace : WordTrace (prefixWord ++ tailWord_4214727) baseStart_4214727 baseEnd_4214727 := by
    simpa [prefixWord, tailWord_4214727, baseEnd_4214727] using wordTrace_append hprefix tailTrace_4214727
  have hstable : (prefixWord ++ tailWord_4214727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214727).length < 2 ^ (prefixWord ++ tailWord_4214727).sum := by decide
  have hdescent : baseEnd_4214727 < baseStart_4214727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214737 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 1, 4, 5]
def baseStart_4214737 : Nat := 118140960795 + 4214737 * 2 ^ 59
def prefixEnd_4214737 : Nat := 4983230072969 + 3 ^ 40 * 4214737 * 2
def baseEnd_4214737 : Nat := 2164185913288981555804283

theorem tailTrace_4214737 : CollatzResearch.WordTrace tailWord_4214737 prefixEnd_4214737 2164185913288981555804283 := by
  unfold tailWord_4214737
  simp only [CollatzResearch.WordTrace]
  refine ⟨153724087331735143616930465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102482724887823429077953643 153724087331735143616930465)
  ·
    refine ⟨115293065498801357712697849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153724087331735143616930465 115293065498801357712697849)
    ·
      refine ⟨86469799124101018284523387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115293065498801357712697849 86469799124101018284523387)
      ·
        refine ⟨129704698686151527426785081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86469799124101018284523387 129704698686151527426785081)
        ·
          refine ⟨97278524014613645570088811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129704698686151527426785081 97278524014613645570088811)
          ·
            refine ⟨145917786021920468355133217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97278524014613645570088811 145917786021920468355133217)
            ·
              refine ⟨109438339516440351266349913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145917786021920468355133217 109438339516440351266349913)
              ·
                refine ⟨82078754637330263449762435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109438339516440351266349913 82078754637330263449762435)
                ·
                  refine ⟨123118131955995395174643653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82078754637330263449762435 123118131955995395174643653)
                  ·
                    refine ⟨23084649741749136595245685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 123118131955995395174643653 23084649741749136595245685)
                    ·
                      refine ⟨2164185913288981555804283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23084649741749136595245685 2164185913288981555804283)
                      ·
                        rfl

theorem cell23_4214737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_4214737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214737 prefixEnd_4214737 := by exact prefixLift 4214737
  have htrace : WordTrace (prefixWord ++ tailWord_4214737) baseStart_4214737 baseEnd_4214737 := by
    simpa [prefixWord, tailWord_4214737, baseEnd_4214737] using wordTrace_append hprefix tailTrace_4214737
  have hstable : (prefixWord ++ tailWord_4214737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214737).length < 2 ^ (prefixWord ++ tailWord_4214737).sum := by decide
  have hdescent : baseEnd_4214737 < baseStart_4214737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214742 : List Nat := [5, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_4214742 : Nat := 118140960795 + 4214742 * 2 ^ 59
def prefixEnd_4214742 : Nat := 4983230072969 + 3 ^ 40 * 4214742 * 2
def baseEnd_4214742 : Nat := 2164188480692254036241761

theorem tailTrace_4214742 : CollatzResearch.WordTrace tailWord_4214742 prefixEnd_4214742 2164188480692254036241761 := by
  unfold tailWord_4214742
  simp only [CollatzResearch.WordTrace]
  refine ⟨9607766856044814341928905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102482846464478019647241653 9607766856044814341928905)
  ·
    refine ⟨7205825142033610756446679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9607766856044814341928905 7205825142033610756446679)
    ·
      refine ⟨10808737713050416134670019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7205825142033610756446679 10808737713050416134670019)
      ·
        refine ⟨16213106569575624202005029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10808737713050416134670019 16213106569575624202005029)
        ·
          refine ⟨3039957481795429537875943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16213106569575624202005029 3039957481795429537875943)
          ·
            refine ⟨4559936222693144306813915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3039957481795429537875943 4559936222693144306813915)
            ·
              refine ⟨6839904334039716460220873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4559936222693144306813915 6839904334039716460220873)
              ·
                refine ⟨5129928250529787345165655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6839904334039716460220873 5129928250529787345165655)
                ·
                  refine ⟨7694892375794681017748483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5129928250529787345165655 7694892375794681017748483)
                  ·
                    refine ⟨11542338563692021526622725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7694892375794681017748483 11542338563692021526622725)
                    ·
                      refine ⟨2164188480692254036241761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11542338563692021526622725 2164188480692254036241761)
                      ·
                        rfl

theorem cell23_4214742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_4214742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214742 prefixEnd_4214742 := by exact prefixLift 4214742
  have htrace : WordTrace (prefixWord ++ tailWord_4214742) baseStart_4214742 baseEnd_4214742 := by
    simpa [prefixWord, tailWord_4214742, baseEnd_4214742] using wordTrace_append hprefix tailTrace_4214742
  have hstable : (prefixWord ++ tailWord_4214742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214742).length < 2 ^ (prefixWord ++ tailWord_4214742).sum := by decide
  have hdescent : baseEnd_4214742 < baseStart_4214742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214745 : List Nat := [1, 2, 1, 2, 7, 1, 1, 2, 1, 2, 3]
def baseStart_4214745 : Nat := 118140960795 + 4214745 * 2 ^ 59
def prefixEnd_4214745 : Nat := 4983230072969 + 3 ^ 40 * 4214745 * 2
def baseEnd_4214745 : Nat := 2164190021134217524504247

theorem tailTrace_4214745 : CollatzResearch.WordTrace tailWord_4214745 prefixEnd_4214745 2164190021134217524504247 := by
  unfold tailWord_4214745
  simp only [CollatzResearch.WordTrace]
  refine ⟨153724379115706160983221689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102482919410470773988814459 153724379115706160983221689)
  ·
    refine ⟨115293284336779620737416267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153724379115706160983221689 115293284336779620737416267)
    ·
      refine ⟨172939926505169431106124401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 115293284336779620737416267 172939926505169431106124401)
      ·
        refine ⟨129704944878877073329593301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172939926505169431106124401 129704944878877073329593301)
        ·
          refine ⟨3039959645598681406162343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 129704944878877073329593301 3039959645598681406162343)
          ·
            refine ⟨4559939468398022109243515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3039959645598681406162343 4559939468398022109243515)
            ·
              refine ⟨6839909202597033163865273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4559939468398022109243515 6839909202597033163865273)
              ·
                refine ⟨5129931901947774872898955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6839909202597033163865273 5129931901947774872898955)
                ·
                  refine ⟨7694897852921662309348433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5129931901947774872898955 7694897852921662309348433)
                  ·
                    refine ⟨5771173389691246732011325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7694897852921662309348433 5771173389691246732011325)
                    ·
                      refine ⟨2164190021134217524504247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5771173389691246732011325 2164190021134217524504247)
                      ·
                        rfl

theorem cell23_4214745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 1, 2, 3].length) (baseStart_4214745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214745 prefixEnd_4214745 := by exact prefixLift 4214745
  have htrace : WordTrace (prefixWord ++ tailWord_4214745) baseStart_4214745 baseEnd_4214745 := by
    simpa [prefixWord, tailWord_4214745, baseEnd_4214745] using wordTrace_append hprefix tailTrace_4214745
  have hstable : (prefixWord ++ tailWord_4214745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214745).length < 2 ^ (prefixWord ++ tailWord_4214745).sum := by decide
  have hdescent : baseEnd_4214745 < baseStart_4214745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214787 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 11]
def baseStart_4214787 : Nat := 118140960795 + 4214787 * 2 ^ 59
def prefixEnd_4214787 : Nat := 4983230072969 + 3 ^ 40 * 4214787 * 2
def baseEnd_4214787 : Nat := 240467954146856262242117

theorem tailTrace_4214787 : CollatzResearch.WordTrace tailWord_4214787 prefixEnd_4214787 240467954146856262242117 := by
  unfold tailWord_4214787
  simp only [CollatzResearch.WordTrace]
  refine ⟨153725910981554002156250615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102483940654369334770833743 153725910981554002156250615)
  ·
    refine ⟨230588866472331003234375923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153725910981554002156250615 230588866472331003234375923)
    ·
      refine ⟨345883299708496504851563885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230588866472331003234375923 345883299708496504851563885)
      ·
        refine ⟨129706237390686189319336457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 345883299708496504851563885 129706237390686189319336457)
        ·
          refine ⟨97279678043014641989502343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129706237390686189319336457 97279678043014641989502343)
          ·
            refine ⟨145919517064521962984253515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97279678043014641989502343 145919517064521962984253515)
            ·
              refine ⟨218879275596782944476380273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145919517064521962984253515 218879275596782944476380273)
              ·
                refine ⟨164159456697587208357285205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218879275596782944476380273 164159456697587208357285205)
                ·
                  refine ⟨240467954146856262242117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 164159456697587208357285205 240467954146856262242117)
                  ·
                    rfl

theorem cell23_4214787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 11].length) (baseStart_4214787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214787 prefixEnd_4214787 := by exact prefixLift 4214787
  have htrace : WordTrace (prefixWord ++ tailWord_4214787) baseStart_4214787 baseEnd_4214787 := by
    simpa [prefixWord, tailWord_4214787, baseEnd_4214787] using wordTrace_append hprefix tailTrace_4214787
  have hstable : (prefixWord ++ tailWord_4214787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214787).length < 2 ^ (prefixWord ++ tailWord_4214787).sum := by decide
  have hdescent : baseEnd_4214787 < baseStart_4214787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214798 : List Nat := [4, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2]
def baseStart_4214798 : Nat := 118140960795 + 4214798 * 2 ^ 59
def prefixEnd_4214798 : Nat := 4983230072969 + 3 ^ 40 * 4214798 * 2
def baseEnd_4214798 : Nat := 2164217235608905817141503

theorem tailTrace_4214798 : CollatzResearch.WordTrace tailWord_4214798 prefixEnd_4214798 2164217235608905817141503 := by
  unfold tailWord_4214798
  simp only [CollatzResearch.WordTrace]
  refine ⟨19215789023064268879362631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102484208123009434023267365 19215789023064268879362631)
  ·
    refine ⟨28823683534596403319043947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19215789023064268879362631 28823683534596403319043947)
    ·
      refine ⟨43235525301894604978565921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28823683534596403319043947 43235525301894604978565921)
      ·
        refine ⟨32426643976420953733924441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43235525301894604978565921 32426643976420953733924441)
        ·
          refine ⟨24319982982315715300443331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32426643976420953733924441 24319982982315715300443331)
          ·
            refine ⟨36479974473473572950664997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24319982982315715300443331 36479974473473572950664997)
            ·
              refine ⟨6839995213776294928249687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36479974473473572950664997 6839995213776294928249687)
              ·
                refine ⟨10259992820664442392374531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6839995213776294928249687 10259992820664442392374531)
                ·
                  refine ⟨15389989230996663588561797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10259992820664442392374531 15389989230996663588561797)
                  ·
                    refine ⟨2885622980811874422855337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15389989230996663588561797 2885622980811874422855337)
                    ·
                      refine ⟨2164217235608905817141503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2885622980811874422855337 2164217235608905817141503)
                      ·
                        rfl

theorem cell23_4214798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_4214798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214798 prefixEnd_4214798 := by exact prefixLift 4214798
  have htrace : WordTrace (prefixWord ++ tailWord_4214798) baseStart_4214798 baseEnd_4214798 := by
    simpa [prefixWord, tailWord_4214798, baseEnd_4214798] using wordTrace_append hprefix tailTrace_4214798
  have hstable : (prefixWord ++ tailWord_4214798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214798).length < 2 ^ (prefixWord ++ tailWord_4214798).sum := by decide
  have hdescent : baseEnd_4214798 < baseStart_4214798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214821 : List Nat := [1, 3, 1, 2, 2, 3, 1, 5, 5]
def baseStart_4214821 : Nat := 118140960795 + 4214821 * 2 ^ 59
def prefixEnd_4214821 : Nat := 4983230072969 + 3 ^ 40 * 4214821 * 2
def baseEnd_4214821 : Nat := 240469893962662136350433

theorem tailTrace_4214821 : CollatzResearch.WordTrace tailWord_4214821 prefixEnd_4214821 240469893962662136350433 := by
  unfold tailWord_4214821
  simp only [CollatzResearch.WordTrace]
  refine ⟨153727151063430825962988317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102484767375620550641992211 153727151063430825962988317)
  ·
    refine ⟨57647681648786559736120619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153727151063430825962988317 57647681648786559736120619)
    ·
      refine ⟨86471522473179839604180929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57647681648786559736120619 86471522473179839604180929)
      ·
        refine ⟨64853641854884879703135697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86471522473179839604180929 64853641854884879703135697)
        ·
          refine ⟨48640231391163659777351773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64853641854884879703135697 48640231391163659777351773)
          ·
            refine ⟨18240086771686372416506915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48640231391163659777351773 18240086771686372416506915)
            ·
              refine ⟨27360130157529558624760373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18240086771686372416506915 27360130157529558624760373)
              ·
                refine ⟨2565012202268396121071285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27360130157529558624760373 2565012202268396121071285)
                ·
                  refine ⟨240469893962662136350433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2565012202268396121071285 240469893962662136350433)
                  ·
                    rfl

theorem cell23_4214821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 5].length) (baseStart_4214821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214821 prefixEnd_4214821 := by exact prefixLift 4214821
  have htrace : WordTrace (prefixWord ++ tailWord_4214821) baseStart_4214821 baseEnd_4214821 := by
    simpa [prefixWord, tailWord_4214821, baseEnd_4214821] using wordTrace_append hprefix tailTrace_4214821
  have hstable : (prefixWord ++ tailWord_4214821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214821).length < 2 ^ (prefixWord ++ tailWord_4214821).sum := by decide
  have hdescent : baseEnd_4214821 < baseStart_4214821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214838 : List Nat := [5, 1, 2, 1, 1, 1, 1, 6, 5]
def baseStart_4214838 : Nat := 118140960795 + 4214838 * 2 ^ 59
def prefixEnd_4214838 : Nat := 4983230072969 + 3 ^ 40 * 4214838 * 2
def baseEnd_4214838 : Nat := 240470863870565073404591

theorem tailTrace_4214838 : CollatzResearch.WordTrace tailWord_4214838 prefixEnd_4214838 240470863870565073404591 := by
  unfold tailWord_4214838
  simp only [CollatzResearch.WordTrace]
  refine ⟨9607985694023077366647323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102485180736246158577571445 9607985694023077366647323)
  ·
    refine ⟨14411978541034616049970985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9607985694023077366647323 14411978541034616049970985)
    ·
      refine ⟨10808983905775962037478239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14411978541034616049970985 10808983905775962037478239)
      ·
        refine ⟨16213475858663943056217359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10808983905775962037478239 16213475858663943056217359)
        ·
          refine ⟨24320213787995914584326039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16213475858663943056217359 24320213787995914584326039)
          ·
            refine ⟨36480320681993871876489059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24320213787995914584326039 36480320681993871876489059)
            ·
              refine ⟨54720481022990807814733589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36480320681993871876489059 54720481022990807814733589)
              ·
                refine ⟨2565022547952694116315637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 54720481022990807814733589 2565022547952694116315637)
                ·
                  refine ⟨240470863870565073404591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2565022547952694116315637 240470863870565073404591)
                  ·
                    rfl

theorem cell23_4214838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_4214838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214838 prefixEnd_4214838 := by exact prefixLift 4214838
  have htrace : WordTrace (prefixWord ++ tailWord_4214838) baseStart_4214838 baseEnd_4214838 := by
    simpa [prefixWord, tailWord_4214838, baseEnd_4214838] using wordTrace_append hprefix tailTrace_4214838
  have hstable : (prefixWord ++ tailWord_4214838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214838).length < 2 ^ (prefixWord ++ tailWord_4214838).sum := by decide
  have hdescent : baseEnd_4214838 < baseStart_4214838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214844 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_4214844 : Nat := 118140960795 + 4214844 * 2 ^ 59
def prefixEnd_4214844 : Nat := 4983230072969 + 3 ^ 40 * 4214844 * 2
def baseEnd_4214844 : Nat := 2164240855719012637166291

theorem tailTrace_4214844 : CollatzResearch.WordTrace tailWord_4214844 prefixEnd_4214844 2164240855719012637166291 := by
  unfold tailWord_4214844
  simp only [CollatzResearch.WordTrace]
  refine ⟨76863994971173750445537793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102485326628231667260717057 76863994971173750445537793)
  ·
    refine ⟨57647996228380312834153345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76863994971173750445537793 57647996228380312834153345)
    ·
      refine ⟨43235997171285234625615009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57647996228380312834153345 43235997171285234625615009)
      ·
        refine ⟨32426997878463925969211257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43235997171285234625615009 32426997878463925969211257)
        ·
          refine ⟨24320248408847944476908443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32426997878463925969211257 24320248408847944476908443)
          ·
            refine ⟨36480372613271916715362665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24320248408847944476908443 36480372613271916715362665)
            ·
              refine ⟨27360279459953937536521999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36480372613271916715362665 27360279459953937536521999)
              ·
                refine ⟨41040419189930906304782999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27360279459953937536521999 41040419189930906304782999)
                ·
                  refine ⟨61560628784896359457174499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41040419189930906304782999 61560628784896359457174499)
                  ·
                    refine ⟨92340943177344539185761749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61560628784896359457174499 92340943177344539185761749)
                    ·
                      refine ⟨2164240855719012637166291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 92340943177344539185761749 2164240855719012637166291)
                      ·
                        rfl

theorem cell23_4214844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_4214844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214844 prefixEnd_4214844 := by exact prefixLift 4214844
  have htrace : WordTrace (prefixWord ++ tailWord_4214844) baseStart_4214844 baseEnd_4214844 := by
    simpa [prefixWord, tailWord_4214844, baseEnd_4214844] using wordTrace_append hprefix tailTrace_4214844
  have hstable : (prefixWord ++ tailWord_4214844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214844).length < 2 ^ (prefixWord ++ tailWord_4214844).sum := by decide
  have hdescent : baseEnd_4214844 < baseStart_4214844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214871 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 1, 6, 2]
def baseStart_4214871 : Nat := 118140960795 + 4214871 * 2 ^ 59
def prefixEnd_4214871 : Nat := 4983230072969 + 3 ^ 40 * 4214871 * 2
def baseEnd_4214871 : Nat := 2164254719696684031528667

theorem tailTrace_4214871 : CollatzResearch.WordTrace tailWord_4214871 prefixEnd_4214871 2164254719696684031528667 := by
  unfold tailWord_4214871
  simp only [CollatzResearch.WordTrace]
  refine ⟨153728974713249684502308467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102485983142166456334872311 153728974713249684502308467)
  ·
    refine ⟨230593462069874526753462701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153728974713249684502308467 230593462069874526753462701)
    ·
      refine ⟨86472548276202947532548513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 230593462069874526753462701 86472548276202947532548513)
      ·
        refine ⟨64854411207152210649411385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86472548276202947532548513 64854411207152210649411385)
        ·
          refine ⟨48640808405364157987058539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64854411207152210649411385 48640808405364157987058539)
          ·
            refine ⟨72961212608046236980587809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48640808405364157987058539 72961212608046236980587809)
            ·
              refine ⟨54720909456034677735440857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72961212608046236980587809 54720909456034677735440857)
              ·
                refine ⟨41040682092026008301580643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54720909456034677735440857 41040682092026008301580643)
                ·
                  refine ⟨61561023138039012452370965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41040682092026008301580643 61561023138039012452370965)
                  ·
                    refine ⟨2885672959595578708704889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61561023138039012452370965 2885672959595578708704889)
                    ·
                      refine ⟨2164254719696684031528667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2885672959595578708704889 2164254719696684031528667)
                      ·
                        rfl

theorem cell23_4214871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_4214871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214871 prefixEnd_4214871 := by exact prefixLift 4214871
  have htrace : WordTrace (prefixWord ++ tailWord_4214871) baseStart_4214871 baseEnd_4214871 := by
    simpa [prefixWord, tailWord_4214871, baseEnd_4214871] using wordTrace_append hprefix tailTrace_4214871
  have hstable : (prefixWord ++ tailWord_4214871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214871).length < 2 ^ (prefixWord ++ tailWord_4214871).sum := by decide
  have hdescent : baseEnd_4214871 < baseStart_4214871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214884 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_4214884 : Nat := 118140960795 + 4214884 * 2 ^ 59
def prefixEnd_4214884 : Nat := 4983230072969 + 3 ^ 40 * 4214884 * 2
def baseEnd_4214884 : Nat := 2164261394945192480666107

theorem tailTrace_4214884 : CollatzResearch.WordTrace tailWord_4214884 prefixEnd_4214884 2164261394945192480666107 := by
  unfold tailWord_4214884
  simp only [CollatzResearch.WordTrace]
  refine ⟨76864724431101293861265853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102486299241468391815021137 76864724431101293861265853)
  ·
    refine ⟨28824271661662985197974695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76864724431101293861265853 28824271661662985197974695)
    ·
      refine ⟨43236407492494477796962043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28824271661662985197974695 43236407492494477796962043)
      ·
        refine ⟨64854611238741716695443065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43236407492494477796962043 64854611238741716695443065)
        ·
          refine ⟨48640958429056287521582299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64854611238741716695443065 48640958429056287521582299)
          ·
            refine ⟨72961437643584431282373449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48640958429056287521582299 72961437643584431282373449)
            ·
              refine ⟨54721078232688323461780087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72961437643584431282373449 54721078232688323461780087)
              ·
                refine ⟨82081617349032485192670131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54721078232688323461780087 82081617349032485192670131)
                ·
                  refine ⟨123122426023548727789005197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82081617349032485192670131 123122426023548727789005197)
                  ·
                    refine ⟨46170909758830772920876949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 123122426023548727789005197 46170909758830772920876949)
                    ·
                      refine ⟨2164261394945192480666107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 46170909758830772920876949 2164261394945192480666107)
                      ·
                        rfl

theorem cell23_4214884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_4214884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214884 prefixEnd_4214884 := by exact prefixLift 4214884
  have htrace : WordTrace (prefixWord ++ tailWord_4214884) baseStart_4214884 baseEnd_4214884 := by
    simpa [prefixWord, tailWord_4214884, baseEnd_4214884] using wordTrace_append hprefix tailTrace_4214884
  have hstable : (prefixWord ++ tailWord_4214884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214884).length < 2 ^ (prefixWord ++ tailWord_4214884).sum := by decide
  have hdescent : baseEnd_4214884 < baseStart_4214884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214898 : List Nat := [3, 2, 1, 2, 2, 2, 3, 1, 3, 4]
def baseStart_4214898 : Nat := 118140960795 + 4214898 * 2 ^ 59
def prefixEnd_4214898 : Nat := 4983230072969 + 3 ^ 40 * 4214898 * 2
def baseEnd_4214898 : Nat := 721422861224785141963681

theorem tailTrace_4214898 : CollatzResearch.WordTrace tailWord_4214898 prefixEnd_4214898 721422861224785141963681 := by
  unfold tailWord_4214898
  simp only [CollatzResearch.WordTrace]
  refine ⟨38432489871037967028385337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102486639656101245409027565 38432489871037967028385337)
  ·
    refine ⟨28824367403278475271289003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38432489871037967028385337 28824367403278475271289003)
    ·
      refine ⟨43236551104917712906933505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28824367403278475271289003 43236551104917712906933505)
      ·
        refine ⟨32427413328688284680200129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43236551104917712906933505 32427413328688284680200129)
        ·
          refine ⟨24320559996516213510150097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32427413328688284680200129 24320559996516213510150097)
          ·
            refine ⟨18240419997387160132612573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24320559996516213510150097 18240419997387160132612573)
            ·
              refine ⟨6840157499020185049729715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18240419997387160132612573 6840157499020185049729715)
              ·
                refine ⟨10260236248530277574594573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6840157499020185049729715 10260236248530277574594573)
                ·
                  refine ⟨3847588593198854090472965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10260236248530277574594573 3847588593198854090472965)
                  ·
                    refine ⟨721422861224785141963681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3847588593198854090472965 721422861224785141963681)
                    ·
                      rfl

theorem cell23_4214898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_4214898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214898 prefixEnd_4214898 := by exact prefixLift 4214898
  have htrace : WordTrace (prefixWord ++ tailWord_4214898) baseStart_4214898 baseEnd_4214898 := by
    simpa [prefixWord, tailWord_4214898, baseEnd_4214898] using wordTrace_append hprefix tailTrace_4214898
  have hstable : (prefixWord ++ tailWord_4214898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214898).length < 2 ^ (prefixWord ++ tailWord_4214898).sum := by decide
  have hdescent : baseEnd_4214898 < baseStart_4214898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214971 : List Nat := [1, 1, 1, 1, 1, 2, 8, 1, 1, 6]
def baseStart_4214971 : Nat := 118140960795 + 4214971 * 2 ^ 59
def prefixEnd_4214971 : Nat := 4983230072969 + 3 ^ 40 * 4214971 * 2
def baseEnd_4214971 : Nat := 721435355920711213426069

theorem tailTrace_4214971 : CollatzResearch.WordTrace tailWord_4214971 prefixEnd_4214971 721435355920711213426069 := by
  unfold tailWord_4214971
  simp only [CollatzResearch.WordTrace]
  refine ⟨153732622012887401580948767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102488414675258267720632511 153732622012887401580948767)
  ·
    refine ⟨230598933019331102371423151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153732622012887401580948767 230598933019331102371423151)
    ·
      refine ⟨345898399528996653557134727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230598933019331102371423151 345898399528996653557134727)
      ·
        refine ⟨518847599293494980335702091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 345898399528996653557134727 518847599293494980335702091)
        ·
          refine ⟨778271398940242470503553137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518847599293494980335702091 778271398940242470503553137)
          ·
            refine ⟨583703549205181852877664853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 778271398940242470503553137 583703549205181852877664853)
            ·
              refine ⟨6840275967248224838410135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 583703549205181852877664853 6840275967248224838410135)
              ·
                refine ⟨10260413950872337257615203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6840275967248224838410135 10260413950872337257615203)
                ·
                  refine ⟨15390620926308505886422805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10260413950872337257615203 15390620926308505886422805)
                  ·
                    refine ⟨721435355920711213426069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15390620926308505886422805 721435355920711213426069)
                    ·
                      rfl

theorem cell23_4214971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 6].length) (baseStart_4214971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214971 prefixEnd_4214971 := by exact prefixLift 4214971
  have htrace : WordTrace (prefixWord ++ tailWord_4214971) baseStart_4214971 baseEnd_4214971 := by
    simpa [prefixWord, tailWord_4214971, baseEnd_4214971] using wordTrace_append hprefix tailTrace_4214971
  have hstable : (prefixWord ++ tailWord_4214971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214971).length < 2 ^ (prefixWord ++ tailWord_4214971).sum := by decide
  have hdescent : baseEnd_4214971 < baseStart_4214971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4214991 : List Nat := [1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 4]
def baseStart_4214991 : Nat := 118140960795 + 4214991 * 2 ^ 59
def prefixEnd_4214991 : Nat := 4983230072969 + 3 ^ 40 * 4214991 * 2
def baseEnd_4214991 : Nat := 2164316337375223562028115

theorem tailTrace_4214991 : CollatzResearch.WordTrace tailWord_4214991 prefixEnd_4214991 2164316337375223562028115 := by
  unfold tailWord_4214991
  simp only [CollatzResearch.WordTrace]
  refine ⟨153733351472814944996676827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102488900981876629997784551 153733351472814944996676827)
  ·
    refine ⟨230600027209222417495015241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153733351472814944996676827 230600027209222417495015241)
    ·
      refine ⟨172950020406916813121261431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230600027209222417495015241 172950020406916813121261431)
      ·
        refine ⟨259425030610375219681892147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172950020406916813121261431 259425030610375219681892147)
        ·
          refine ⟨389137545915562829522838221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259425030610375219681892147 389137545915562829522838221)
          ·
            refine ⟨145926579718336061071064333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 389137545915562829522838221 145926579718336061071064333)
            ·
              refine ⟨54722467394376022901649125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145926579718336061071064333 54722467394376022901649125)
              ·
                refine ⟨10260462636445504294059211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54722467394376022901649125 10260462636445504294059211)
                ·
                  refine ⟨15390693954668256441088817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10260462636445504294059211 15390693954668256441088817)
                  ·
                    refine ⟨11543020466001192330816613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15390693954668256441088817 11543020466001192330816613)
                    ·
                      refine ⟨2164316337375223562028115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11543020466001192330816613 2164316337375223562028115)
                      ·
                        rfl

theorem cell23_4214991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 4].length) (baseStart_4214991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4214991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4214991 prefixEnd_4214991 := by exact prefixLift 4214991
  have htrace : WordTrace (prefixWord ++ tailWord_4214991) baseStart_4214991 baseEnd_4214991 := by
    simpa [prefixWord, tailWord_4214991, baseEnd_4214991] using wordTrace_append hprefix tailTrace_4214991
  have hstable : (prefixWord ++ tailWord_4214991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4214991).length < 2 ^ (prefixWord ++ tailWord_4214991).sum := by decide
  have hdescent : baseEnd_4214991 < baseStart_4214991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4214991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215005 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 4, 4]
def baseStart_4215005 : Nat := 118140960795 + 4215005 * 2 ^ 59
def prefixEnd_4215005 : Nat := 4983230072969 + 3 ^ 40 * 4215005 * 2
def baseEnd_4215005 : Nat := 721441175368128835751017

theorem tailTrace_4215005 : CollatzResearch.WordTrace tailWord_4215005 prefixEnd_4215005 721441175368128835751017 := by
  unfold tailWord_4215005
  simp only [CollatzResearch.WordTrace]
  refine ⟨153733862094764225387686469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102489241396509483591790979 153733862094764225387686469)
  ·
    refine ⟨28825099142768292260191213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153733862094764225387686469 28825099142768292260191213)
    ·
      refine ⟨10809412178538109597571705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28825099142768292260191213 10809412178538109597571705)
      ·
        refine ⟨8107059133903582198178779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10809412178538109597571705 8107059133903582198178779)
        ·
          refine ⟨12160588700855373297268169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8107059133903582198178779 12160588700855373297268169)
          ·
            refine ⟨9120441525641529972951127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12160588700855373297268169 9120441525641529972951127)
            ·
              refine ⟨13680662288462294959426691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9120441525641529972951127 13680662288462294959426691)
              ·
                refine ⟨20520993432693442439140037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13680662288462294959426691 20520993432693442439140037)
                ·
                  refine ⟨3847686268630020457338757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20520993432693442439140037 3847686268630020457338757)
                  ·
                    refine ⟨721441175368128835751017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3847686268630020457338757 721441175368128835751017)
                    ·
                      rfl

theorem cell23_4215005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_4215005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215005 prefixEnd_4215005 := by exact prefixLift 4215005
  have htrace : WordTrace (prefixWord ++ tailWord_4215005) baseStart_4215005 baseEnd_4215005 := by
    simpa [prefixWord, tailWord_4215005, baseEnd_4215005] using wordTrace_append hprefix tailTrace_4215005
  have hstable : (prefixWord ++ tailWord_4215005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215005).length < 2 ^ (prefixWord ++ tailWord_4215005).sum := by decide
  have hdescent : baseEnd_4215005 < baseStart_4215005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215041 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_4215041 : Nat := 118140960795 + 4215041 * 2 ^ 59
def prefixEnd_4215041 : Nat := 4983230072969 + 3 ^ 40 * 4215041 * 2
def baseEnd_4215041 : Nat := 2164342011407948366402885

theorem tailTrace_4215041 : CollatzResearch.WordTrace tailWord_4215041 prefixEnd_4215041 2164342011407948366402885 := by
  unfold tailWord_4215041
  simp only [CollatzResearch.WordTrace]
  refine ⟨153735175122633803535996977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102490116748422535690664651 153735175122633803535996977)
  ·
    refine ⟨115301381341975352651997733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153735175122633803535996977 115301381341975352651997733)
    ·
      refine ⟨21619009001620378622249575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 115301381341975352651997733 21619009001620378622249575)
      ·
        refine ⟨32428513502430567933374363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21619009001620378622249575 32428513502430567933374363)
        ·
          refine ⟨48642770253645851900061545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32428513502430567933374363 48642770253645851900061545)
          ·
            refine ⟨36482077690234388925046159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48642770253645851900061545 36482077690234388925046159)
            ·
              refine ⟨54723116535351583387569239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36482077690234388925046159 54723116535351583387569239)
              ·
                refine ⟨82084674803027375081353859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54723116535351583387569239 82084674803027375081353859)
                ·
                  refine ⟨123127012204541062622030789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 82084674803027375081353859 123127012204541062622030789)
                  ·
                    refine ⟨23086314788351449241630773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 123127012204541062622030789 23086314788351449241630773)
                    ·
                      refine ⟨2164342011407948366402885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23086314788351449241630773 2164342011407948366402885)
                      ·
                        rfl

theorem cell23_4215041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_4215041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215041 prefixEnd_4215041 := by exact prefixLift 4215041
  have htrace : WordTrace (prefixWord ++ tailWord_4215041) baseStart_4215041 baseEnd_4215041 := by
    simpa [prefixWord, tailWord_4215041, baseEnd_4215041] using wordTrace_append hprefix tailTrace_4215041
  have hstable : (prefixWord ++ tailWord_4215041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215041).length < 2 ^ (prefixWord ++ tailWord_4215041).sum := by decide
  have hdescent : baseEnd_4215041 < baseStart_4215041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215061 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 4, 6]
def baseStart_4215061 : Nat := 118140960795 + 4215061 * 2 ^ 59
def prefixEnd_4215061 : Nat := 4983230072969 + 3 ^ 40 * 4215061 * 2
def baseEnd_4215061 : Nat := 721450760340346096050931

theorem tailTrace_4215061 : CollatzResearch.WordTrace tailWord_4215061 prefixEnd_4215061 721450760340346096050931 := by
  unfold tailWord_4215061
  simp only [CollatzResearch.WordTrace]
  refine ⟨153735904582561346951725037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102490603055040897967816691 153735904582561346951725037)
  ·
    refine ⟨57650964218460505106896889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153735904582561346951725037 57650964218460505106896889)
    ·
      refine ⟨43238223163845378830172667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57650964218460505106896889 43238223163845378830172667)
      ·
        refine ⟨64857334745768068245259001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43238223163845378830172667 64857334745768068245259001)
        ·
          refine ⟨48643001059326051183944251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64857334745768068245259001 48643001059326051183944251)
          ·
            refine ⟨72964501588989076775916377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48643001059326051183944251 72964501588989076775916377)
            ·
              refine ⟨54723376191741807581937283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72964501588989076775916377 54723376191741807581937283)
              ·
                refine ⟨82085064287612711372905925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54723376191741807581937283 82085064287612711372905925)
                ·
                  refine ⟨15390949553927383382419861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82085064287612711372905925 15390949553927383382419861)
                  ·
                    refine ⟨721450760340346096050931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15390949553927383382419861 721450760340346096050931)
                    ·
                      rfl

theorem cell23_4215061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_4215061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215061 prefixEnd_4215061 := by exact prefixLift 4215061
  have htrace : WordTrace (prefixWord ++ tailWord_4215061) baseStart_4215061 baseEnd_4215061 := by
    simpa [prefixWord, tailWord_4215061, baseEnd_4215061] using wordTrace_append hprefix tailTrace_4215061
  have hstable : (prefixWord ++ tailWord_4215061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215061).length < 2 ^ (prefixWord ++ tailWord_4215061).sum := by decide
  have hdescent : baseEnd_4215061 < baseStart_4215061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215089 : List Nat := [1, 2, 2, 3, 4, 2, 1, 2, 1, 3, 2]
def baseStart_4215089 : Nat := 118140960795 + 4215089 * 2 ^ 59
def prefixEnd_4215089 : Nat := 4983230072969 + 3 ^ 40 * 4215089 * 2
def baseEnd_4215089 : Nat := 2164366658479364178602665

theorem tailTrace_4215089 : CollatzResearch.WordTrace tailWord_4215089 prefixEnd_4215089 2164366658479364178602665 := by
  unfold tailWord_4215089
  simp only [CollatzResearch.WordTrace]
  refine ⟨153736925826459907733744321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102491283884306605155829547 153736925826459907733744321)
  ·
    refine ⟨115302694369844930800308241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153736925826459907733744321 115302694369844930800308241)
    ·
      refine ⟨86477020777383698100231181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115302694369844930800308241 86477020777383698100231181)
      ·
        refine ⟨32428882791518886787586693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86477020777383698100231181 32428882791518886787586693)
        ·
          refine ⟨6080415523409791272672505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32428882791518886787586693 6080415523409791272672505)
          ·
            refine ⟨4560311642557343454504379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6080415523409791272672505 4560311642557343454504379)
            ·
              refine ⟨6840467463836015181756569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4560311642557343454504379 6840467463836015181756569)
              ·
                refine ⟨5130350597877011386317427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6840467463836015181756569 5130350597877011386317427)
                ·
                  refine ⟨7695525896815517079476141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5130350597877011386317427 7695525896815517079476141)
                  ·
                    refine ⟨2885822211305818904803553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7695525896815517079476141 2885822211305818904803553)
                    ·
                      refine ⟨2164366658479364178602665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2885822211305818904803553 2164366658479364178602665)
                      ·
                        rfl

theorem cell23_4215089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_4215089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215089 prefixEnd_4215089 := by exact prefixLift 4215089
  have htrace : WordTrace (prefixWord ++ tailWord_4215089) baseStart_4215089 baseEnd_4215089 := by
    simpa [prefixWord, tailWord_4215089, baseEnd_4215089] using wordTrace_append hprefix tailTrace_4215089
  have hstable : (prefixWord ++ tailWord_4215089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215089).length < 2 ^ (prefixWord ++ tailWord_4215089).sum := by decide
  have hdescent : baseEnd_4215089 < baseStart_4215089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215091 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 9]
def baseStart_4215091 : Nat := 118140960795 + 4215091 * 2 ^ 59
def prefixEnd_4215091 : Nat := 4983230072969 + 3 ^ 40 * 4215091 * 2
def baseEnd_4215091 : Nat := 240485298382297018975295

theorem tailTrace_4215091 : CollatzResearch.WordTrace tailWord_4215091 prefixEnd_4215091 240485298382297018975295 := by
  unfold tailWord_4215091
  simp only [CollatzResearch.WordTrace]
  refine ⟨153736998772452662075317127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102491332514968441383544751 153736998772452662075317127)
  ·
    refine ⟨230605498158678993112975691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153736998772452662075317127 230605498158678993112975691)
    ·
      refine ⟨345908247238018489669463537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 230605498158678993112975691 345908247238018489669463537)
      ·
        refine ⟨259431185428513867252097653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 345908247238018489669463537 259431185428513867252097653)
        ·
          refine ⟨24321673633923175054884155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 259431185428513867252097653 24321673633923175054884155)
          ·
            refine ⟨36482510450884762582326233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24321673633923175054884155 36482510450884762582326233)
            ·
              refine ⟨27361882838163571936744675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36482510450884762582326233 27361882838163571936744675)
              ·
                refine ⟨41042824257245357905117013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27361882838163571936744675 41042824257245357905117013)
                ·
                  refine ⟨240485298382297018975295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 41042824257245357905117013 240485298382297018975295)
                  ·
                    rfl

theorem cell23_4215091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 9].length) (baseStart_4215091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215091 prefixEnd_4215091 := by exact prefixLift 4215091
  have htrace : WordTrace (prefixWord ++ tailWord_4215091) baseStart_4215091 baseEnd_4215091 := by
    simpa [prefixWord, tailWord_4215091, baseEnd_4215091] using wordTrace_append hprefix tailTrace_4215091
  have hstable : (prefixWord ++ tailWord_4215091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215091).length < 2 ^ (prefixWord ++ tailWord_4215091).sum := by decide
  have hdescent : baseEnd_4215091 < baseStart_4215091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215102 : List Nat := [4, 2, 1, 2, 1, 3, 1, 2, 1, 4, 2]
def baseStart_4215102 : Nat := 118140960795 + 4215102 * 2 ^ 59
def prefixEnd_4215102 : Nat := 4983230072969 + 3 ^ 40 * 4215102 * 2
def baseEnd_4215102 : Nat := 2164373333727872627740105

theorem tailTrace_4215102 : CollatzResearch.WordTrace tailWord_4215102 prefixEnd_4215102 2164373333727872627740105 := by
  unfold tailWord_4215102
  simp only [CollatzResearch.WordTrace]
  refine ⟨19217174996926601369245945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102491599983608540635978373 19217174996926601369245945)
  ·
    refine ⟨14412881247694951026934459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19217174996926601369245945 14412881247694951026934459)
    ·
      refine ⟨21619321871542426540401689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14412881247694951026934459 21619321871542426540401689)
      ·
        refine ⟨16214491403656819905301267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21619321871542426540401689 16214491403656819905301267)
        ·
          refine ⟨24321737105485229857951901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16214491403656819905301267 24321737105485229857951901)
          ·
            refine ⟨9120651414556961196731963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24321737105485229857951901 9120651414556961196731963)
            ·
              refine ⟨13680977121835441795097945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9120651414556961196731963 13680977121835441795097945)
              ·
                refine ⟨10260732841376581346323459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13680977121835441795097945 10260732841376581346323459)
                ·
                  refine ⟨15391099262064872019485189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10260732841376581346323459 15391099262064872019485189)
                  ·
                    refine ⟨2885831111637163503653473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15391099262064872019485189 2885831111637163503653473)
                    ·
                      refine ⟨2164373333727872627740105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2885831111637163503653473 2164373333727872627740105)
                      ·
                        rfl

theorem cell23_4215102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_4215102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215102 prefixEnd_4215102 := by exact prefixLift 4215102
  have htrace : WordTrace (prefixWord ++ tailWord_4215102) baseStart_4215102 baseEnd_4215102 := by
    simpa [prefixWord, tailWord_4215102, baseEnd_4215102] using wordTrace_append hprefix tailTrace_4215102
  have hstable : (prefixWord ++ tailWord_4215102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215102).length < 2 ^ (prefixWord ++ tailWord_4215102).sum := by decide
  have hdescent : baseEnd_4215102 < baseStart_4215102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215132 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_4215132 : Nat := 118140960795 + 4215132 * 2 ^ 59
def prefixEnd_4215132 : Nat := 4983230072969 + 3 ^ 40 * 4215132 * 2
def baseEnd_4215132 : Nat := 2164388738147507510364967

theorem tailTrace_4215132 : CollatzResearch.WordTrace tailWord_4215132 prefixEnd_4215132 2164388738147507510364967 := by
  unfold tailWord_4215132
  simp only [CollatzResearch.WordTrace]
  refine ⟨76869247082652063038779825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102492329443536084051706433 76869247082652063038779825)
  ·
    refine ⟨57651935311989047279084869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76869247082652063038779825 57651935311989047279084869)
    ·
      refine ⟨10809737870997946364828413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57651935311989047279084869 10809737870997946364828413)
      ·
        refine ⟨4053651701624229886810655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10809737870997946364828413 4053651701624229886810655)
        ·
          refine ⟨6080477552436344830215983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4053651701624229886810655 6080477552436344830215983)
          ·
            refine ⟨9120716328654517245323975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6080477552436344830215983 9120716328654517245323975)
            ·
              refine ⟨13681074492981775867985963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9120716328654517245323975 13681074492981775867985963)
              ·
                refine ⟨20521611739472663801978945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13681074492981775867985963 20521611739472663801978945)
                ·
                  refine ⟨15391208804604497851484209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20521611739472663801978945 15391208804604497851484209)
                  ·
                    refine ⟨11543406603453373388613157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15391208804604497851484209 11543406603453373388613157)
                    ·
                      refine ⟨2164388738147507510364967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11543406603453373388613157 2164388738147507510364967)
                      ·
                        rfl

theorem cell23_4215132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_4215132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215132 prefixEnd_4215132 := by exact prefixLift 4215132
  have htrace : WordTrace (prefixWord ++ tailWord_4215132) baseStart_4215132 baseEnd_4215132 := by
    simpa [prefixWord, tailWord_4215132, baseEnd_4215132] using wordTrace_append hprefix tailTrace_4215132
  have hstable : (prefixWord ++ tailWord_4215132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215132).length < 2 ^ (prefixWord ++ tailWord_4215132).sum := by decide
  have hdescent : baseEnd_4215132 < baseStart_4215132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215151 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 1, 10]
def baseStart_4215151 : Nat := 118140960795 + 4215151 * 2 ^ 59
def prefixEnd_4215151 : Nat := 4983230072969 + 3 ^ 40 * 4215151 * 2
def baseEnd_4215151 : Nat := 721466164759980978675793

theorem tailTrace_4215151 : CollatzResearch.WordTrace tailWord_4215151 prefixEnd_4215151 721466164759980978675793 := by
  unfold tailWord_4215151
  simp only [CollatzResearch.WordTrace]
  refine ⟨153739187152235292322501307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102492791434823528215000871 153739187152235292322501307)
  ·
    refine ⟨230608780728352938483751961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153739187152235292322501307 230608780728352938483751961)
    ·
      refine ⟨172956585546264703862813971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 230608780728352938483751961 172956585546264703862813971)
      ·
        refine ⟨259434878319397055794220957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172956585546264703862813971 259434878319397055794220957)
        ·
          refine ⟨97288079369773895922832859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 259434878319397055794220957 97288079369773895922832859)
          ·
            refine ⟨145932119054660843884249289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97288079369773895922832859 145932119054660843884249289)
            ·
              refine ⟨109449089290995632913186967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145932119054660843884249289 109449089290995632913186967)
              ·
                refine ⟨164173633936493449369780451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109449089290995632913186967 164173633936493449369780451)
                ·
                  refine ⟨246260450904740174054670677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 164173633936493449369780451 246260450904740174054670677)
                  ·
                    refine ⟨721466164759980978675793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 246260450904740174054670677 721466164759980978675793)
                    ·
                      rfl

theorem cell23_4215151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 10].length) (baseStart_4215151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215151 prefixEnd_4215151 := by exact prefixLift 4215151
  have htrace : WordTrace (prefixWord ++ tailWord_4215151) baseStart_4215151 baseEnd_4215151 := by
    simpa [prefixWord, tailWord_4215151, baseEnd_4215151] using wordTrace_append hprefix tailTrace_4215151
  have hstable : (prefixWord ++ tailWord_4215151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215151).length < 2 ^ (prefixWord ++ tailWord_4215151).sum := by decide
  have hdescent : baseEnd_4215151 < baseStart_4215151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215170 : List Nat := [3, 4, 2, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_4215170 : Nat := 118140960795 + 4215170 * 2 ^ 59
def prefixEnd_4215170 : Nat := 4983230072969 + 3 ^ 40 * 4215170 * 2
def baseEnd_4215170 : Nat := 2164408250412378361689793

theorem tailTrace_4215170 : CollatzResearch.WordTrace tailWord_4215170 prefixEnd_4215170 2164408250412378361689793 := by
  unfold tailWord_4215170
  simp only [CollatzResearch.WordTrace]
  refine ⟨38434970034791614641860741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102493253426110972378295309 38434970034791614641860741)
  ·
    refine ⟨7206556881523427745348889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38434970034791614641860741 7206556881523427745348889)
    ·
      refine ⟨5404917661142570809011667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7206556881523427745348889 5404917661142570809011667)
      ·
        refine ⟨8107376491713856213517501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5404917661142570809011667 8107376491713856213517501)
        ·
          refine ⟨3040266184392696080069063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8107376491713856213517501 3040266184392696080069063)
          ·
            refine ⟨4560399276589044120103595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3040266184392696080069063 4560399276589044120103595)
            ·
              refine ⟨6840598914883566180155393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4560399276589044120103595 6840598914883566180155393)
              ·
                refine ⟨5130449186162674635116545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6840598914883566180155393 5130449186162674635116545)
                ·
                  refine ⟨3847836889622005976337409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5130449186162674635116545 3847836889622005976337409)
                  ·
                    refine ⟨2885877667216504482253057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3847836889622005976337409 2885877667216504482253057)
                    ·
                      refine ⟨2164408250412378361689793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2885877667216504482253057 2164408250412378361689793)
                      ·
                        rfl

theorem cell23_4215170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_4215170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215170 prefixEnd_4215170 := by exact prefixLift 4215170
  have htrace : WordTrace (prefixWord ++ tailWord_4215170) baseStart_4215170 baseEnd_4215170 := by
    simpa [prefixWord, tailWord_4215170, baseEnd_4215170] using wordTrace_append hprefix tailTrace_4215170
  have hstable : (prefixWord ++ tailWord_4215170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215170).length < 2 ^ (prefixWord ++ tailWord_4215170).sum := by decide
  have hdescent : baseEnd_4215170 < baseStart_4215170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215175 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 4, 4, 2]
def baseStart_4215175 : Nat := 118140960795 + 4215175 * 2 ^ 59
def prefixEnd_4215175 : Nat := 4983230072969 + 3 ^ 40 * 4215175 * 2
def baseEnd_4215175 : Nat := 2164410817815650842127269

theorem tailTrace_4215175 : CollatzResearch.WordTrace tailWord_4215175 prefixEnd_4215175 2164410817815650842127269 := by
  unfold tailWord_4215175
  simp only [CollatzResearch.WordTrace]
  refine ⟨153740062504148344421374979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102493375002765562947583319 153740062504148344421374979)
  ·
    refine ⟨230610093756222516632062469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153740062504148344421374979 230610093756222516632062469)
    ·
      refine ⟨43239392579291721868511713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 230610093756222516632062469 43239392579291721868511713)
      ·
        refine ⟨32429544434468791401383785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43239392579291721868511713 32429544434468791401383785)
        ·
          refine ⟨24322158325851593551037839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32429544434468791401383785 24322158325851593551037839)
          ·
            refine ⟨36483237488777390326556759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24322158325851593551037839 36483237488777390326556759)
            ·
              refine ⟨54724856233166085489835139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36483237488777390326556759 54724856233166085489835139)
              ·
                refine ⟨82087284349749128234752709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54724856233166085489835139 82087284349749128234752709)
                ·
                  refine ⟨15391365815577961544016133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 82087284349749128234752709 15391365815577961544016133)
                  ·
                    refine ⟨2885881090420867789503025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15391365815577961544016133 2885881090420867789503025)
                    ·
                      refine ⟨2164410817815650842127269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2885881090420867789503025 2164410817815650842127269)
                      ·
                        rfl

theorem cell23_4215175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_4215175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215175 prefixEnd_4215175 := by exact prefixLift 4215175
  have htrace : WordTrace (prefixWord ++ tailWord_4215175) baseStart_4215175 baseEnd_4215175 := by
    simpa [prefixWord, tailWord_4215175, baseEnd_4215175] using wordTrace_append hprefix tailTrace_4215175
  have hstable : (prefixWord ++ tailWord_4215175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215175).length < 2 ^ (prefixWord ++ tailWord_4215175).sum := by decide
  have hdescent : baseEnd_4215175 < baseStart_4215175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215192 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 2, 4, 2]
def baseStart_4215192 : Nat := 118140960795 + 4215192 * 2 ^ 59
def prefixEnd_4215192 : Nat := 4983230072969 + 3 ^ 40 * 4215192 * 2
def baseEnd_4215192 : Nat := 2164419546986777275614691

theorem tailTrace_4215192 : CollatzResearch.WordTrace tailWord_4215192 prefixEnd_4215192 2164419546986777275614691 := by
  unfold tailWord_4215192
  simp only [CollatzResearch.WordTrace]
  refine ⟨76870341272543378162371915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102493788363391170883162553 76870341272543378162371915)
  ·
    refine ⟨115305511908815067243557873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76870341272543378162371915 115305511908815067243557873)
    ·
      refine ⟨86479133931611300432668405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 115305511908815067243557873 86479133931611300432668405)
      ·
        refine ⟨8107418806088559415562663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86479133931611300432668405 8107418806088559415562663)
        ·
          refine ⟨12161128209132839123343995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8107418806088559415562663 12161128209132839123343995)
          ·
            refine ⟨18241692313699258685015993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12161128209132839123343995 18241692313699258685015993)
            ·
              refine ⟨13681269235274444013761995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18241692313699258685015993 13681269235274444013761995)
              ·
                refine ⟨20521903852911666020642993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13681269235274444013761995 20521903852911666020642993)
                ·
                  refine ⟨15391427889683749515482245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20521903852911666020642993 15391427889683749515482245)
                  ·
                    refine ⟨2885892729315703034152921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15391427889683749515482245 2885892729315703034152921)
                    ·
                      refine ⟨2164419546986777275614691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2885892729315703034152921 2164419546986777275614691)
                      ·
                        rfl

theorem cell23_4215192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_4215192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215192 prefixEnd_4215192 := by exact prefixLift 4215192
  have htrace : WordTrace (prefixWord ++ tailWord_4215192) baseStart_4215192 baseEnd_4215192 := by
    simpa [prefixWord, tailWord_4215192, baseEnd_4215192] using wordTrace_append hprefix tailTrace_4215192
  have hstable : (prefixWord ++ tailWord_4215192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215192).length < 2 ^ (prefixWord ++ tailWord_4215192).sum := by decide
  have hdescent : baseEnd_4215192 < baseStart_4215192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4215236 : List Nat := [2, 3, 3, 2, 3, 1, 1, 1, 3, 4]
def baseStart_4215236 : Nat := 118140960795 + 4215236 * 2 ^ 59
def prefixEnd_4215236 : Nat := 4983230072969 + 3 ^ 40 * 4215236 * 2
def baseEnd_4215236 : Nat := 721480713378525034488163

theorem tailTrace_4215236 : CollatzResearch.WordTrace tailWord_4215236 prefixEnd_4215236 721480713378525034488163 := by
  unfold tailWord_4215236
  simp only [CollatzResearch.WordTrace]
  refine ⟨76871143678463675919672781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102494858237951567892897041 76871143678463675919672781)
  ·
    refine ⟨28826678879423878469877293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76871143678463675919672781 28826678879423878469877293)
    ·
      refine ⟨10810004579783954426203985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28826678879423878469877293 10810004579783954426203985)
      ·
        refine ⟨8107503434837965819652989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10810004579783954426203985 8107503434837965819652989)
        ·
          refine ⟨3040313788064237182369871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8107503434837965819652989 3040313788064237182369871)
          ·
            refine ⟨4560470682096355773554807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3040313788064237182369871 4560470682096355773554807)
            ·
              refine ⟨6840706023144533660332211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4560470682096355773554807 6840706023144533660332211)
              ·
                refine ⟨10261059034716800490498317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6840706023144533660332211 10261059034716800490498317)
                ·
                  refine ⟨3847897138018800183936869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10261059034716800490498317 3847897138018800183936869)
                  ·
                    refine ⟨721480713378525034488163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3847897138018800183936869 721480713378525034488163)
                    ·
                      rfl

theorem cell23_4215236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_4215236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4215236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4215236 prefixEnd_4215236 := by exact prefixLift 4215236
  have htrace : WordTrace (prefixWord ++ tailWord_4215236) baseStart_4215236 baseEnd_4215236 := by
    simpa [prefixWord, tailWord_4215236, baseEnd_4215236] using wordTrace_append hprefix tailTrace_4215236
  have hstable : (prefixWord ++ tailWord_4215236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4215236).length < 2 ^ (prefixWord ++ tailWord_4215236).sum := by decide
  have hdescent : baseEnd_4215236 < baseStart_4215236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4215236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
