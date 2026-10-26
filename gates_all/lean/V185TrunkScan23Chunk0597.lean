import V185TrunkScan23Chunk0596

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3529918 : List Nat := [4, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2]
def baseStart_3529918 : Nat := 118140960795 + 3529918 * 2 ^ 59
def prefixEnd_3529918 : Nat := 4983230072969 + 3 ^ 40 * 3529918 * 2
def baseEnd_3529918 : Nat := 1812544604957625413291209

theorem tailTrace_3529918 : CollatzResearch.WordTrace tailWord_3529918 prefixEnd_3529918 1812544604957625413291209 := by
  unfold tailWord_3529918
  simp only [CollatzResearch.WordTrace]
  refine ⟨16093335803214677855401801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85831124283811615228809605 16093335803214677855401801)
  ·
    refine ⟨12070001852411008391551351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16093335803214677855401801 12070001852411008391551351)
    ·
      refine ⟨18105002778616512587327027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12070001852411008391551351 18105002778616512587327027)
      ·
        refine ⟨27157504167924768880990541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18105002778616512587327027 27157504167924768880990541)
        ·
          refine ⟨10184064062971788330371453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27157504167924768880990541 10184064062971788330371453)
          ·
            refine ⟨3819024023614420623889295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10184064062971788330371453 3819024023614420623889295)
            ·
              refine ⟨5728536035421630935833943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3819024023614420623889295 5728536035421630935833943)
              ·
                refine ⟨8592804053132446403750915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5728536035421630935833943 8592804053132446403750915)
                ·
                  refine ⟨12889206079698669605626373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8592804053132446403750915 12889206079698669605626373)
                  ·
                    refine ⟨2416726139943500551054945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12889206079698669605626373 2416726139943500551054945)
                    ·
                      refine ⟨1812544604957625413291209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2416726139943500551054945 1812544604957625413291209)
                      ·
                        rfl

theorem cell23_3529918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_3529918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529918 prefixEnd_3529918 := by exact prefixLift 3529918
  have htrace : WordTrace (prefixWord ++ tailWord_3529918) baseStart_3529918 baseEnd_3529918 := by
    simpa [prefixWord, tailWord_3529918, baseEnd_3529918] using wordTrace_append hprefix tailTrace_3529918
  have hstable : (prefixWord ++ tailWord_3529918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529918).length < 2 ^ (prefixWord ++ tailWord_3529918).sum := by decide
  have hdescent : baseEnd_3529918 < baseStart_3529918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529922 : List Nat := [3, 5, 1, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_3529922 : Nat := 118140960795 + 3529922 * 2 ^ 59
def prefixEnd_3529922 : Nat := 4983230072969 + 3 ^ 40 * 3529922 * 2
def baseEnd_3529922 : Nat := 1812546658880243397641191

theorem tailTrace_3529922 : CollatzResearch.WordTrace tailWord_3529922 prefixEnd_3529922 1812546658880243397641191 := by
  unfold tailWord_3529922
  simp only [CollatzResearch.WordTrace]
  refine ⟨32186708079425732881590005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85831221545135287684240013 32186708079425732881590005)
  ·
    refine ⟨3017503882446162457649063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32186708079425732881590005 3017503882446162457649063)
    ·
      refine ⟨4526255823669243686473595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3017503882446162457649063 4526255823669243686473595)
      ·
        refine ⟨6789383735503865529710393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4526255823669243686473595 6789383735503865529710393)
        ·
          refine ⟨5092037801627899147282795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6789383735503865529710393 5092037801627899147282795)
          ·
            refine ⟨7638056702441848720924193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5092037801627899147282795 7638056702441848720924193)
            ·
              refine ⟨5728542526831386540693145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7638056702441848720924193 5728542526831386540693145)
              ·
                refine ⟨4296406895123539905519859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5728542526831386540693145 4296406895123539905519859)
                ·
                  refine ⟨6444610342685309858279789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4296406895123539905519859 6444610342685309858279789)
                  ·
                    refine ⟨2416728878506991196854921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6444610342685309858279789 2416728878506991196854921)
                    ·
                      refine ⟨1812546658880243397641191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2416728878506991196854921 1812546658880243397641191)
                      ·
                        rfl

theorem cell23_3529922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_3529922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529922 prefixEnd_3529922 := by exact prefixLift 3529922
  have htrace : WordTrace (prefixWord ++ tailWord_3529922) baseStart_3529922 baseEnd_3529922 := by
    simpa [prefixWord, tailWord_3529922, baseEnd_3529922] using wordTrace_append hprefix tailTrace_3529922
  have hstable : (prefixWord ++ tailWord_3529922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529922).length < 2 ^ (prefixWord ++ tailWord_3529922).sum := by decide
  have hdescent : baseEnd_3529922 < baseStart_3529922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529937 : List Nat := [1, 2, 2, 1, 2, 2, 1, 5, 2, 5]
def baseStart_3529937 : Nat := 118140960795 + 3529937 * 2 ^ 59
def prefixEnd_3529937 : Nat := 4983230072969 + 3 ^ 40 * 3529937 * 2
def baseEnd_3529937 : Nat := 604184787030020279651207

theorem tailTrace_3529937 : CollatzResearch.WordTrace tailWord_3529937 prefixEnd_3529937 604184787030020279651207 := by
  unfold tailWord_3529937
  simp only [CollatzResearch.WordTrace]
  refine ⟨128747379412648589088156065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85831586275099059392104043 128747379412648589088156065)
  ·
    refine ⟨96560534559486441816117049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128747379412648589088156065 96560534559486441816117049)
    ·
      refine ⟨72420400919614831362087787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96560534559486441816117049 72420400919614831362087787)
      ·
        refine ⟨108630601379422247043131681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72420400919614831362087787 108630601379422247043131681)
        ·
          refine ⟨81472951034566685282348761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108630601379422247043131681 81472951034566685282348761)
          ·
            refine ⟨61104713275925013961761571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81472951034566685282348761 61104713275925013961761571)
            ·
              refine ⟨91657069913887520942642357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61104713275925013961761571 91657069913887520942642357)
              ·
                refine ⟨8592850304426955088372721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91657069913887520942642357 8592850304426955088372721)
                ·
                  refine ⟨6444637728320216316279541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8592850304426955088372721 6444637728320216316279541)
                  ·
                    refine ⟨604184787030020279651207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6444637728320216316279541 604184787030020279651207)
                    ·
                      rfl

theorem cell23_3529937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_3529937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529937 prefixEnd_3529937 := by exact prefixLift 3529937
  have htrace : WordTrace (prefixWord ++ tailWord_3529937) baseStart_3529937 baseEnd_3529937 := by
    simpa [prefixWord, tailWord_3529937, baseEnd_3529937] using wordTrace_append hprefix tailTrace_3529937
  have hstable : (prefixWord ++ tailWord_3529937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529937).length < 2 ^ (prefixWord ++ tailWord_3529937).sum := by decide
  have hdescent : baseEnd_3529937 < baseStart_3529937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529941 : List Nat := [1, 3, 2, 4, 1, 1, 3, 3, 5]
def baseStart_3529941 : Nat := 118140960795 + 3529941 * 2 ^ 59
def prefixEnd_3529941 : Nat := 4983230072969 + 3 ^ 40 * 3529941 * 2
def baseEnd_3529941 : Nat := 201395157223630980367067

theorem tailTrace_3529941 : CollatzResearch.WordTrace tailWord_3529941 prefixEnd_3529941 201395157223630980367067 := by
  unfold tailWord_3529941
  simp only [CollatzResearch.WordTrace]
  refine ⟨128747525304634097771301677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85831683536422731847534451 128747525304634097771301677)
  ·
    refine ⟨48280321989237786664238129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128747525304634097771301677 48280321989237786664238129)
    ·
      refine ⟨36210241491928339998178597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48280321989237786664238129 36210241491928339998178597)
      ·
        refine ⟨6789420279736563749658487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36210241491928339998178597 6789420279736563749658487)
        ·
          refine ⟨10184130419604845624487731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6789420279736563749658487 10184130419604845624487731)
          ·
            refine ⟨15276195629407268436731597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10184130419604845624487731 15276195629407268436731597)
            ·
              refine ⟨5728573361027725663774349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15276195629407268436731597 5728573361027725663774349)
              ·
                refine ⟨2148215010385397123915381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5728573361027725663774349 2148215010385397123915381)
                ·
                  refine ⟨201395157223630980367067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2148215010385397123915381 201395157223630980367067)
                  ·
                    rfl

theorem cell23_3529941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 5].length) (baseStart_3529941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529941 prefixEnd_3529941 := by exact prefixLift 3529941
  have htrace : WordTrace (prefixWord ++ tailWord_3529941) baseStart_3529941 baseEnd_3529941 := by
    simpa [prefixWord, tailWord_3529941, baseEnd_3529941] using wordTrace_append hprefix tailTrace_3529941
  have hstable : (prefixWord ++ tailWord_3529941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529941).length < 2 ^ (prefixWord ++ tailWord_3529941).sum := by decide
  have hdescent : baseEnd_3529941 < baseStart_3529941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3529974 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_3529974 : Nat := 118140960795 + 3529974 * 2 ^ 59
def prefixEnd_3529974 : Nat := 4983230072969 + 3 ^ 40 * 3529974 * 2
def baseEnd_3529974 : Nat := 1812573359874277194190951

theorem tailTrace_3529974 : CollatzResearch.WordTrace tailWord_3529974 prefixEnd_3529974 1812573359874277194190951 := by
  unfold tailWord_3529974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8046795557094659025453311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85832485942343029604835317 8046795557094659025453311)
  ·
    refine ⟨12070193335641988538179967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8046795557094659025453311 12070193335641988538179967)
    ·
      refine ⟨18105290003462982807269951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12070193335641988538179967 18105290003462982807269951)
      ·
        refine ⟨27157935005194474210904927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18105290003462982807269951 27157935005194474210904927)
        ·
          refine ⟨40736902507791711316357391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27157935005194474210904927 40736902507791711316357391)
          ·
            refine ⟨61105353761687566974536087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40736902507791711316357391 61105353761687566974536087)
            ·
              refine ⟨91658030642531350461804131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61105353761687566974536087 91658030642531350461804131)
              ·
                refine ⟨137487045963797025692706197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91658030642531350461804131 137487045963797025692706197)
                ·
                  refine ⟨6444705279552985579345603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137487045963797025692706197 6444705279552985579345603)
                  ·
                    refine ⟨9667057919329478369018405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6444705279552985579345603 9667057919329478369018405)
                    ·
                      refine ⟨1812573359874277194190951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9667057919329478369018405 1812573359874277194190951)
                      ·
                        rfl

theorem cell23_3529974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_3529974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3529974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3529974 prefixEnd_3529974 := by exact prefixLift 3529974
  have htrace : WordTrace (prefixWord ++ tailWord_3529974) baseStart_3529974 baseEnd_3529974 := by
    simpa [prefixWord, tailWord_3529974, baseEnd_3529974] using wordTrace_append hprefix tailTrace_3529974
  have hstable : (prefixWord ++ tailWord_3529974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3529974).length < 2 ^ (prefixWord ++ tailWord_3529974).sum := by decide
  have hdescent : baseEnd_3529974 < baseStart_3529974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3529974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530001 : List Nat := [1, 2, 2, 1, 1, 4, 2, 5, 1, 4]
def baseStart_3530001 : Nat := 118140960795 + 3530001 * 2 ^ 59
def prefixEnd_3530001 : Nat := 4983230072969 + 3 ^ 40 * 3530001 * 2
def baseEnd_3530001 : Nat := 604195741283982862851109

theorem tailTrace_3530001 : CollatzResearch.WordTrace tailWord_3530001 prefixEnd_3530001 604195741283982862851109 := by
  unfold tailWord_3530001
  simp only [CollatzResearch.WordTrace]
  refine ⟨128749713684416728018485857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85833142456277818678990571 128749713684416728018485857)
  ·
    refine ⟨96562285263312546013864393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128749713684416728018485857 96562285263312546013864393)
    ·
      refine ⟨72421713947484409510398295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96562285263312546013864393 72421713947484409510398295)
      ·
        refine ⟨108632570921226614265597443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72421713947484409510398295 108632570921226614265597443)
        ·
          refine ⟨162948856381839921398396165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108632570921226614265597443 162948856381839921398396165)
          ·
            refine ⟨30552910571594985262199281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 162948856381839921398396165 30552910571594985262199281)
            ·
              refine ⟨22914682928696238946649461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30552910571594985262199281 22914682928696238946649461)
              ·
                refine ⟨2148251524565272401248387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22914682928696238946649461 2148251524565272401248387)
                ·
                  refine ⟨3222377286847908601872581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2148251524565272401248387 3222377286847908601872581)
                  ·
                    refine ⟨604195741283982862851109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3222377286847908601872581 604195741283982862851109)
                    ·
                      rfl

theorem cell23_3530001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 1, 4].length) (baseStart_3530001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530001 prefixEnd_3530001 := by exact prefixLift 3530001
  have htrace : WordTrace (prefixWord ++ tailWord_3530001) baseStart_3530001 baseEnd_3530001 := by
    simpa [prefixWord, tailWord_3530001, baseEnd_3530001] using wordTrace_append hprefix tailTrace_3530001
  have hstable : (prefixWord ++ tailWord_3530001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530001).length < 2 ^ (prefixWord ++ tailWord_3530001).sum := by decide
  have hdescent : baseEnd_3530001 < baseStart_3530001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530017 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_3530017 : Nat := 118140960795 + 3530017 * 2 ^ 59
def prefixEnd_3530017 : Nat := 4983230072969 + 3 ^ 40 * 3530017 * 2
def baseEnd_3530017 : Nat := 1812595439542420525953253

theorem tailTrace_3530017 : CollatzResearch.WordTrace tailWord_3530017 prefixEnd_3530017 1812595439542420525953253 := by
  unfold tailWord_3530017
  simp only [CollatzResearch.WordTrace]
  refine ⟨128750297252358762751068305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85833531501572508500712203 128750297252358762751068305)
  ·
    refine ⟨96562722939269072063301229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128750297252358762751068305 96562722939269072063301229)
    ·
      refine ⟨36211021102225902023737961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96562722939269072063301229 36211021102225902023737961)
      ·
        refine ⟨27158265826669426517803471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36211021102225902023737961 27158265826669426517803471)
        ·
          refine ⟨40737398740004139776705207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27158265826669426517803471 40737398740004139776705207)
          ·
            refine ⟨61106098110006209665057811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40737398740004139776705207 61106098110006209665057811)
            ·
              refine ⟨91659147165009314497586717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61106098110006209665057811 91659147165009314497586717)
              ·
                refine ⟨34372180186878492936595019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91659147165009314497586717 34372180186878492936595019)
                ·
                  refine ⟨51558270280317739404892529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34372180186878492936595019 51558270280317739404892529)
                  ·
                    refine ⟨38668702710238304553669397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51558270280317739404892529 38668702710238304553669397)
                    ·
                      refine ⟨1812595439542420525953253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38668702710238304553669397 1812595439542420525953253)
                      ·
                        rfl

theorem cell23_3530017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_3530017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530017 prefixEnd_3530017 := by exact prefixLift 3530017
  have htrace : WordTrace (prefixWord ++ tailWord_3530017) baseStart_3530017 baseEnd_3530017 := by
    simpa [prefixWord, tailWord_3530017, baseEnd_3530017] using wordTrace_append hprefix tailTrace_3530017
  have hstable : (prefixWord ++ tailWord_3530017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530017).length < 2 ^ (prefixWord ++ tailWord_3530017).sum := by decide
  have hdescent : baseEnd_3530017 < baseStart_3530017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530044 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 3, 5]
def baseStart_3530044 : Nat := 118140960795 + 3530044 * 2 ^ 59
def prefixEnd_3530044 : Nat := 4983230072969 + 3 ^ 40 * 3530044 * 2
def baseEnd_3530044 : Nat := 604203101173363973438543

theorem tailTrace_3530044 : CollatzResearch.WordTrace tailWord_3530044 prefixEnd_3530044 604203101173363973438543 := by
  unfold tailWord_3530044
  simp only [CollatzResearch.WordTrace]
  refine ⟨64375641011630473181150593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85834188015507297574867457 64375641011630473181150593)
  ·
    refine ⟨48281730758722854885862945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64375641011630473181150593 48281730758722854885862945)
    ·
      refine ⟨36211298069042141164397209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48281730758722854885862945 36211298069042141164397209)
      ·
        refine ⟨27158473551781605873297907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36211298069042141164397209 27158473551781605873297907)
        ·
          refine ⟨40737710327672408809946861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27158473551781605873297907 40737710327672408809946861)
          ·
            refine ⟨15276641372877153303730073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40737710327672408809946861 15276641372877153303730073)
            ·
              refine ⟨11457481029657864977797555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15276641372877153303730073 11457481029657864977797555)
              ·
                refine ⟨17186221544486797466696333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11457481029657864977797555 17186221544486797466696333)
                ·
                  refine ⟨6444833079182549050011125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17186221544486797466696333 6444833079182549050011125)
                  ·
                    refine ⟨604203101173363973438543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6444833079182549050011125 604203101173363973438543)
                    ·
                      rfl

theorem cell23_3530044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_3530044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530044 prefixEnd_3530044 := by exact prefixLift 3530044
  have htrace : WordTrace (prefixWord ++ tailWord_3530044) baseStart_3530044 baseEnd_3530044 := by
    simpa [prefixWord, tailWord_3530044, baseEnd_3530044] using wordTrace_append hprefix tailTrace_3530044
  have hstable : (prefixWord ++ tailWord_3530044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530044).length < 2 ^ (prefixWord ++ tailWord_3530044).sum := by decide
  have hdescent : baseEnd_3530044 < baseStart_3530044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530045 : List Nat := [1, 4, 1, 5, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3530045 : Nat := 118140960795 + 3530045 * 2 ^ 59
def prefixEnd_3530045 : Nat := 4983230072969 + 3 ^ 40 * 3530045 * 2
def baseEnd_3530045 : Nat := 1812609817000746416403125

theorem tailTrace_3530045 : CollatzResearch.WordTrace tailWord_3530045 prefixEnd_3530045 1812609817000746416403125 := by
  unfold tailWord_3530045
  simp only [CollatzResearch.WordTrace]
  refine ⟨128751318496257323533087589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85834212330838215688725059 128751318496257323533087589)
  ·
    refine ⟨24140872218048248162453923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128751318496257323533087589 24140872218048248162453923)
    ·
      refine ⟨36211308327072372243680885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24140872218048248162453923 36211308327072372243680885)
      ·
        refine ⟨3394810155663034897845083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36211308327072372243680885 3394810155663034897845083)
        ·
          refine ⟨5092215233494552346767625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3394810155663034897845083 5092215233494552346767625)
          ·
            refine ⟨3819161425120914260075719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5092215233494552346767625 3819161425120914260075719)
            ·
              refine ⟨5728742137681371390113579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3819161425120914260075719 5728742137681371390113579)
              ·
                refine ⟨8593113206522057085170369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5728742137681371390113579 8593113206522057085170369)
                ·
                  refine ⟨6444834904891542813877777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8593113206522057085170369 6444834904891542813877777)
                  ·
                    refine ⟨4833626178668657110408333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6444834904891542813877777 4833626178668657110408333)
                    ·
                      refine ⟨1812609817000746416403125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4833626178668657110408333 1812609817000746416403125)
                      ·
                        rfl

theorem cell23_3530045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3530045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530045 prefixEnd_3530045 := by exact prefixLift 3530045
  have htrace : WordTrace (prefixWord ++ tailWord_3530045) baseStart_3530045 baseEnd_3530045 := by
    simpa [prefixWord, tailWord_3530045, baseEnd_3530045] using wordTrace_append hprefix tailTrace_3530045
  have hstable : (prefixWord ++ tailWord_3530045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530045).length < 2 ^ (prefixWord ++ tailWord_3530045).sum := by decide
  have hdescent : baseEnd_3530045 < baseStart_3530045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530084 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_3530084 : Nat := 118140960795 + 3530084 * 2 ^ 59
def prefixEnd_3530084 : Nat := 4983230072969 + 3 ^ 40 * 3530084 * 2
def baseEnd_3530084 : Nat := 1812629842746271763815445

theorem tailTrace_3530084 : CollatzResearch.WordTrace tailWord_3530084 prefixEnd_3530084 1812629842746271763815445 := by
  unfold tailWord_3530084
  simp only [CollatzResearch.WordTrace]
  refine ⟨64376370471558016596878653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85835160628744022129171537 64376370471558016596878653)
  ·
    refine ⟨24141138926834256223829495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64376370471558016596878653 24141138926834256223829495)
    ·
      refine ⟨36211708390251384335744243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24141138926834256223829495 36211708390251384335744243)
      ·
        refine ⟨54317562585377076503616365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36211708390251384335744243 54317562585377076503616365)
        ·
          refine ⟨20369085969516403688856137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54317562585377076503616365 20369085969516403688856137)
          ·
            refine ⟨15276814477137302766642103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20369085969516403688856137 15276814477137302766642103)
            ·
              refine ⟨22915221715705954149963155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15276814477137302766642103 22915221715705954149963155)
              ·
                refine ⟨34372832573558931224944733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22915221715705954149963155 34372832573558931224944733)
                ·
                  refine ⟨12889812215084599209354275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34372832573558931224944733 12889812215084599209354275)
                  ·
                    refine ⟨19334718322626898814031413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12889812215084599209354275 19334718322626898814031413)
                    ·
                      refine ⟨1812629842746271763815445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19334718322626898814031413 1812629842746271763815445)
                      ·
                        rfl

theorem cell23_3530084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_3530084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530084 prefixEnd_3530084 := by exact prefixLift 3530084
  have htrace : WordTrace (prefixWord ++ tailWord_3530084) baseStart_3530084 baseEnd_3530084 := by
    simpa [prefixWord, tailWord_3530084, baseEnd_3530084] using wordTrace_append hprefix tailTrace_3530084
  have hstable : (prefixWord ++ tailWord_3530084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530084).length < 2 ^ (prefixWord ++ tailWord_3530084).sum := by decide
  have hdescent : baseEnd_3530084 < baseStart_3530084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530098 : List Nat := [3, 2, 1, 2, 1, 2, 1, 4, 3, 2, 2]
def baseStart_3530098 : Nat := 118140960795 + 3530098 * 2 ^ 59
def prefixEnd_3530098 : Nat := 4983230072969 + 3 ^ 40 * 3530098 * 2
def baseEnd_3530098 : Nat := 1812637031475434709040381

theorem tailTrace_3530098 : CollatzResearch.WordTrace tailWord_3530098 prefixEnd_3530098 1812637031475434709040381 := by
  unfold tailWord_3530098
  simp only [CollatzResearch.WordTrace]
  refine ⟨32188312891266328396191737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85835501043376875723177965 32188312891266328396191737)
  ·
    refine ⟨24141234668449746297143803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32188312891266328396191737 24141234668449746297143803)
    ·
      refine ⟨36211852002674619445715705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24141234668449746297143803 36211852002674619445715705)
      ·
        refine ⟨27158889002005964584286779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36211852002674619445715705 27158889002005964584286779)
        ·
          refine ⟨40738333503008946876430169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27158889002005964584286779 40738333503008946876430169)
          ·
            refine ⟨30553750127256710157322627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40738333503008946876430169 30553750127256710157322627)
            ·
              refine ⟨45830625190885065235983941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30553750127256710157322627 45830625190885065235983941)
              ·
                refine ⟨8593242223290949731746989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45830625190885065235983941 8593242223290949731746989)
                ·
                  refine ⟨3222465833734106149405121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8593242223290949731746989 3222465833734106149405121)
                  ·
                    refine ⟨2416849375300579612053841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3222465833734106149405121 2416849375300579612053841)
                    ·
                      refine ⟨1812637031475434709040381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2416849375300579612053841 1812637031475434709040381)
                      ·
                        rfl

theorem cell23_3530098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_3530098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530098 prefixEnd_3530098 := by exact prefixLift 3530098
  have htrace : WordTrace (prefixWord ++ tailWord_3530098) baseStart_3530098 baseEnd_3530098 := by
    simpa [prefixWord, tailWord_3530098, baseEnd_3530098] using wordTrace_append hprefix tailTrace_3530098
  have hstable : (prefixWord ++ tailWord_3530098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530098).length < 2 ^ (prefixWord ++ tailWord_3530098).sum := by decide
  have hdescent : baseEnd_3530098 < baseStart_3530098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530121 : List Nat := [1, 2, 1, 1, 8, 1, 9]
def baseStart_3530121 : Nat := 118140960795 + 3530121 * 2 ^ 59
def prefixEnd_3530121 : Nat := 4983230072969 + 3 ^ 40 * 3530121 * 2
def baseEnd_3530121 : Nat := 22378380759635655790775

theorem tailTrace_3530121 : CollatzResearch.WordTrace tailWord_3530121 prefixEnd_3530121 22378380759635655790775 := by
  unfold tailWord_3530121
  simp only [CollatzResearch.WordTrace]
  refine ⟨128754090443981988512854217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85836060295987992341902811 128754090443981988512854217)
  ·
    refine ⟨96565567832986491384640663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128754090443981988512854217 96565567832986491384640663)
    ·
      refine ⟨144848351749479737076960995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96565567832986491384640663 144848351749479737076960995)
      ·
        refine ⟨217272527624219605615441493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144848351749479737076960995 217272527624219605615441493)
        ·
          refine ⟨2546162433096323503305955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 217272527624219605615441493 2546162433096323503305955)
          ·
            refine ⟨3819243649644485254958933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2546162433096323503305955 3819243649644485254958933)
            ·
              refine ⟨22378380759635655790775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3819243649644485254958933 22378380759635655790775)
              ·
                rfl

theorem cell23_3530121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 9].length) (baseStart_3530121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530121 prefixEnd_3530121 := by exact prefixLift 3530121
  have htrace : WordTrace (prefixWord ++ tailWord_3530121) baseStart_3530121 baseEnd_3530121 := by
    simpa [prefixWord, tailWord_3530121, baseEnd_3530121] using wordTrace_append hprefix tailTrace_3530121
  have hstable : (prefixWord ++ tailWord_3530121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530121).length < 2 ^ (prefixWord ++ tailWord_3530121).sum := by decide
  have hdescent : baseEnd_3530121 < baseStart_3530121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530132 : List Nat := [2, 4, 2, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_3530132 : Nat := 118140960795 + 3530132 * 2 ^ 59
def prefixEnd_3530132 : Nat := 4983230072969 + 3 ^ 40 * 3530132 * 2
def baseEnd_3530132 : Nat := 1812654489817687576015225

theorem tailTrace_3530132 : CollatzResearch.WordTrace tailWord_3530132 prefixEnd_3530132 1812654489817687576015225 := by
  unfold tailWord_3530132
  simp only [CollatzResearch.WordTrace]
  refine ⟨64377245823471068695752325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85836327764628091594336433 64377245823471068695752325)
  ·
    refine ⟨12070733591900825380453561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64377245823471068695752325 12070733591900825380453561)
    ·
      refine ⟨9053050193925619035340171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12070733591900825380453561 9053050193925619035340171)
      ·
        refine ⟨13579575290888428553010257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9053050193925619035340171 13579575290888428553010257)
        ·
          refine ⟨10184681468166321414757693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13579575290888428553010257 10184681468166321414757693)
          ·
            refine ⟨3819255550562370530534135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10184681468166321414757693 3819255550562370530534135)
            ·
              refine ⟨5728883325843555795801203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3819255550562370530534135 5728883325843555795801203)
              ·
                refine ⟨8593324988765333693701805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5728883325843555795801203 8593324988765333693701805)
                ·
                  refine ⟨3222496870787000135138177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8593324988765333693701805 3222496870787000135138177)
                  ·
                    refine ⟨2416872653090250101353633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3222496870787000135138177 2416872653090250101353633)
                    ·
                      refine ⟨1812654489817687576015225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2416872653090250101353633 1812654489817687576015225)
                      ·
                        rfl

theorem cell23_3530132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_3530132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530132 prefixEnd_3530132 := by exact prefixLift 3530132
  have htrace : WordTrace (prefixWord ++ tailWord_3530132) baseStart_3530132 baseEnd_3530132 := by
    simpa [prefixWord, tailWord_3530132, baseEnd_3530132] using wordTrace_append hprefix tailTrace_3530132
  have hstable : (prefixWord ++ tailWord_3530132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530132).length < 2 ^ (prefixWord ++ tailWord_3530132).sum := by decide
  have hdescent : baseEnd_3530132 < baseStart_3530132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530152 : List Nat := [2, 1, 6, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_3530152 : Nat := 118140960795 + 3530152 * 2 ^ 59
def prefixEnd_3530152 : Nat := 4983230072969 + 3 ^ 40 * 3530152 * 2
def baseEnd_3530152 : Nat := 1812664759430777497765133

theorem tailTrace_3530152 : CollatzResearch.WordTrace tailWord_3530152 prefixEnd_3530152 1812664759430777497765133 := by
  unfold tailWord_3530152
  simp only [CollatzResearch.WordTrace]
  refine ⟨64377610553434840403616355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85836814071246453871488473 64377610553434840403616355)
  ·
    refine ⟨96566415830152260605424533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64377610553434840403616355 96566415830152260605424533)
    ·
      refine ⟨4526550742038387215879275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 96566415830152260605424533 4526550742038387215879275)
      ·
        refine ⟨6789826113057580823818913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4526550742038387215879275 6789826113057580823818913)
        ·
          refine ⟨5092369584793185617864185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6789826113057580823818913 5092369584793185617864185)
          ·
            refine ⟨3819277188594889213398139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5092369584793185617864185 3819277188594889213398139)
            ·
              refine ⟨5728915782892333820097209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3819277188594889213398139 5728915782892333820097209)
              ·
                refine ⟨4296686837169250365072907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5728915782892333820097209 4296686837169250365072907)
                ·
                  refine ⟨6445030255753875547609361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4296686837169250365072907 6445030255753875547609361)
                  ·
                    refine ⟨4833772691815406660707021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6445030255753875547609361 4833772691815406660707021)
                    ·
                      refine ⟨1812664759430777497765133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4833772691815406660707021 1812664759430777497765133)
                      ·
                        rfl

theorem cell23_3530152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_3530152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530152 prefixEnd_3530152 := by exact prefixLift 3530152
  have htrace : WordTrace (prefixWord ++ tailWord_3530152) baseStart_3530152 baseEnd_3530152 := by
    simpa [prefixWord, tailWord_3530152, baseEnd_3530152] using wordTrace_append hprefix tailTrace_3530152
  have hstable : (prefixWord ++ tailWord_3530152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530152).length < 2 ^ (prefixWord ++ tailWord_3530152).sum := by decide
  have hdescent : baseEnd_3530152 < baseStart_3530152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530198 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_3530198 : Nat := 118140960795 + 3530198 * 2 ^ 59
def prefixEnd_3530198 : Nat := 4983230072969 + 3 ^ 40 * 3530198 * 2
def baseEnd_3530198 : Nat := 604229459846961439263307

theorem tailTrace_3530198 : CollatzResearch.WordTrace tailWord_3530198 prefixEnd_3530198 604229459846961439263307 := by
  unfold tailWord_3530198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8047306179043939416462953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85837932576468687108938165 8047306179043939416462953)
  ·
    refine ⟨6035479634282954562347215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8047306179043939416462953 6035479634282954562347215)
    ·
      refine ⟨9053219451424431843520823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6035479634282954562347215 9053219451424431843520823)
      ·
        refine ⟨13579829177136647765281235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9053219451424431843520823 13579829177136647765281235)
        ·
          refine ⟨20369743765704971647921853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13579829177136647765281235 20369743765704971647921853)
          ·
            refine ⟨7638653912139364367970695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20369743765704971647921853 7638653912139364367970695)
            ·
              refine ⟨11457980868209046551956043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7638653912139364367970695 11457980868209046551956043)
              ·
                refine ⟨17186971302313569827934065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11457980868209046551956043 17186971302313569827934065)
                ·
                  refine ⟨12890228476735177370950549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17186971302313569827934065 12890228476735177370950549)
                  ·
                    refine ⟨604229459846961439263307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12890228476735177370950549 604229459846961439263307)
                    ·
                      rfl

theorem cell23_3530198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_3530198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530198 prefixEnd_3530198 := by exact prefixLift 3530198
  have htrace : WordTrace (prefixWord ++ tailWord_3530198) baseStart_3530198 baseEnd_3530198 := by
    simpa [prefixWord, tailWord_3530198, baseEnd_3530198] using wordTrace_append hprefix tailTrace_3530198
  have hstable : (prefixWord ++ tailWord_3530198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530198).length < 2 ^ (prefixWord ++ tailWord_3530198).sum := by decide
  have hdescent : baseEnd_3530198 < baseStart_3530198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530201 : List Nat := [1, 2, 1, 2, 4, 3, 1, 1, 2, 2, 4]
def baseStart_3530201 : Nat := 118140960795 + 3530201 * 2 ^ 59
def prefixEnd_3530201 : Nat := 4983230072969 + 3 ^ 40 * 3530201 * 2
def baseEnd_3530201 : Nat := 1812689919982847806052407

theorem tailTrace_3530201 : CollatzResearch.WordTrace tailWord_3530201 prefixEnd_3530201 1812689919982847806052407 := by
  unfold tailWord_3530201
  simp only [CollatzResearch.WordTrace]
  refine ⟨128757008283692162175766457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85838005522461441450510971 128757008283692162175766457)
  ·
    refine ⟨96567756212769121631824843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128757008283692162175766457 96567756212769121631824843)
    ·
      refine ⟨144851634319153682447737265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96567756212769121631824843 144851634319153682447737265)
      ·
        refine ⟨108638725739365261835802949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144851634319153682447737265 108638725739365261835802949)
        ·
          refine ⟨20369761076130986594213053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108638725739365261835802949 20369761076130986594213053)
          ·
            refine ⟨7638660403549119972829895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20369761076130986594213053 7638660403549119972829895)
            ·
              refine ⟨11457990605323679959244843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7638660403549119972829895 11457990605323679959244843)
              ·
                refine ⟨17186985907985519938867265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11457990605323679959244843 17186985907985519938867265)
                ·
                  refine ⟨12890239430989139954150449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17186985907985519938867265 12890239430989139954150449)
                  ·
                    refine ⟨9667679573241854965612837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12890239430989139954150449 9667679573241854965612837)
                    ·
                      refine ⟨1812689919982847806052407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9667679573241854965612837 1812689919982847806052407)
                      ·
                        rfl

theorem cell23_3530201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_3530201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530201 prefixEnd_3530201 := by exact prefixLift 3530201
  have htrace : WordTrace (prefixWord ++ tailWord_3530201) baseStart_3530201 baseEnd_3530201 := by
    simpa [prefixWord, tailWord_3530201, baseEnd_3530201] using wordTrace_append hprefix tailTrace_3530201
  have hstable : (prefixWord ++ tailWord_3530201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530201).length < 2 ^ (prefixWord ++ tailWord_3530201).sum := by decide
  have hdescent : baseEnd_3530201 < baseStart_3530201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530205 : List Nat := [1, 4, 3, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_3530205 : Nat := 118140960795 + 3530205 * 2 ^ 59
def prefixEnd_3530205 : Nat := 4983230072969 + 3 ^ 40 * 3530205 * 2
def baseEnd_3530205 : Nat := 1812691973905465790402389

theorem tailTrace_3530205 : CollatzResearch.WordTrace tailWord_3530205 prefixEnd_3530205 1812691973905465790402389 := by
  unfold tailWord_3530205
  simp only [CollatzResearch.WordTrace]
  refine ⟨128757154175677670858912069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85838102783785113905941379 128757154175677670858912069)
  ·
    refine ⟨24141966407939563286046013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128757154175677670858912069 24141966407939563286046013)
    ·
      refine ⟨9053237402977336232267255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24141966407939563286046013 9053237402977336232267255)
      ·
        refine ⟨13579856104466004348400883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9053237402977336232267255 13579856104466004348400883)
        ·
          refine ⟨20369784156699006522601325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13579856104466004348400883 20369784156699006522601325)
          ·
            refine ⟨7638669058762127445975497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20369784156699006522601325 7638669058762127445975497)
            ·
              refine ⟨5729001794071595584481623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7638669058762127445975497 5729001794071595584481623)
              ·
                refine ⟨8593502691107393376722435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5729001794071595584481623 8593502691107393376722435)
                ·
                  refine ⟨12890254036661090065083653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8593502691107393376722435 12890254036661090065083653)
                  ·
                    refine ⟨2416922631873954387203185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12890254036661090065083653 2416922631873954387203185)
                    ·
                      refine ⟨1812691973905465790402389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2416922631873954387203185 1812691973905465790402389)
                      ·
                        rfl

theorem cell23_3530205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_3530205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530205 prefixEnd_3530205 := by exact prefixLift 3530205
  have htrace : WordTrace (prefixWord ++ tailWord_3530205) baseStart_3530205 baseEnd_3530205 := by
    simpa [prefixWord, tailWord_3530205, baseEnd_3530205] using wordTrace_append hprefix tailTrace_3530205
  have hstable : (prefixWord ++ tailWord_3530205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530205).length < 2 ^ (prefixWord ++ tailWord_3530205).sum := by decide
  have hdescent : baseEnd_3530205 < baseStart_3530205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530211 : List Nat := [1, 1, 1, 6, 2, 2, 1, 2, 7]
def baseStart_3530211 : Nat := 118140960795 + 3530211 * 2 ^ 59
def prefixEnd_3530211 : Nat := 4983230072969 + 3 ^ 40 * 3530211 * 2
def baseEnd_3530211 : Nat := 201410561643265862991929

theorem tailTrace_3530211 : CollatzResearch.WordTrace tailWord_3530211 prefixEnd_3530211 201410561643265862991929 := by
  unfold tailWord_3530211
  simp only [CollatzResearch.WordTrace]
  refine ⟨128757373013655933883630487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85838248675770622589086991 128757373013655933883630487)
  ·
    refine ⟨193136059520483900825445731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128757373013655933883630487 193136059520483900825445731)
    ·
      refine ⟨289704089280725851238168597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193136059520483900825445731 289704089280725851238168597)
      ·
        refine ⟨13579879185034024276789153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 289704089280725851238168597 13579879185034024276789153)
        ·
          refine ⟨10184909388775518207591865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13579879185034024276789153 10184909388775518207591865)
          ·
            refine ⟨7638682041581638655693899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10184909388775518207591865 7638682041581638655693899)
            ·
              refine ⟨11458023062372457983540849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7638682041581638655693899 11458023062372457983540849)
              ·
                refine ⟨8593517296779343487655637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11458023062372457983540849 8593517296779343487655637)
                ·
                  refine ⟨201410561643265862991929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8593517296779343487655637 201410561643265862991929)
                  ·
                    rfl

theorem cell23_3530211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 7].length) (baseStart_3530211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530211 prefixEnd_3530211 := by exact prefixLift 3530211
  have htrace : WordTrace (prefixWord ++ tailWord_3530211) baseStart_3530211 baseEnd_3530211 := by
    simpa [prefixWord, tailWord_3530211, baseEnd_3530211] using wordTrace_append hprefix tailTrace_3530211
  have hstable : (prefixWord ++ tailWord_3530211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530211).length < 2 ^ (prefixWord ++ tailWord_3530211).sum := by decide
  have hdescent : baseEnd_3530211 < baseStart_3530211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530231 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 1, 7, 2]
def baseStart_3530231 : Nat := 118140960795 + 3530231 * 2 ^ 59
def prefixEnd_3530231 : Nat := 4983230072969 + 3 ^ 40 * 3530231 * 2
def baseEnd_3530231 : Nat := 1812705324402482688677269

theorem tailTrace_3530231 : CollatzResearch.WordTrace tailWord_3530231 prefixEnd_3530231 1812705324402482688677269 := by
  unfold tailWord_3530231
  simp only [CollatzResearch.WordTrace]
  refine ⟨128758102473583477299358547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85838734982388984866239031 128758102473583477299358547)
  ·
    refine ⟨193137153710375215949037821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128758102473583477299358547 193137153710375215949037821)
    ·
      refine ⟨72426432641390705980889183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193137153710375215949037821 72426432641390705980889183)
      ·
        refine ⟨108639648962086058971333775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72426432641390705980889183 108639648962086058971333775)
        ·
          refine ⟨162959473443129088457000663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108639648962086058971333775 162959473443129088457000663)
          ·
            refine ⟨244439210164693632685500995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162959473443129088457000663 244439210164693632685500995)
            ·
              refine ⟨366658815247040449028251493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244439210164693632685500995 366658815247040449028251493)
              ·
                refine ⟨68748527858820084192797155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 366658815247040449028251493 68748527858820084192797155)
                ·
                  refine ⟨103122791788230126289195733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68748527858820084192797155 103122791788230126289195733)
                  ·
                    refine ⟨2416940432536643584903025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 103122791788230126289195733 2416940432536643584903025)
                    ·
                      refine ⟨1812705324402482688677269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2416940432536643584903025 1812705324402482688677269)
                      ·
                        rfl

theorem cell23_3530231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 7, 2].length) (baseStart_3530231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530231 prefixEnd_3530231 := by exact prefixLift 3530231
  have htrace : WordTrace (prefixWord ++ tailWord_3530231) baseStart_3530231 baseEnd_3530231 := by
    simpa [prefixWord, tailWord_3530231, baseEnd_3530231] using wordTrace_append hprefix tailTrace_3530231
  have hstable : (prefixWord ++ tailWord_3530231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530231).length < 2 ^ (prefixWord ++ tailWord_3530231).sum := by decide
  have hdescent : baseEnd_3530231 < baseStart_3530231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530261 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_3530261 : Nat := 118140960795 + 3530261 * 2 ^ 59
def prefixEnd_3530261 : Nat := 4983230072969 + 3 ^ 40 * 3530261 * 2
def baseEnd_3530261 : Nat := 1812720728822117571302131

theorem tailTrace_3530261 : CollatzResearch.WordTrace tailWord_3530261 prefixEnd_3530261 1812720728822117571302131 := by
  unfold tailWord_3530261
  simp only [CollatzResearch.WordTrace]
  refine ⟨128759196663474792422950637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85839464442316528281967091 128759196663474792422950637)
  ·
    refine ⟨48284698748803047158606489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128759196663474792422950637 48284698748803047158606489)
    ·
      refine ⟨36213524061602285368954867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48284698748803047158606489 36213524061602285368954867)
      ·
        refine ⟨54320286092403428053432301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36213524061602285368954867 54320286092403428053432301)
        ·
          refine ⟨20370107284651285520037113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54320286092403428053432301 20370107284651285520037113)
          ·
            refine ⟨15277580463488464140027835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20370107284651285520037113 15277580463488464140027835)
            ·
              refine ⟨22916370695232696210041753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15277580463488464140027835 22916370695232696210041753)
              ·
                refine ⟨17187278021424522157531315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22916370695232696210041753 17187278021424522157531315)
                ·
                  refine ⟨25780917032136783236296973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17187278021424522157531315 25780917032136783236296973)
                  ·
                    refine ⟨9667843887051293713611365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25780917032136783236296973 9667843887051293713611365)
                    ·
                      refine ⟨1812720728822117571302131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9667843887051293713611365 1812720728822117571302131)
                      ·
                        rfl

theorem cell23_3530261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_3530261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530261 prefixEnd_3530261 := by exact prefixLift 3530261
  have htrace : WordTrace (prefixWord ++ tailWord_3530261) baseStart_3530261 baseEnd_3530261 := by
    simpa [prefixWord, tailWord_3530261, baseEnd_3530261] using wordTrace_append hprefix tailTrace_3530261
  have hstable : (prefixWord ++ tailWord_3530261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530261).length < 2 ^ (prefixWord ++ tailWord_3530261).sum := by decide
  have hdescent : baseEnd_3530261 < baseStart_3530261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530298 : List Nat := [3, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3]
def baseStart_3530298 : Nat := 118140960795 + 3530298 * 2 ^ 59
def prefixEnd_3530298 : Nat := 4983230072969 + 3 ^ 40 * 3530298 * 2
def baseEnd_3530298 : Nat := 1812739727606333926539461

theorem tailTrace_3530298 : CollatzResearch.WordTrace tailWord_3530298 prefixEnd_3530298 1812739727606333926539461 := by
  unfold tailWord_3530298
  simp only [CollatzResearch.WordTrace]
  refine ⟨32190136541085186935511887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85840364109560498494698365 32190136541085186935511887)
  ·
    refine ⟨48285204811627780403267831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32190136541085186935511887 48285204811627780403267831)
    ·
      refine ⟨72427807217441670604901747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48285204811627780403267831 72427807217441670604901747)
      ·
        refine ⟨108641710826162505907352621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72427807217441670604901747 108641710826162505907352621)
        ·
          refine ⟨40740641559810939715257233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108641710826162505907352621 40740641559810939715257233)
          ·
            refine ⟨30555481169858204786442925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40740641559810939715257233 30555481169858204786442925)
            ·
              refine ⟨11458305438696826794916097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30555481169858204786442925 11458305438696826794916097)
              ·
                refine ⟨8593729079022620096187073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11458305438696826794916097 8593729079022620096187073)
                ·
                  refine ⟨6445296809266965072140305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8593729079022620096187073 6445296809266965072140305)
                  ·
                    refine ⟨4833972606950223804105229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6445296809266965072140305 4833972606950223804105229)
                    ·
                      refine ⟨1812739727606333926539461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4833972606950223804105229 1812739727606333926539461)
                      ·
                        rfl

theorem cell23_3530298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_3530298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530298 prefixEnd_3530298 := by exact prefixLift 3530298
  have htrace : WordTrace (prefixWord ++ tailWord_3530298) baseStart_3530298 baseEnd_3530298 := by
    simpa [prefixWord, tailWord_3530298, baseEnd_3530298] using wordTrace_append hprefix tailTrace_3530298
  have hstable : (prefixWord ++ tailWord_3530298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530298).length < 2 ^ (prefixWord ++ tailWord_3530298).sum := by decide
  have hdescent : baseEnd_3530298 < baseStart_3530298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530328 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 5, 1, 3]
def baseStart_3530328 : Nat := 118140960795 + 3530328 * 2 ^ 59
def prefixEnd_3530328 : Nat := 4983230072969 + 3 ^ 40 * 3530328 * 2
def baseEnd_3530328 : Nat := 1812755132025968809164323

theorem tailTrace_3530328 : CollatzResearch.WordTrace tailWord_3530328 prefixEnd_3530328 1812755132025968809164323 := by
  unfold tailWord_3530328
  simp only [CollatzResearch.WordTrace]
  refine ⟨64380820177116031432819819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85841093569488041910426425 64380820177116031432819819)
  ·
    refine ⟨96571230265674047149229729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64380820177116031432819819 96571230265674047149229729)
    ·
      refine ⟨72428422699255535361922297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96571230265674047149229729 72428422699255535361922297)
      ·
        refine ⟨54321317024441651521441723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72428422699255535361922297 54321317024441651521441723)
        ·
          refine ⟨81481975536662477282162585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54321317024441651521441723 81481975536662477282162585)
          ·
            refine ⟨61111481652496857961621939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81481975536662477282162585 61111481652496857961621939)
            ·
              refine ⟨91667222478745286942432909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61111481652496857961621939 91667222478745286942432909)
              ·
                refine ⟨34375208429529482603412341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91667222478745286942432909 34375208429529482603412341)
                ·
                  refine ⟨3222675790268388994069907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34375208429529482603412341 3222675790268388994069907)
                  ·
                    refine ⟨4834013685402583491104861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3222675790268388994069907 4834013685402583491104861)
                    ·
                      refine ⟨1812755132025968809164323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4834013685402583491104861 1812755132025968809164323)
                      ·
                        rfl

theorem cell23_3530328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_3530328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530328 prefixEnd_3530328 := by exact prefixLift 3530328
  have htrace : WordTrace (prefixWord ++ tailWord_3530328) baseStart_3530328 baseEnd_3530328 := by
    simpa [prefixWord, tailWord_3530328, baseEnd_3530328] using wordTrace_append hprefix tailTrace_3530328
  have hstable : (prefixWord ++ tailWord_3530328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530328).length < 2 ^ (prefixWord ++ tailWord_3530328).sum := by decide
  have hdescent : baseEnd_3530328 < baseStart_3530328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530361 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 3, 6]
def baseStart_3530361 : Nat := 118140960795 + 3530361 * 2 ^ 59
def prefixEnd_3530361 : Nat := 4983230072969 + 3 ^ 40 * 3530361 * 2
def baseEnd_3530361 : Nat := 604257358962522393350557

theorem tailTrace_3530361 : CollatzResearch.WordTrace tailWord_3530361 prefixEnd_3530361 604257358962522393350557 := by
  unfold tailWord_3530361
  simp only [CollatzResearch.WordTrace]
  refine ⟨128762843963112509501590937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85841895975408339667727291 128762843963112509501590937)
  ·
    refine ⟨96572132972334382126193203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128762843963112509501590937 96572132972334382126193203)
    ·
      refine ⟨144858199458501573189289805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96572132972334382126193203 144858199458501573189289805)
      ·
        refine ⟨54321824796938089945983677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144858199458501573189289805 54321824796938089945983677)
        ·
          refine ⟨20370684298851783729743879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54321824796938089945983677 20370684298851783729743879)
          ·
            refine ⟨30556026448277675594615819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20370684298851783729743879 30556026448277675594615819)
            ·
              refine ⟨45834039672416513391923729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30556026448277675594615819 45834039672416513391923729)
              ·
                refine ⟨34375529754312385043942797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45834039672416513391923729 34375529754312385043942797)
                ·
                  refine ⟨12890823657867144391478549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34375529754312385043942797 12890823657867144391478549)
                  ·
                    refine ⟨604257358962522393350557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12890823657867144391478549 604257358962522393350557)
                    ·
                      rfl

theorem cell23_3530361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 6].length) (baseStart_3530361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530361 prefixEnd_3530361 := by exact prefixLift 3530361
  have htrace : WordTrace (prefixWord ++ tailWord_3530361) baseStart_3530361 baseEnd_3530361 := by
    simpa [prefixWord, tailWord_3530361, baseEnd_3530361] using wordTrace_append hprefix tailTrace_3530361
  have hstable : (prefixWord ++ tailWord_3530361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530361).length < 2 ^ (prefixWord ++ tailWord_3530361).sum := by decide
  have hdescent : baseEnd_3530361 < baseStart_3530361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530371 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 5]
def baseStart_3530371 : Nat := 118140960795 + 3530371 * 2 ^ 59
def prefixEnd_3530371 : Nat := 4983230072969 + 3 ^ 40 * 3530371 * 2
def baseEnd_3530371 : Nat := 1812777211694112140926625

theorem tailTrace_3530371 : CollatzResearch.WordTrace tailWord_3530371 prefixEnd_3530371 1812777211694112140926625 := by
  unfold tailWord_3530371
  simp only [CollatzResearch.WordTrace]
  refine ⟨128763208693076281209454967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85842139128717520806303311 128763208693076281209454967)
  ·
    refine ⟨193144813039614421814182451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128763208693076281209454967 193144813039614421814182451)
    ·
      refine ⟨289717219559421632721273677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193144813039614421814182451 289717219559421632721273677)
      ·
        refine ⟨108643957334783112270477629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289717219559421632721273677 108643957334783112270477629)
        ·
          refine ⟨40741484000543667101429111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108643957334783112270477629 40741484000543667101429111)
          ·
            refine ⟨61112226000815500652143667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40741484000543667101429111 61112226000815500652143667)
            ·
              refine ⟨91668339001223250978215501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61112226000815500652143667 91668339001223250978215501)
              ·
                refine ⟨34375627125458719116830813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91668339001223250978215501 34375627125458719116830813)
                ·
                  refine ⟨12890860172047019668811555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34375627125458719116830813 12890860172047019668811555)
                  ·
                    refine ⟨19336290258070529503217333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12890860172047019668811555 19336290258070529503217333)
                    ·
                      refine ⟨1812777211694112140926625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19336290258070529503217333 1812777211694112140926625)
                      ·
                        rfl

theorem cell23_3530371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_3530371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530371 prefixEnd_3530371 := by exact prefixLift 3530371
  have htrace : WordTrace (prefixWord ++ tailWord_3530371) baseStart_3530371 baseEnd_3530371 := by
    simpa [prefixWord, tailWord_3530371, baseEnd_3530371] using wordTrace_append hprefix tailTrace_3530371
  have hstable : (prefixWord ++ tailWord_3530371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530371).length < 2 ^ (prefixWord ++ tailWord_3530371).sum := by decide
  have hdescent : baseEnd_3530371 < baseStart_3530371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530378 : List Nat := [3, 1, 2, 3, 2, 1, 1, 3, 1, 6]
def baseStart_3530378 : Nat := 118140960795 + 3530378 * 2 ^ 59
def prefixEnd_3530378 : Nat := 4983230072969 + 3 ^ 40 * 3530378 * 2
def baseEnd_3530378 : Nat := 604260268686231204513031

theorem tailTrace_3530378 : CollatzResearch.WordTrace tailWord_3530378 prefixEnd_3530378 604260268686231204513031 := by
  unfold tailWord_3530378
  simp only [CollatzResearch.WordTrace]
  refine ⟨32190866001012730351239947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85842309336033947603306525 32190866001012730351239947)
  ·
    refine ⟨48286299001519095526859921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32190866001012730351239947 48286299001519095526859921)
    ·
      refine ⟨36214724251139321645144941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48286299001519095526859921 36214724251139321645144941)
      ·
        refine ⟨13580521594177245616929353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36214724251139321645144941 13580521594177245616929353)
        ·
          refine ⟨10185391195632934212697015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13580521594177245616929353 10185391195632934212697015)
          ·
            refine ⟨15278086793449401319045523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10185391195632934212697015 15278086793449401319045523)
            ·
              refine ⟨22917130190174101978568285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15278086793449401319045523 22917130190174101978568285)
              ·
                refine ⟨8593923821315288241963107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22917130190174101978568285 8593923821315288241963107)
                ·
                  refine ⟨12890885731972932362944661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8593923821315288241963107 12890885731972932362944661)
                  ·
                    refine ⟨604260268686231204513031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12890885731972932362944661 604260268686231204513031)
                    ·
                      rfl

theorem cell23_3530378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_3530378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530378 prefixEnd_3530378 := by exact prefixLift 3530378
  have htrace : WordTrace (prefixWord ++ tailWord_3530378) baseStart_3530378 baseEnd_3530378 := by
    simpa [prefixWord, tailWord_3530378, baseEnd_3530378] using wordTrace_append hprefix tailTrace_3530378
  have hstable : (prefixWord ++ tailWord_3530378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530378).length < 2 ^ (prefixWord ++ tailWord_3530378).sum := by decide
  have hdescent : baseEnd_3530378 < baseStart_3530378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530399 : List Nat := [1, 1, 2, 7, 1, 2, 2, 1, 1, 5]
def baseStart_3530399 : Nat := 118140960795 + 3530399 * 2 ^ 59
def prefixEnd_3530399 : Nat := 4983230072969 + 3 ^ 40 * 3530399 * 2
def baseEnd_3530399 : Nat := 604263863050812677125499

theorem tailTrace_3530399 : CollatzResearch.WordTrace tailWord_3530399 prefixEnd_3530399 604263863050812677125499 := by
  unfold tailWord_3530399
  simp only [CollatzResearch.WordTrace]
  refine ⟨128764229936974841991474251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85842819957983227994316167 128764229936974841991474251)
  ·
    refine ⟨193146344905462262987211377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128764229936974841991474251 193146344905462262987211377)
    ·
      refine ⟨144859758679096697240408533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193146344905462262987211377 144859758679096697240408533)
      ·
        refine ⟨3395150594041328841572075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 144859758679096697240408533 3395150594041328841572075)
        ·
          refine ⟨5092725891061993262358113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3395150594041328841572075 5092725891061993262358113)
          ·
            refine ⟨3819544418296494946768585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5092725891061993262358113 3819544418296494946768585)
            ·
              refine ⟨2864658313722371210076439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3819544418296494946768585 2864658313722371210076439)
              ·
                refine ⟨4296987470583556815114659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2864658313722371210076439 4296987470583556815114659)
                ·
                  refine ⟨6445481205875335222671989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4296987470583556815114659 6445481205875335222671989)
                  ·
                    refine ⟨604263863050812677125499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6445481205875335222671989 604263863050812677125499)
                    ·
                      rfl

theorem cell23_3530399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 1, 5].length) (baseStart_3530399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530399 prefixEnd_3530399 := by exact prefixLift 3530399
  have htrace : WordTrace (prefixWord ++ tailWord_3530399) baseStart_3530399 baseEnd_3530399 := by
    simpa [prefixWord, tailWord_3530399, baseEnd_3530399] using wordTrace_append hprefix tailTrace_3530399
  have hstable : (prefixWord ++ tailWord_3530399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530399).length < 2 ^ (prefixWord ++ tailWord_3530399).sum := by decide
  have hdescent : baseEnd_3530399 < baseStart_3530399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530418 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3]
def baseStart_3530418 : Nat := 118140960795 + 3530418 * 2 ^ 59
def prefixEnd_3530418 : Nat := 4983230072969 + 3 ^ 40 * 3530418 * 2
def baseEnd_3530418 : Nat := 1812801345284873457038909

theorem tailTrace_3530418 : CollatzResearch.WordTrace tailWord_3530418 prefixEnd_3530418 1812801345284873457038909 := by
  unfold tailWord_3530418
  simp only [CollatzResearch.WordTrace]
  refine ⟨32191230730976502059103977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85843281949270672157610605 32191230730976502059103977)
  ·
    refine ⟨24143423048232376544327983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32191230730976502059103977 24143423048232376544327983)
    ·
      refine ⟨36215134572348564816491975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24143423048232376544327983 36215134572348564816491975)
      ·
        refine ⟨54322701858522847224737963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36215134572348564816491975 54322701858522847224737963)
        ·
          refine ⟨81484052787784270837106945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54322701858522847224737963 81484052787784270837106945)
          ·
            refine ⟨61113039590838203127830209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81484052787784270837106945 61113039590838203127830209)
            ·
              refine ⟨45834779693128652345872657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61113039590838203127830209 45834779693128652345872657)
              ·
                refine ⟨34376084769846489259404493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45834779693128652345872657 34376084769846489259404493)
                ·
                  refine ⟨12891031788692433472276685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34376084769846489259404493 12891031788692433472276685)
                  ·
                    refine ⟨4834136920759662552103757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12891031788692433472276685 4834136920759662552103757)
                    ·
                      refine ⟨1812801345284873457038909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4834136920759662552103757 1812801345284873457038909)
                      ·
                        rfl

theorem cell23_3530418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_3530418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530418 prefixEnd_3530418 := by exact prefixLift 3530418
  have htrace : WordTrace (prefixWord ++ tailWord_3530418) baseStart_3530418 baseEnd_3530418 := by
    simpa [prefixWord, tailWord_3530418, baseEnd_3530418] using wordTrace_append hprefix tailTrace_3530418
  have hstable : (prefixWord ++ tailWord_3530418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530418).length < 2 ^ (prefixWord ++ tailWord_3530418).sum := by decide
  have hdescent : baseEnd_3530418 < baseStart_3530418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530422 : List Nat := [5, 1, 3, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_3530422 : Nat := 118140960795 + 3530422 * 2 ^ 59
def prefixEnd_3530422 : Nat := 4983230072969 + 3 ^ 40 * 3530422 * 2
def baseEnd_3530422 : Nat := 1812803399207491441388891

theorem tailTrace_3530422 : CollatzResearch.WordTrace tailWord_3530422 prefixEnd_3530422 1812803399207491441388891 := by
  unfold tailWord_3530422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8047816800993219807472595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85843379210594344613041013 8047816800993219807472595)
  ·
    refine ⟨12071725201489829711208893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8047816800993219807472595 12071725201489829711208893)
    ·
      refine ⟨4526896950558686141703335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12071725201489829711208893 4526896950558686141703335)
      ·
        refine ⟨6790345425838029212555003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4526896950558686141703335 6790345425838029212555003)
        ·
          refine ⟨10185518138757043818832505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6790345425838029212555003 10185518138757043818832505)
          ·
            refine ⟨7639138604067782864124379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10185518138757043818832505 7639138604067782864124379)
            ·
              refine ⟨11458707906101674296186569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7639138604067782864124379 11458707906101674296186569)
              ·
                refine ⟨8594030929576255722139927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11458707906101674296186569 8594030929576255722139927)
                ·
                  refine ⟨12891046394364383583209891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8594030929576255722139927 12891046394364383583209891)
                  ·
                    refine ⟨19336569591546575374814837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12891046394364383583209891 19336569591546575374814837)
                    ·
                      refine ⟨1812803399207491441388891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19336569591546575374814837 1812803399207491441388891)
                      ·
                        rfl

theorem cell23_3530422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_3530422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530422 prefixEnd_3530422 := by exact prefixLift 3530422
  have htrace : WordTrace (prefixWord ++ tailWord_3530422) baseStart_3530422 baseEnd_3530422 := by
    simpa [prefixWord, tailWord_3530422, baseEnd_3530422] using wordTrace_append hprefix tailTrace_3530422
  have hstable : (prefixWord ++ tailWord_3530422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530422).length < 2 ^ (prefixWord ++ tailWord_3530422).sum := by decide
  have hdescent : baseEnd_3530422 < baseStart_3530422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530442 : List Nat := [3, 1, 2, 1, 6, 1, 2, 7]
def baseStart_3530442 : Nat := 118140960795 + 3530442 * 2 ^ 59
def prefixEnd_3530442 : Nat := 4983230072969 + 3 ^ 40 * 3530442 * 2
def baseEnd_3530442 : Nat := 67141246993354865301437

theorem tailTrace_3530442 : CollatzResearch.WordTrace tailWord_3530442 prefixEnd_3530442 67141246993354865301437 := by
  unfold tailWord_3530442
  simp only [CollatzResearch.WordTrace]
  refine ⟨32191449568954765083822395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85843865517212706890193053 32191449568954765083822395)
  ·
    refine ⟨48287174353432147625733593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32191449568954765083822395 48287174353432147625733593)
    ·
      refine ⟨36215380765074110719300195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48287174353432147625733593 36215380765074110719300195)
      ·
        refine ⟨54323071147611166078950293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36215380765074110719300195 54323071147611166078950293)
        ·
          refine ⟨2546393960044273409950795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 54323071147611166078950293 2546393960044273409950795)
          ·
            refine ⟨3819590940066410114926193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2546393960044273409950795 3819590940066410114926193)
            ·
              refine ⟨2864693205049807586194645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3819590940066410114926193 2864693205049807586194645)
              ·
                refine ⟨67141246993354865301437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2864693205049807586194645 67141246993354865301437)
                ·
                  rfl

theorem cell23_3530442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 7].length) (baseStart_3530442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530442 prefixEnd_3530442 := by exact prefixLift 3530442
  have htrace : WordTrace (prefixWord ++ tailWord_3530442) baseStart_3530442 baseEnd_3530442 := by
    simpa [prefixWord, tailWord_3530442, baseEnd_3530442] using wordTrace_append hprefix tailTrace_3530442
  have hstable : (prefixWord ++ tailWord_3530442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530442).length < 2 ^ (prefixWord ++ tailWord_3530442).sum := by decide
  have hdescent : baseEnd_3530442 < baseStart_3530442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530452 : List Nat := [2, 4, 1, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_3530452 : Nat := 118140960795 + 3530452 * 2 ^ 59
def prefixEnd_3530452 : Nat := 4983230072969 + 3 ^ 40 * 3530452 * 2
def baseEnd_3530452 : Nat := 1812818803627126324013753

theorem tailTrace_3530452 : CollatzResearch.WordTrace tailWord_3530452 prefixEnd_3530452 1812818803627126324013753 := by
  unfold tailWord_3530452
  simp only [CollatzResearch.WordTrace]
  refine ⟨64383081502891416021576805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85844108670521888028769073 64383081502891416021576805)
  ·
    refine ⟨12071827781792140504045651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64383081502891416021576805 12071827781792140504045651)
    ·
      refine ⟨18107741672688210756068477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12071827781792140504045651 18107741672688210756068477)
      ·
        refine ⟨6790403127258079033525679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18107741672688210756068477 6790403127258079033525679)
        ·
          refine ⟨10185604690887118550288519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6790403127258079033525679 10185604690887118550288519)
          ·
            refine ⟨15278407036330677825432779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10185604690887118550288519 15278407036330677825432779)
            ·
              refine ⟨22917610554496016738149169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15278407036330677825432779 22917610554496016738149169)
              ·
                refine ⟨17188207915872012553611877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22917610554496016738149169 17188207915872012553611877)
                ·
                  refine ⟨3222788984226002353802227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17188207915872012553611877 3222788984226002353802227)
                  ·
                    refine ⟨4834183476339003530703341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3222788984226002353802227 4834183476339003530703341)
                    ·
                      refine ⟨1812818803627126324013753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4834183476339003530703341 1812818803627126324013753)
                      ·
                        rfl

theorem cell23_3530452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_3530452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530452 prefixEnd_3530452 := by exact prefixLift 3530452
  have htrace : WordTrace (prefixWord ++ tailWord_3530452) baseStart_3530452 baseEnd_3530452 := by
    simpa [prefixWord, tailWord_3530452, baseEnd_3530452] using wordTrace_append hprefix tailTrace_3530452
  have hstable : (prefixWord ++ tailWord_3530452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530452).length < 2 ^ (prefixWord ++ tailWord_3530452).sum := by decide
  have hdescent : baseEnd_3530452 < baseStart_3530452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530478 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_3530478 : Nat := 118140960795 + 3530478 * 2 ^ 59
def prefixEnd_3530478 : Nat := 4983230072969 + 3 ^ 40 * 3530478 * 2
def baseEnd_3530478 : Nat := 1812832154124143222288633

theorem tailTrace_3530478 : CollatzResearch.WordTrace tailWord_3530478 prefixEnd_3530478 1812832154124143222288633 := by
  unfold tailWord_3530478
  simp only [CollatzResearch.WordTrace]
  refine ⟨16095888912961079810450011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85844740869125758989066725 16095888912961079810450011)
  ·
    refine ⟨24143833369441619715675017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16095888912961079810450011 24143833369441619715675017)
    ·
      refine ⟨18107875027081214786756263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24143833369441619715675017 18107875027081214786756263)
      ·
        refine ⟨27161812540621822180134395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18107875027081214786756263 27161812540621822180134395)
        ·
          refine ⟨40742718810932733270201593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27161812540621822180134395 40742718810932733270201593)
          ·
            refine ⟨30557039108199549952651195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40742718810932733270201593 30557039108199549952651195)
            ·
              refine ⟨45835558662299324928976793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30557039108199549952651195 45835558662299324928976793)
              ·
                refine ⟨34376668996724493696732595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45835558662299324928976793 34376668996724493696732595)
                ·
                  refine ⟨51565003495086740545098893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34376668996724493696732595 51565003495086740545098893)
                  ·
                    refine ⟨19336876310657527704412085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51565003495086740545098893 19336876310657527704412085)
                    ·
                      refine ⟨1812832154124143222288633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19336876310657527704412085 1812832154124143222288633)
                      ·
                        rfl

theorem cell23_3530478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_3530478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530478 prefixEnd_3530478 := by exact prefixLift 3530478
  have htrace : WordTrace (prefixWord ++ tailWord_3530478) baseStart_3530478 baseEnd_3530478 := by
    simpa [prefixWord, tailWord_3530478, baseEnd_3530478] using wordTrace_append hprefix tailTrace_3530478
  have hstable : (prefixWord ++ tailWord_3530478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530478).length < 2 ^ (prefixWord ++ tailWord_3530478).sum := by decide
  have hdescent : baseEnd_3530478 < baseStart_3530478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530486 : List Nat := [5, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3]
def baseStart_3530486 : Nat := 118140960795 + 3530486 * 2 ^ 59
def prefixEnd_3530486 : Nat := 4983230072969 + 3 ^ 40 * 3530486 * 2
def baseEnd_3530486 : Nat := 1812836261969379190988597

theorem tailTrace_3530486 : CollatzResearch.WordTrace tailWord_3530486 prefixEnd_3530486 1812836261969379190988597 := by
  unfold tailWord_3530486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8047962692978728490618207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85844935391773103899927541 8047962692978728490618207)
  ·
    refine ⟨12071944039468092735927311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8047962692978728490618207 12071944039468092735927311)
    ·
      refine ⟨18107916059202139103890967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12071944039468092735927311 18107916059202139103890967)
      ·
        refine ⟨27161874088803208655836451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18107916059202139103890967 27161874088803208655836451)
        ·
          refine ⟨40742811133204812983754677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27161874088803208655836451 40742811133204812983754677)
          ·
            refine ⟨3819638543737951217227001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40742811133204812983754677 3819638543737951217227001)
            ·
              refine ⟨2864728907803463412920251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3819638543737951217227001 2864728907803463412920251)
              ·
                refine ⟨4297093361705195119380377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2864728907803463412920251 4297093361705195119380377)
                ·
                  refine ⟨3222820021278896339535283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4297093361705195119380377 3222820021278896339535283)
                  ·
                    refine ⟨4834230031918344509302925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3222820021278896339535283 4834230031918344509302925)
                    ·
                      refine ⟨1812836261969379190988597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4834230031918344509302925 1812836261969379190988597)
                      ·
                        rfl

theorem cell23_3530486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_3530486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530486 prefixEnd_3530486 := by exact prefixLift 3530486
  have htrace : WordTrace (prefixWord ++ tailWord_3530486) baseStart_3530486 baseEnd_3530486 := by
    simpa [prefixWord, tailWord_3530486, baseEnd_3530486] using wordTrace_append hprefix tailTrace_3530486
  have hstable : (prefixWord ++ tailWord_3530486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530486).length < 2 ^ (prefixWord ++ tailWord_3530486).sum := by decide
  have hdescent : baseEnd_3530486 < baseStart_3530486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530532 : List Nat := [2, 3, 1, 3, 2, 2, 1, 4, 5]
def baseStart_3530532 : Nat := 118140960795 + 3530532 * 2 ^ 59
def prefixEnd_3530532 : Nat := 4983230072969 + 3 ^ 40 * 3530532 * 2
def baseEnd_3530532 : Nat := 201428875786609556779265

theorem tailTrace_3530532 : CollatzResearch.WordTrace tailWord_3530532 prefixEnd_3530532 201428875786609556779265 := by
  unfold tailWord_3530532
  simp only [CollatzResearch.WordTrace]
  refine ⟨64384540422746502853032925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85846053896995337137377233 64384540422746502853032925)
  ·
    refine ⟨24144202658529938569887347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64384540422746502853032925 24144202658529938569887347)
    ·
      refine ⟨36216303987794907854831021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24144202658529938569887347 36216303987794907854831021)
      ·
        refine ⟨13581113995423090445561633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36216303987794907854831021 13581113995423090445561633)
        ·
          refine ⟨10185835496567317834171225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13581113995423090445561633 10185835496567317834171225)
          ·
            refine ⟨7639376622425488375628419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10185835496567317834171225 7639376622425488375628419)
            ·
              refine ⟨11459064933638232563442629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7639376622425488375628419 11459064933638232563442629)
              ·
                refine ⟨2148574675057168605645493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11459064933638232563442629 2148574675057168605645493)
                ·
                  refine ⟨201428875786609556779265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2148574675057168605645493 201428875786609556779265)
                  ·
                    rfl

theorem cell23_3530532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_3530532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530532 prefixEnd_3530532 := by exact prefixLift 3530532
  have htrace : WordTrace (prefixWord ++ tailWord_3530532) baseStart_3530532 baseEnd_3530532 := by
    simpa [prefixWord, tailWord_3530532, baseEnd_3530532] using wordTrace_append hprefix tailTrace_3530532
  have hstable : (prefixWord ++ tailWord_3530532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530532).length < 2 ^ (prefixWord ++ tailWord_3530532).sum := by decide
  have hdescent : baseEnd_3530532 < baseStart_3530532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530565 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 1, 6, 2]
def baseStart_3530565 : Nat := 118140960795 + 3530565 * 2 ^ 59
def prefixEnd_3530565 : Nat := 4983230072969 + 3 ^ 40 * 3530565 * 2
def baseEnd_3530565 : Nat := 1812876826941084381900733

theorem tailTrace_3530565 : CollatzResearch.WordTrace tailWord_3530565 prefixEnd_3530565 1812876826941084381900733 := by
  unfold tailWord_3530565
  simp only [CollatzResearch.WordTrace]
  refine ⟨128770284454373452342017149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85846856302915634894678099 128770284454373452342017149)
  ·
    refine ⟨48288856670390044628256431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128770284454373452342017149 48288856670390044628256431)
    ·
      refine ⟨72433285005585066942384647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48288856670390044628256431 72433285005585066942384647)
      ·
        refine ⟨108649927508377600413576971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72433285005585066942384647 108649927508377600413576971)
        ·
          refine ⟨162974891262566400620365457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108649927508377600413576971 162974891262566400620365457)
          ·
            refine ⟨122231168446924800465274093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162974891262566400620365457 122231168446924800465274093)
            ·
              refine ⟨45836688167596800174477785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122231168446924800465274093 45836688167596800174477785)
              ·
                refine ⟨34377516125697600130858339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45836688167596800174477785 34377516125697600130858339)
                ·
                  refine ⟨51566274188546400196287509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34377516125697600130858339 51566274188546400196287509)
                  ·
                    refine ⟨2417169102588112509200977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51566274188546400196287509 2417169102588112509200977)
                    ·
                      refine ⟨1812876826941084381900733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2417169102588112509200977 1812876826941084381900733)
                      ·
                        rfl

theorem cell23_3530565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 6, 2].length) (baseStart_3530565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530565 prefixEnd_3530565 := by exact prefixLift 3530565
  have htrace : WordTrace (prefixWord ++ tailWord_3530565) baseStart_3530565 baseEnd_3530565 := by
    simpa [prefixWord, tailWord_3530565, baseEnd_3530565] using wordTrace_append hprefix tailTrace_3530565
  have hstable : (prefixWord ++ tailWord_3530565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530565).length < 2 ^ (prefixWord ++ tailWord_3530565).sum := by decide
  have hdescent : baseEnd_3530565 < baseStart_3530565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530566 : List Nat := [6, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_3530566 : Nat := 118140960795 + 3530566 * 2 ^ 59
def prefixEnd_3530566 : Nat := 4983230072969 + 3 ^ 40 * 3530566 * 2
def baseEnd_3530566 : Nat := 201430815602415430887581

theorem tailTrace_3530566 : CollatzResearch.WordTrace tailWord_3530566 prefixEnd_3530566 201430815602415430887581 := by
  unfold tailWord_3530566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4024072528980307172275111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85846880618246553008535701 4024072528980307172275111)
  ·
    refine ⟨6036108793470460758412667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4024072528980307172275111 6036108793470460758412667)
    ·
      refine ⟨9054163190205691137619001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6036108793470460758412667 9054163190205691137619001)
      ·
        refine ⟨6790622392654268353214251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9054163190205691137619001 6790622392654268353214251)
        ·
          refine ⟨10185933588981402529821377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6790622392654268353214251 10185933588981402529821377)
          ·
            refine ⟨7639450191736051897366033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10185933588981402529821377 7639450191736051897366033)
            ·
              refine ⟨5729587643802038923024525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7639450191736051897366033 5729587643802038923024525)
              ·
                refine ⟨2148595366425764596134197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5729587643802038923024525 2148595366425764596134197)
                ·
                  refine ⟨201430815602415430887581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2148595366425764596134197 201430815602415430887581)
                  ·
                    rfl

theorem cell23_3530566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_3530566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530566 prefixEnd_3530566 := by exact prefixLift 3530566
  have htrace : WordTrace (prefixWord ++ tailWord_3530566) baseStart_3530566 baseEnd_3530566 := by
    simpa [prefixWord, tailWord_3530566, baseEnd_3530566] using wordTrace_append hprefix tailTrace_3530566
  have hstable : (prefixWord ++ tailWord_3530566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530566).length < 2 ^ (prefixWord ++ tailWord_3530566).sum := by decide
  have hdescent : baseEnd_3530566 < baseStart_3530566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530585 : List Nat := [1, 2, 1, 2, 2, 3, 2, 1, 4, 2, 3]
def baseStart_3530585 : Nat := 118140960795 + 3530585 * 2 ^ 59
def prefixEnd_3530585 : Nat := 4983230072969 + 3 ^ 40 * 3530585 * 2
def baseEnd_3530585 : Nat := 1812887096554174303650641

theorem tailTrace_3530585 : CollatzResearch.WordTrace tailWord_3530585 prefixEnd_3530585 1812887096554174303650641 := by
  unfold tailWord_3530585
  simp only [CollatzResearch.WordTrace]
  refine ⟨128771013914300995757745209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85847342609533997171830139 128771013914300995757745209)
  ·
    refine ⟨96578260435725746818308907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128771013914300995757745209 96578260435725746818308907)
    ·
      refine ⟨144867390653588620227463361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96578260435725746818308907 144867390653588620227463361)
      ·
        refine ⟨108650542990191465170597521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144867390653588620227463361 108650542990191465170597521)
        ·
          refine ⟨81487907242643598877948141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108650542990191465170597521 81487907242643598877948141)
          ·
            refine ⟨30557965215991349579230553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81487907242643598877948141 30557965215991349579230553)
            ·
              refine ⟨22918473911993512184422915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30557965215991349579230553 22918473911993512184422915)
              ·
                refine ⟨34377710867990268276634373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22918473911993512184422915 34377710867990268276634373)
                ·
                  refine ⟨6445820787748175301868945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34377710867990268276634373 6445820787748175301868945)
                  ·
                    refine ⟨4834365590811131476401709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6445820787748175301868945 4834365590811131476401709)
                    ·
                      refine ⟨1812887096554174303650641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4834365590811131476401709 1812887096554174303650641)
                      ·
                        rfl

theorem cell23_3530585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_3530585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530585 prefixEnd_3530585 := by exact prefixLift 3530585
  have htrace : WordTrace (prefixWord ++ tailWord_3530585) baseStart_3530585 baseEnd_3530585 := by
    simpa [prefixWord, tailWord_3530585, baseEnd_3530585] using wordTrace_append hprefix tailTrace_3530585
  have hstable : (prefixWord ++ tailWord_3530585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530585).length < 2 ^ (prefixWord ++ tailWord_3530585).sum := by decide
  have hdescent : baseEnd_3530585 < baseStart_3530585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530592 : List Nat := [2, 1, 1, 3, 3, 3, 2, 1, 3, 4]
def baseStart_3530592 : Nat := 118140960795 + 3530592 * 2 ^ 59
def prefixEnd_3530592 : Nat := 4983230072969 + 3 ^ 40 * 3530592 * 2
def baseEnd_3530592 : Nat := 604296896972918592087703

theorem tailTrace_3530592 : CollatzResearch.WordTrace tailWord_3530592 prefixEnd_3530592 604296896972918592087703 := by
  unfold tailWord_3530592
  simp only [CollatzResearch.WordTrace]
  refine ⟨64385634612637817976625015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85847512816850423968833353 64385634612637817976625015)
  ·
    refine ⟨96578451918956726964937523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64385634612637817976625015 96578451918956726964937523)
    ·
      refine ⟨144867677878435090447406285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96578451918956726964937523 144867677878435090447406285)
      ·
        refine ⟨54325379204413158917777357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144867677878435090447406285 54325379204413158917777357)
        ·
          refine ⟨20372017201654934594166509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54325379204413158917777357 20372017201654934594166509)
          ·
            refine ⟨7639506450620600472812441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20372017201654934594166509 7639506450620600472812441)
            ·
              refine ⟨5729629837965450354609331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7639506450620600472812441 5729629837965450354609331)
              ·
                refine ⟨8594444756948175531913997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5729629837965450354609331 8594444756948175531913997)
                ·
                  refine ⟨3222916783855565824467749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8594444756948175531913997 3222916783855565824467749)
                  ·
                    refine ⟨604296896972918592087703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3222916783855565824467749 604296896972918592087703)
                    ·
                      rfl

theorem cell23_3530592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 1, 3, 4].length) (baseStart_3530592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530592 prefixEnd_3530592 := by exact prefixLift 3530592
  have htrace : WordTrace (prefixWord ++ tailWord_3530592) baseStart_3530592 baseEnd_3530592 := by
    simpa [prefixWord, tailWord_3530592, baseEnd_3530592] using wordTrace_append hprefix tailTrace_3530592
  have hstable : (prefixWord ++ tailWord_3530592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530592).length < 2 ^ (prefixWord ++ tailWord_3530592).sum := by decide
  have hdescent : baseEnd_3530592 < baseStart_3530592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530605 : List Nat := [1, 5, 1, 1, 1, 1, 2, 5, 6]
def baseStart_3530605 : Nat := 118140960795 + 3530605 * 2 ^ 59
def prefixEnd_3530605 : Nat := 4983230072969 + 3 ^ 40 * 3530605 * 2
def baseEnd_3530605 : Nat := 201433040685251580600061

theorem tailTrace_3530605 : CollatzResearch.WordTrace tailWord_3530605 prefixEnd_3530605 201433040685251580600061 := by
  unfold tailWord_3530605
  simp only [CollatzResearch.WordTrace]
  refine ⟨128771743374228539173473269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85847828916152359448982179 128771743374228539173473269)
  ·
    refine ⟨12072350941333925547513119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128771743374228539173473269 12072350941333925547513119)
    ·
      refine ⟨18108526412000888321269679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12072350941333925547513119 18108526412000888321269679)
      ·
        refine ⟨27162789618001332481904519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18108526412000888321269679 27162789618001332481904519)
        ·
          refine ⟨40744184427001998722856779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27162789618001332481904519 40744184427001998722856779)
          ·
            refine ⟨61116276640502998084285169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40744184427001998722856779 61116276640502998084285169)
            ·
              refine ⟨45837207480377248563213877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61116276640502998084285169 45837207480377248563213877)
              ·
                refine ⟨4297238201285367052801301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45837207480377248563213877 4297238201285367052801301)
                ·
                  refine ⟨201433040685251580600061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4297238201285367052801301 201433040685251580600061)
                  ·
                    rfl

theorem cell23_3530605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_3530605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530605 prefixEnd_3530605 := by exact prefixLift 3530605
  have htrace : WordTrace (prefixWord ++ tailWord_3530605) baseStart_3530605 baseEnd_3530605 := by
    simpa [prefixWord, tailWord_3530605, baseEnd_3530605] using wordTrace_append hprefix tailTrace_3530605
  have hstable : (prefixWord ++ tailWord_3530605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530605).length < 2 ^ (prefixWord ++ tailWord_3530605).sum := by decide
  have hdescent : baseEnd_3530605 < baseStart_3530605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530608 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 6]
def baseStart_3530608 : Nat := 118140960795 + 3530608 * 2 ^ 59
def prefixEnd_3530608 : Nat := 4983230072969 + 3 ^ 40 * 3530608 * 2
def baseEnd_3530608 : Nat := 1812898906609227713663035

theorem tailTrace_3530608 : CollatzResearch.WordTrace tailWord_3530608 prefixEnd_3530608 1812898906609227713663035 := by
  unfold tailWord_3530608
  simp only [CollatzResearch.WordTrace]
  refine ⟨64385926396608835342916239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85847901862145113790554985 64385926396608835342916239)
  ·
    refine ⟨96578889594913253014374359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64385926396608835342916239 96578889594913253014374359)
    ·
      refine ⟨144868334392369879521561539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96578889594913253014374359 144868334392369879521561539)
      ·
        refine ⟨217302501588554819282342309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144868334392369879521561539 217302501588554819282342309)
        ·
          refine ⟨40744219047854028615439183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217302501588554819282342309 40744219047854028615439183)
          ·
            refine ⟨61116328571781042923158775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40744219047854028615439183 61116328571781042923158775)
            ·
              refine ⟨91674492857671564384738163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61116328571781042923158775 91674492857671564384738163)
              ·
                refine ⟨137511739286507346577107245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91674492857671564384738163 137511739286507346577107245)
                ·
                  refine ⟨51566902232440254966415217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137511739286507346577107245 51566902232440254966415217)
                  ·
                    refine ⟨38675176674330191224811413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51566902232440254966415217 38675176674330191224811413)
                    ·
                      refine ⟨1812898906609227713663035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38675176674330191224811413 1812898906609227713663035)
                      ·
                        rfl

theorem cell23_3530608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_3530608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530608 prefixEnd_3530608 := by exact prefixLift 3530608
  have htrace : WordTrace (prefixWord ++ tailWord_3530608) baseStart_3530608 baseEnd_3530608 := by
    simpa [prefixWord, tailWord_3530608, baseEnd_3530608] using wordTrace_append hprefix tailTrace_3530608
  have hstable : (prefixWord ++ tailWord_3530608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530608).length < 2 ^ (prefixWord ++ tailWord_3530608).sum := by decide
  have hdescent : baseEnd_3530608 < baseStart_3530608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530622 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 8]
def baseStart_3530622 : Nat := 118140960795 + 3530622 * 2 ^ 59
def prefixEnd_3530622 : Nat := 4983230072969 + 3 ^ 40 * 3530622 * 2
def baseEnd_3530622 : Nat := 201434010593154517654219

theorem tailTrace_3530622 : CollatzResearch.WordTrace tailWord_3530622 prefixEnd_3530622 201434010593154517654219 := by
  unfold tailWord_3530622
  simp only [CollatzResearch.WordTrace]
  refine ⟨16096545426895868884605265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85848242276777967384561413 16096545426895868884605265)
  ·
    refine ⟨12072409070171901663453949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16096545426895868884605265 12072409070171901663453949)
    ·
      refine ⟨4527153401314463123795231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12072409070171901663453949 4527153401314463123795231)
      ·
        refine ⟨6790730101971694685692847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4527153401314463123795231 6790730101971694685692847)
        ·
          refine ⟨10186095152957542028539271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6790730101971694685692847 10186095152957542028539271)
          ·
            refine ⟨15279142729436313042808907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10186095152957542028539271 15279142729436313042808907)
            ·
              refine ⟨22918714094154469564213361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15279142729436313042808907 22918714094154469564213361)
              ·
                refine ⟨17189035570615852173160021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22918714094154469564213361 17189035570615852173160021)
                ·
                  refine ⟨201434010593154517654219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17189035570615852173160021 201434010593154517654219)
                  ·
                    rfl

theorem cell23_3530622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_3530622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530622 prefixEnd_3530622 := by exact prefixLift 3530622
  have htrace : WordTrace (prefixWord ++ tailWord_3530622) baseStart_3530622 baseEnd_3530622 := by
    simpa [prefixWord, tailWord_3530622, baseEnd_3530622] using wordTrace_append hprefix tailTrace_3530622
  have hstable : (prefixWord ++ tailWord_3530622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530622).length < 2 ^ (prefixWord ++ tailWord_3530622).sum := by decide
  have hdescent : baseEnd_3530622 < baseStart_3530622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530649 : List Nat := [1, 2, 1, 2, 1, 3, 2, 6, 1, 1, 3]
def baseStart_3530649 : Nat := 118140960795 + 3530649 * 2 ^ 59
def prefixEnd_3530649 : Nat := 4983230072969 + 3 ^ 40 * 3530649 * 2
def baseEnd_3530649 : Nat := 1812919959316062053250347

theorem tailTrace_3530649 : CollatzResearch.WordTrace tailWord_3530649 prefixEnd_3530649 1812919959316062053250347 := by
  unfold tailWord_3530649
  simp only [CollatzResearch.WordTrace]
  refine ⟨128773348186069134688075001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85848898790712756458716667 128773348186069134688075001)
  ·
    refine ⟨96580011139551851016056251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128773348186069134688075001 96580011139551851016056251)
    ·
      refine ⟨144870016709327776524084377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96580011139551851016056251 144870016709327776524084377)
      ·
        refine ⟨108652512531995832393063283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144870016709327776524084377 108652512531995832393063283)
        ·
          refine ⟨162978768797993748589594925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108652512531995832393063283 162978768797993748589594925)
          ·
            refine ⟨61117038299247655721098097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 162978768797993748589594925 61117038299247655721098097)
            ·
              refine ⟨45837778724435741790823573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61117038299247655721098097 45837778724435741790823573)
              ·
                refine ⟨2148645877707925396444855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45837778724435741790823573 2148645877707925396444855)
                ·
                  refine ⟨3222968816561888094667283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2148645877707925396444855 3222968816561888094667283)
                  ·
                    refine ⟨4834453224842832142000925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3222968816561888094667283 4834453224842832142000925)
                    ·
                      refine ⟨1812919959316062053250347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4834453224842832142000925 1812919959316062053250347)
                      ·
                        rfl

theorem cell23_3530649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6, 1, 1, 3].length) (baseStart_3530649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530649 prefixEnd_3530649 := by exact prefixLift 3530649
  have htrace : WordTrace (prefixWord ++ tailWord_3530649) baseStart_3530649 baseEnd_3530649 := by
    simpa [prefixWord, tailWord_3530649, baseEnd_3530649] using wordTrace_append hprefix tailTrace_3530649
  have hstable : (prefixWord ++ tailWord_3530649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530649).length < 2 ^ (prefixWord ++ tailWord_3530649).sum := by decide
  have hdescent : baseEnd_3530649 < baseStart_3530649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530665 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 6, 4]
def baseStart_3530665 : Nat := 118140960795 + 3530665 * 2 ^ 59
def prefixEnd_3530665 : Nat := 4983230072969 + 3 ^ 40 * 3530665 * 2
def baseEnd_3530665 : Nat := 604309391668844663550091

theorem tailTrace_3530665 : CollatzResearch.WordTrace tailWord_3530665 prefixEnd_3530665 604309391668844663550091 := by
  unfold tailWord_3530665
  simp only [CollatzResearch.WordTrace]
  refine ⟨128773931754011169420657449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85849287836007446280438299 128773931754011169420657449)
  ·
    refine ⟨96580448815508377065493087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128773931754011169420657449 96580448815508377065493087)
    ·
      refine ⟨144870673223262565598239631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96580448815508377065493087 144870673223262565598239631)
      ·
        refine ⟨217306009834893848397359447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144870673223262565598239631 217306009834893848397359447)
        ·
          refine ⟨325959014752340772596039171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217306009834893848397359447 325959014752340772596039171)
          ·
            refine ⟨488938522128511158894058757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325959014752340772596039171 488938522128511158894058757)
            ·
              refine ⟨91675972899095842292636017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 488938522128511158894058757 91675972899095842292636017)
              ·
                refine ⟨68756979674321881719477013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91675972899095842292636017 68756979674321881719477013)
                ·
                  refine ⟨3222983422233838205600485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68756979674321881719477013 3222983422233838205600485)
                  ·
                    refine ⟨604309391668844663550091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3222983422233838205600485 604309391668844663550091)
                    ·
                      rfl

theorem cell23_3530665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 4].length) (baseStart_3530665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530665 prefixEnd_3530665 := by exact prefixLift 3530665
  have htrace : WordTrace (prefixWord ++ tailWord_3530665) baseStart_3530665 baseEnd_3530665 := by
    simpa [prefixWord, tailWord_3530665, baseEnd_3530665] using wordTrace_append hprefix tailTrace_3530665
  have hstable : (prefixWord ++ tailWord_3530665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530665).length < 2 ^ (prefixWord ++ tailWord_3530665).sum := by decide
  have hdescent : baseEnd_3530665 < baseStart_3530665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530735 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 5]
def baseStart_3530735 : Nat := 118140960795 + 3530735 * 2 ^ 59
def prefixEnd_3530735 : Nat := 4983230072969 + 3 ^ 40 * 3530735 * 2
def baseEnd_3530735 : Nat := 1812964118652348716774951

theorem tailTrace_3530735 : CollatzResearch.WordTrace tailWord_3530735 prefixEnd_3530735 1812964118652348716774951 := by
  unfold tailWord_3530735
  simp only [CollatzResearch.WordTrace]
  refine ⟨128776484863757571375705659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85850989909171714250470439 128776484863757571375705659)
  ·
    refine ⟨193164727295636357063558489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128776484863757571375705659 193164727295636357063558489)
    ·
      refine ⟨144873545471727267797668867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193164727295636357063558489 144873545471727267797668867)
      ·
        refine ⟨217310318207590901696503301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144873545471727267797668867 217310318207590901696503301)
        ·
          refine ⟨40745684663923294068094369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217310318207590901696503301 40745684663923294068094369)
          ·
            refine ⟨30559263497942470551070777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40745684663923294068094369 30559263497942470551070777)
            ·
              refine ⟨22919447623456852913303083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30559263497942470551070777 22919447623456852913303083)
              ·
                refine ⟨34379171435185279369954625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22919447623456852913303083 34379171435185279369954625)
                ·
                  refine ⟨25784378576388959527465969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34379171435185279369954625 25784378576388959527465969)
                  ·
                    refine ⟨19338283932291719645599477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25784378576388959527465969 19338283932291719645599477)
                    ·
                      refine ⟨1812964118652348716774951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19338283932291719645599477 1812964118652348716774951)
                      ·
                        rfl

theorem cell23_3530735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_3530735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530735 prefixEnd_3530735 := by exact prefixLift 3530735
  have htrace : WordTrace (prefixWord ++ tailWord_3530735) baseStart_3530735 baseEnd_3530735 := by
    simpa [prefixWord, tailWord_3530735, baseEnd_3530735] using wordTrace_append hprefix tailTrace_3530735
  have hstable : (prefixWord ++ tailWord_3530735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530735).length < 2 ^ (prefixWord ++ tailWord_3530735).sum := by decide
  have hdescent : baseEnd_3530735 < baseStart_3530735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530773 : List Nat := [1, 3, 2, 1, 5, 1, 3, 1, 2, 1, 3]
def baseStart_3530773 : Nat := 118140960795 + 3530773 * 2 ^ 59
def prefixEnd_3530773 : Nat := 4983230072969 + 3 ^ 40 * 3530773 * 2
def baseEnd_3530773 : Nat := 1812983630917219568099777

theorem tailTrace_3530773 : CollatzResearch.WordTrace tailWord_3530773 prefixEnd_3530773 1812983630917219568099777 := by
  unfold tailWord_3530773
  simp only [CollatzResearch.WordTrace]
  refine ⟨128777870837619903865588973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85851913891746602577059315 128777870837619903865588973)
  ·
    refine ⟨48291701564107463949595865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128777870837619903865588973 48291701564107463949595865)
    ·
      refine ⟨36218776173080597962196899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48291701564107463949595865 36218776173080597962196899)
      ·
        refine ⟨54328164259620896943295349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36218776173080597962196899 54328164259620896943295349)
        ·
          refine ⟨5093265399339459088433939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54328164259620896943295349 5093265399339459088433939)
          ·
            refine ⟨7639898099009188632650909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5093265399339459088433939 7639898099009188632650909)
            ·
              refine ⟨2864961787128445737244091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7639898099009188632650909 2864961787128445737244091)
              ·
                refine ⟨4297442680692668605866137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2864961787128445737244091 4297442680692668605866137)
                ·
                  refine ⟨3223082010519501454399603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4297442680692668605866137 3223082010519501454399603)
                  ·
                    refine ⟨4834623015779252181599405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3223082010519501454399603 4834623015779252181599405)
                    ·
                      refine ⟨1812983630917219568099777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4834623015779252181599405 1812983630917219568099777)
                      ·
                        rfl

theorem cell23_3530773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_3530773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530773 prefixEnd_3530773 := by exact prefixLift 3530773
  have htrace : WordTrace (prefixWord ++ tailWord_3530773) baseStart_3530773 baseEnd_3530773 := by
    simpa [prefixWord, tailWord_3530773, baseEnd_3530773] using wordTrace_append hprefix tailTrace_3530773
  have hstable : (prefixWord ++ tailWord_3530773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530773).length < 2 ^ (prefixWord ++ tailWord_3530773).sum := by decide
  have hdescent : baseEnd_3530773 < baseStart_3530773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530829 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_3530829 : Nat := 118140960795 + 3530829 * 2 ^ 59
def prefixEnd_3530829 : Nat := 4983230072969 + 3 ^ 40 * 3530829 * 2
def baseEnd_3530829 : Nat := 1813012385833871348999519

theorem tailTrace_3530829 : CollatzResearch.WordTrace tailWord_3530829 prefixEnd_3530829 1813012385833871348999519 := by
  unfold tailWord_3530829
  simp only [CollatzResearch.WordTrace]
  refine ⟨128779913325417025429627541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85853275550278016953085027 128779913325417025429627541)
  ·
    refine ⟨6036558437128923067013791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128779913325417025429627541 6036558437128923067013791)
    ·
      refine ⟨9054837655693384600520687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6036558437128923067013791 9054837655693384600520687)
      ·
        refine ⟨13582256483540076900781031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9054837655693384600520687 13582256483540076900781031)
        ·
          refine ⟨20373384725310115351171547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13582256483540076900781031 20373384725310115351171547)
          ·
            refine ⟨30560077087965173026757321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20373384725310115351171547 30560077087965173026757321)
            ·
              refine ⟨22920057815973879770067991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30560077087965173026757321 22920057815973879770067991)
              ·
                refine ⟨34380086723960819655101987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22920057815973879770067991 34380086723960819655101987)
                ·
                  refine ⟨51570130085941229482652981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34380086723960819655101987 51570130085941229482652981)
                  ·
                    refine ⟨4834699695556990263998717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51570130085941229482652981 4834699695556990263998717)
                    ·
                      refine ⟨1813012385833871348999519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4834699695556990263998717 1813012385833871348999519)
                      ·
                        rfl

theorem cell23_3530829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_3530829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530829 prefixEnd_3530829 := by exact prefixLift 3530829
  have htrace : WordTrace (prefixWord ++ tailWord_3530829) baseStart_3530829 baseEnd_3530829 := by
    simpa [prefixWord, tailWord_3530829, baseEnd_3530829] using wordTrace_append hprefix tailTrace_3530829
  have hstable : (prefixWord ++ tailWord_3530829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530829).length < 2 ^ (prefixWord ++ tailWord_3530829).sum := by decide
  have hdescent : baseEnd_3530829 < baseStart_3530829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530830 : List Nat := [4, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2]
def baseStart_3530830 : Nat := 118140960795 + 3530830 * 2 ^ 59
def prefixEnd_3530830 : Nat := 4983230072969 + 3 ^ 40 * 3530830 * 2
def baseEnd_3530830 : Nat := 1813012899314525845087015

theorem tailTrace_3530830 : CollatzResearch.WordTrace tailWord_3530830 prefixEnd_3530830 1813012899314525845087015 := by
  unfold tailWord_3530830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16097493724801675325051743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85853299865608935066942629 16097493724801675325051743)
  ·
    refine ⟨24146240587202512987577615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16097493724801675325051743 24146240587202512987577615)
    ·
      refine ⟨36219360880803769481366423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24146240587202512987577615 36219360880803769481366423)
      ·
        refine ⟨54329041321205654222049635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36219360880803769481366423 54329041321205654222049635)
        ·
          refine ⟨81493561981808481333074453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54329041321205654222049635 81493561981808481333074453)
          ·
            refine ⟨3820010717897272562487865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81493561981808481333074453 3820010717897272562487865)
            ·
              refine ⟨2865008038422954421865899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3820010717897272562487865 2865008038422954421865899)
              ·
                refine ⟨4297512057634431632798849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2865008038422954421865899 4297512057634431632798849)
                ·
                  refine ⟨3223134043225823724599137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4297512057634431632798849 3223134043225823724599137)
                  ·
                    refine ⟨2417350532419367793449353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3223134043225823724599137 2417350532419367793449353)
                    ·
                      refine ⟨1813012899314525845087015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2417350532419367793449353 1813012899314525845087015)
                      ·
                        rfl

theorem cell23_3530830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 1, 2, 2, 2].length) (baseStart_3530830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530830 prefixEnd_3530830 := by exact prefixLift 3530830
  have htrace : WordTrace (prefixWord ++ tailWord_3530830) baseStart_3530830 baseEnd_3530830 := by
    simpa [prefixWord, tailWord_3530830, baseEnd_3530830] using wordTrace_append hprefix tailTrace_3530830
  have hstable : (prefixWord ++ tailWord_3530830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530830).length < 2 ^ (prefixWord ++ tailWord_3530830).sum := by decide
  have hdescent : baseEnd_3530830 < baseStart_3530830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530852 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_3530852 : Nat := 118140960795 + 3530852 * 2 ^ 59
def prefixEnd_3530852 : Nat := 4983230072969 + 3 ^ 40 * 3530852 * 2
def baseEnd_3530852 : Nat := 1813024195888924759011913

theorem tailTrace_3530852 : CollatzResearch.WordTrace tailWord_3530852 prefixEnd_3530852 1813024195888924759011913 := by
  unfold tailWord_3530852
  simp only [CollatzResearch.WordTrace]
  refine ⟨64390376102166850178857405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85853834802889133571809873 64390376102166850178857405)
  ·
    refine ⟨24146391038312568817071527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64390376102166850178857405 24146391038312568817071527)
    ·
      refine ⟨36219586557468853225607291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24146391038312568817071527 36219586557468853225607291)
      ·
        refine ⟨54329379836203279838410937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36219586557468853225607291 54329379836203279838410937)
        ·
          refine ⟨40747034877152459878808203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54329379836203279838410937 40747034877152459878808203)
          ·
            refine ⟨61120552315728689818212305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40747034877152459878808203 61120552315728689818212305)
            ·
              refine ⟨45840414236796517363659229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61120552315728689818212305 45840414236796517363659229)
              ·
                refine ⟨17190155338798694011372211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45840414236796517363659229 17190155338798694011372211)
                ·
                  refine ⟨25785233008198041017058317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17190155338798694011372211 25785233008198041017058317)
                  ·
                    refine ⟨9669462378074265381396869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25785233008198041017058317 9669462378074265381396869)
                    ·
                      refine ⟨1813024195888924759011913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9669462378074265381396869 1813024195888924759011913)
                      ·
                        rfl

theorem cell23_3530852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_3530852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530852 prefixEnd_3530852 := by exact prefixLift 3530852
  have htrace : WordTrace (prefixWord ++ tailWord_3530852) baseStart_3530852 baseEnd_3530852 := by
    simpa [prefixWord, tailWord_3530852, baseEnd_3530852] using wordTrace_append hprefix tailTrace_3530852
  have hstable : (prefixWord ++ tailWord_3530852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530852).length < 2 ^ (prefixWord ++ tailWord_3530852).sum := by decide
  have hdescent : baseEnd_3530852 < baseStart_3530852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530872 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 3, 4, 3]
def baseStart_3530872 : Nat := 118140960795 + 3530872 * 2 ^ 59
def prefixEnd_3530872 : Nat := 4983230072969 + 3 ^ 40 * 3530872 * 2
def baseEnd_3530872 : Nat := 1813034465502014680761821

theorem tailTrace_3530872 : CollatzResearch.WordTrace tailWord_3530872 prefixEnd_3530872 1813034465502014680761821 := by
  unfold tailWord_3530872
  simp only [CollatzResearch.WordTrace]
  refine ⟨64390740832130621886721435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85854321109507495848961913 64390740832130621886721435)
  ·
    refine ⟨96586111248195932830082153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64390740832130621886721435 96586111248195932830082153)
    ·
      refine ⟨72439583436146949622561615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96586111248195932830082153 72439583436146949622561615)
      ·
        refine ⟨108659375154220424433842423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72439583436146949622561615 108659375154220424433842423)
        ·
          refine ⟨162989062731330636650763635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108659375154220424433842423 162989062731330636650763635)
          ·
            refine ⟨244483594096995954976145453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162989062731330636650763635 244483594096995954976145453)
            ·
              refine ⟨91681347786373483116054545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 244483594096995954976145453 91681347786373483116054545)
              ·
                refine ⟨68761010839780112337040909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91681347786373483116054545 68761010839780112337040909)
                ·
                  refine ⟨25785379064917542126390341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68761010839780112337040909 25785379064917542126390341)
                  ·
                    refine ⟨4834758574672039148698189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25785379064917542126390341 4834758574672039148698189)
                    ·
                      refine ⟨1813034465502014680761821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4834758574672039148698189 1813034465502014680761821)
                      ·
                        rfl

theorem cell23_3530872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_3530872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530872 prefixEnd_3530872 := by exact prefixLift 3530872
  have htrace : WordTrace (prefixWord ++ tailWord_3530872) baseStart_3530872 baseEnd_3530872 := by
    simpa [prefixWord, tailWord_3530872, baseEnd_3530872] using wordTrace_append hprefix tailTrace_3530872
  have hstable : (prefixWord ++ tailWord_3530872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530872).length < 2 ^ (prefixWord ++ tailWord_3530872).sum := by decide
  have hdescent : baseEnd_3530872 < baseStart_3530872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530900 : List Nat := [2, 4, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_3530900 : Nat := 118140960795 + 3530900 * 2 ^ 59
def prefixEnd_3530900 : Nat := 4983230072969 + 3 ^ 40 * 3530900 * 2
def baseEnd_3530900 : Nat := 604349614320113523737231

theorem tailTrace_3530900 : CollatzResearch.WordTrace tailWord_3530900 prefixEnd_3530900 604349614320113523737231 := by
  unfold tailWord_3530900
  simp only [CollatzResearch.WordTrace]
  refine ⟨64391251454079902277731077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85855001938773203036974769 64391251454079902277731077)
  ·
    refine ⟨12073359647639981677074577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 64391251454079902277731077 12073359647639981677074577)
    ·
      refine ⟨9055019735729986257805933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12073359647639981677074577 9055019735729986257805933)
      ·
        refine ⟨3395632400898744846677225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9055019735729986257805933 3395632400898744846677225)
        ·
          refine ⟨2546724300674058635007919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3395632400898744846677225 2546724300674058635007919)
          ·
            refine ⟨3820086451011087952511879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2546724300674058635007919 3820086451011087952511879)
            ·
              refine ⟨5730129676516631928767819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3820086451011087952511879 5730129676516631928767819)
              ·
                refine ⟨8595194514774947893151729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5730129676516631928767819 8595194514774947893151729)
                ·
                  refine ⟨6446395886081210919863797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8595194514774947893151729 6446395886081210919863797)
                  ·
                    refine ⟨604349614320113523737231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6446395886081210919863797 604349614320113523737231)
                    ·
                      rfl

theorem cell23_3530900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_3530900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530900 prefixEnd_3530900 := by exact prefixLift 3530900
  have htrace : WordTrace (prefixWord ++ tailWord_3530900) baseStart_3530900 baseEnd_3530900 := by
    simpa [prefixWord, tailWord_3530900, baseEnd_3530900] using wordTrace_append hprefix tailTrace_3530900
  have hstable : (prefixWord ++ tailWord_3530900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530900).length < 2 ^ (prefixWord ++ tailWord_3530900).sum := by decide
  have hdescent : baseEnd_3530900 < baseStart_3530900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530903 : List Nat := [1, 1, 3, 3, 5, 1, 1, 1, 2, 1, 4]
def baseStart_3530903 : Nat := 118140960795 + 3530903 * 2 ^ 59
def prefixEnd_3530903 : Nat := 4983230072969 + 3 ^ 40 * 3530903 * 2
def baseEnd_3530903 : Nat := 1813050383402304059474179

theorem tailTrace_3530903 : CollatzResearch.WordTrace tailWord_3530903 prefixEnd_3530903 1813050383402304059474179 := by
  unfold tailWord_3530903
  simp only [CollatzResearch.WordTrace]
  refine ⟨128782612327148936067821363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85855074884765957378547575 128782612327148936067821363)
  ·
    refine ⟨193173918490723404101732045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128782612327148936067821363 193173918490723404101732045)
    ·
      refine ⟨72440219434021276538149517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193173918490723404101732045 72440219434021276538149517)
      ·
        refine ⟨27165082287757978701806069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72440219434021276538149517 27165082287757978701806069)
        ·
          refine ⟨2546726464477310503294319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27165082287757978701806069 2546726464477310503294319)
          ·
            refine ⟨3820089696715965754941479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2546726464477310503294319 3820089696715965754941479)
            ·
              refine ⟨5730134545073948632412219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3820089696715965754941479 5730134545073948632412219)
              ·
                refine ⟨8595201817610922948618329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5730134545073948632412219 8595201817610922948618329)
                ·
                  refine ⟨6446401363208192211463747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8595201817610922948618329 6446401363208192211463747)
                  ·
                    refine ⟨9669602044812288317195621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6446401363208192211463747 9669602044812288317195621)
                    ·
                      refine ⟨1813050383402304059474179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9669602044812288317195621 1813050383402304059474179)
                      ·
                        rfl

theorem cell23_3530903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_3530903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530903 prefixEnd_3530903 := by exact prefixLift 3530903
  have htrace : WordTrace (prefixWord ++ tailWord_3530903) baseStart_3530903 baseEnd_3530903 := by
    simpa [prefixWord, tailWord_3530903, baseEnd_3530903] using wordTrace_append hprefix tailTrace_3530903
  have hstable : (prefixWord ++ tailWord_3530903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530903).length < 2 ^ (prefixWord ++ tailWord_3530903).sum := by decide
  have hdescent : baseEnd_3530903 < baseStart_3530903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530906 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3]
def baseStart_3530906 : Nat := 118140960795 + 3530906 * 2 ^ 59
def prefixEnd_3530906 : Nat := 4983230072969 + 3 ^ 40 * 3530906 * 2
def baseEnd_3530906 : Nat := 1813051923844267547736665

theorem tailTrace_3530906 : CollatzResearch.WordTrace tailWord_3530906 prefixEnd_3530906 1813051923844267547736665 := by
  unfold tailWord_3530906
  simp only [CollatzResearch.WordTrace]
  refine ⟨32195680436534516895045143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85855147830758711720120381 32195680436534516895045143)
  ·
    refine ⟨48293520654801775342567715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32195680436534516895045143 48293520654801775342567715)
    ·
      refine ⟨72440280982202663013851573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48293520654801775342567715 72440280982202663013851573)
      ·
        refine ⟨6791276342081499657548585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72440280982202663013851573 6791276342081499657548585)
        ·
          refine ⟨5093457256561124743161439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6791276342081499657548585 5093457256561124743161439)
          ·
            refine ⟨7640185884841687114742159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5093457256561124743161439 7640185884841687114742159)
            ·
              refine ⟨11460278827262530672113239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7640185884841687114742159 11460278827262530672113239)
              ·
                refine ⟨17190418240893796008169859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11460278827262530672113239 17190418240893796008169859)
                ·
                  refine ⟨25785627361340694012254789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17190418240893796008169859 25785627361340694012254789)
                  ·
                    refine ⟨4834805130251380127297773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25785627361340694012254789 4834805130251380127297773)
                    ·
                      refine ⟨1813051923844267547736665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4834805130251380127297773 1813051923844267547736665)
                      ·
                        rfl

theorem cell23_3530906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_3530906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530906 prefixEnd_3530906 := by exact prefixLift 3530906
  have htrace : WordTrace (prefixWord ++ tailWord_3530906) baseStart_3530906 baseEnd_3530906 := by
    simpa [prefixWord, tailWord_3530906, baseEnd_3530906] using wordTrace_append hprefix tailTrace_3530906
  have hstable : (prefixWord ++ tailWord_3530906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530906).length < 2 ^ (prefixWord ++ tailWord_3530906).sum := by decide
  have hdescent : baseEnd_3530906 < baseStart_3530906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530913 : List Nat := [1, 2, 3, 3, 1, 3, 2, 3, 1, 4]
def baseStart_3530913 : Nat := 118140960795 + 3530913 * 2 ^ 59
def prefixEnd_3530913 : Nat := 4983230072969 + 3 ^ 40 * 3530913 * 2
def baseEnd_3530913 : Nat := 604351839402949673449711

theorem tailTrace_3530913 : CollatzResearch.WordTrace tailWord_3530913 prefixEnd_3530913 604351839402949673449711 := by
  unfold tailWord_3530913
  simp only [CollatzResearch.WordTrace]
  refine ⟨128782977057112707775685393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85855318038075138517123595 128782977057112707775685393)
  ·
    refine ⟨96587232792834530831764045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128782977057112707775685393 96587232792834530831764045)
    ·
      refine ⟨36220212297312949061911517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96587232792834530831764045 36220212297312949061911517)
      ·
        refine ⟨13582579611492355898216819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36220212297312949061911517 13582579611492355898216819)
        ·
          refine ⟨20373869417238533847325229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13582579611492355898216819 20373869417238533847325229)
          ·
            refine ⟨7640201031464450192746961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20373869417238533847325229 7640201031464450192746961)
            ·
              refine ⟨5730150773598337644560221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7640201031464450192746961 5730150773598337644560221)
              ·
                refine ⟨2148806540099376616710083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5730150773598337644560221 2148806540099376616710083)
                ·
                  refine ⟨3223209810149064925065125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2148806540099376616710083 3223209810149064925065125)
                  ·
                    refine ⟨604351839402949673449711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3223209810149064925065125 604351839402949673449711)
                    ·
                      rfl

theorem cell23_3530913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_3530913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530913 prefixEnd_3530913 := by exact prefixLift 3530913
  have htrace : WordTrace (prefixWord ++ tailWord_3530913) baseStart_3530913 baseEnd_3530913 := by
    simpa [prefixWord, tailWord_3530913, baseEnd_3530913] using wordTrace_append hprefix tailTrace_3530913
  have hstable : (prefixWord ++ tailWord_3530913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530913).length < 2 ^ (prefixWord ++ tailWord_3530913).sum := by decide
  have hdescent : baseEnd_3530913 < baseStart_3530913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530936 : List Nat := [2, 1, 2, 1, 2, 1, 6, 1, 3, 1, 3]
def baseStart_3530936 : Nat := 118140960795 + 3530936 * 2 ^ 59
def prefixEnd_3530936 : Nat := 4983230072969 + 3 ^ 40 * 3530936 * 2
def baseEnd_3530936 : Nat := 1813067328263902430361527

theorem tailTrace_3530936 : CollatzResearch.WordTrace tailWord_3530936 prefixEnd_3530936 1813067328263902430361527 := by
  unfold tailWord_3530936
  simp only [CollatzResearch.WordTrace]
  refine ⟨64391907968014691351886331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85855877290686255135848441 64391907968014691351886331)
  ·
    refine ⟨96587861952022037027829497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64391907968014691351886331 96587861952022037027829497)
    ·
      refine ⟨72440896464016527770872123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96587861952022037027829497 72440896464016527770872123)
      ·
        refine ⟨108661344696024791656308185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72440896464016527770872123 108661344696024791656308185)
        ·
          refine ⟨81496008522018593742231139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108661344696024791656308185 81496008522018593742231139)
          ·
            refine ⟨122244012783027890613346709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81496008522018593742231139 122244012783027890613346709)
            ·
              refine ⟨5730188099204432372500627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 122244012783027890613346709 5730188099204432372500627)
              ·
                refine ⟨8595282148806648558750941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5730188099204432372500627 8595282148806648558750941)
                ·
                  refine ⟨3223230805802493209531603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8595282148806648558750941 3223230805802493209531603)
                  ·
                    refine ⟨4834846208703739814297405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3223230805802493209531603 4834846208703739814297405)
                    ·
                      refine ⟨1813067328263902430361527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4834846208703739814297405 1813067328263902430361527)
                      ·
                        rfl

theorem cell23_3530936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 3, 1, 3].length) (baseStart_3530936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530936 prefixEnd_3530936 := by exact prefixLift 3530936
  have htrace : WordTrace (prefixWord ++ tailWord_3530936) baseStart_3530936 baseEnd_3530936 := by
    simpa [prefixWord, tailWord_3530936, baseEnd_3530936] using wordTrace_append hprefix tailTrace_3530936
  have hstable : (prefixWord ++ tailWord_3530936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530936).length < 2 ^ (prefixWord ++ tailWord_3530936).sum := by decide
  have hdescent : baseEnd_3530936 < baseStart_3530936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530959 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 2, 6, 2]
def baseStart_3530959 : Nat := 118140960795 + 3530959 * 2 ^ 59
def prefixEnd_3530959 : Nat := 4983230072969 + 3 ^ 40 * 3530959 * 2
def baseEnd_3530959 : Nat := 1813079138318955840373921

theorem tailTrace_3530959 : CollatzResearch.WordTrace tailWord_3530959 prefixEnd_3530959 1813079138318955840373921 := by
  unfold tailWord_3530959
  simp only [CollatzResearch.WordTrace]
  refine ⟨128784654814946057631859931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85856436543297371754573287 128784654814946057631859931)
  ·
    refine ⟨193176982222419086447789897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128784654814946057631859931 193176982222419086447789897)
    ·
      refine ⟨144882736666814314835842423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193176982222419086447789897 144882736666814314835842423)
      ·
        refine ⟨217324105000221472253763635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144882736666814314835842423 217324105000221472253763635)
        ·
          refine ⟨325986157500332208380645453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217324105000221472253763635 325986157500332208380645453)
          ·
            refine ⟨122244809062624578142742045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325986157500332208380645453 122244809062624578142742045)
            ·
              refine ⟨45841803398484216803528267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122244809062624578142742045 45841803398484216803528267)
              ·
                refine ⟨68762705097726325205292401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45841803398484216803528267 68762705097726325205292401)
                ·
                  refine ⟨51572028823294743903969301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68762705097726325205292401 51572028823294743903969301)
                  ·
                    refine ⟨2417438851091941120498561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51572028823294743903969301 2417438851091941120498561)
                    ·
                      refine ⟨1813079138318955840373921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2417438851091941120498561 1813079138318955840373921)
                      ·
                        rfl

theorem cell23_3530959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 6, 2].length) (baseStart_3530959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530959 prefixEnd_3530959 := by exact prefixLift 3530959
  have htrace : WordTrace (prefixWord ++ tailWord_3530959) baseStart_3530959 baseEnd_3530959 := by
    simpa [prefixWord, tailWord_3530959, baseEnd_3530959] using wordTrace_append hprefix tailTrace_3530959
  have hstable : (prefixWord ++ tailWord_3530959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530959).length < 2 ^ (prefixWord ++ tailWord_3530959).sum := by decide
  have hdescent : baseEnd_3530959 < baseStart_3530959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530969 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 4, 4]
def baseStart_3530969 : Nat := 118140960795 + 3530969 * 2 ^ 59
def prefixEnd_3530969 : Nat := 4983230072969 + 3 ^ 40 * 3530969 * 2
def baseEnd_3530969 : Nat := 604361424375166933749625

theorem tailTrace_3530969 : CollatzResearch.WordTrace tailWord_3530969 prefixEnd_3530969 604361424375166933749625 := by
  unfold tailWord_3530969
  simp only [CollatzResearch.WordTrace]
  refine ⟨128785019544909829339723961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85856679696606552893149307 128785019544909829339723961)
  ·
    refine ⟨96588764658682372004792971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128785019544909829339723961 96588764658682372004792971)
    ·
      refine ⟨144883146988023558007189457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96588764658682372004792971 144883146988023558007189457)
      ·
        refine ⟨108662360241017668505392093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144883146988023558007189457 108662360241017668505392093)
        ·
          refine ⟨40748385090381625689522035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108662360241017668505392093 40748385090381625689522035)
          ·
            refine ⟨61122577635572438534283053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40748385090381625689522035 61122577635572438534283053)
            ·
              refine ⟨22920966613339664450356145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61122577635572438534283053 22920966613339664450356145)
              ·
                refine ⟨17190724960004748337767109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22920966613339664450356145 17190724960004748337767109)
                ·
                  refine ⟨3223260930000890313331333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17190724960004748337767109 3223260930000890313331333)
                  ·
                    refine ⟨604361424375166933749625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3223260930000890313331333 604361424375166933749625)
                    ·
                      rfl

theorem cell23_3530969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 4].length) (baseStart_3530969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530969 prefixEnd_3530969 := by exact prefixLift 3530969
  have htrace : WordTrace (prefixWord ++ tailWord_3530969) baseStart_3530969 baseEnd_3530969 := by
    simpa [prefixWord, tailWord_3530969, baseEnd_3530969] using wordTrace_append hprefix tailTrace_3530969
  have hstable : (prefixWord ++ tailWord_3530969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530969).length < 2 ^ (prefixWord ++ tailWord_3530969).sum := by decide
  have hdescent : baseEnd_3530969 < baseStart_3530969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530986 : List Nat := [3, 1, 3, 1, 1, 2, 2, 4, 2, 4]
def baseStart_3530986 : Nat := 118140960795 + 3530986 * 2 ^ 59
def prefixEnd_3530986 : Nat := 4983230072969 + 3 ^ 40 * 3530986 * 2
def baseEnd_3530986 : Nat := 604364334098875744912099

theorem tailTrace_3530986 : CollatzResearch.WordTrace tailWord_3530986 prefixEnd_3530986 604364334098875744912099 := by
  unfold tailWord_3530986
  simp only [CollatzResearch.WordTrace]
  refine ⟨32196409896462060310773203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85857093057232160828728541 32196409896462060310773203)
  ·
    refine ⟨48294614844693090466159805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32196409896462060310773203 48294614844693090466159805)
    ·
      refine ⟨18110480566759908924809927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48294614844693090466159805 18110480566759908924809927)
      ·
        refine ⟨27165720850139863387214891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18110480566759908924809927 27165720850139863387214891)
        ·
          refine ⟨40748581275209795080822337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27165720850139863387214891 40748581275209795080822337)
          ·
            refine ⟨30561435956407346310616753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40748581275209795080822337 30561435956407346310616753)
            ·
              refine ⟨22921076967305509732962565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30561435956407346310616753 22921076967305509732962565)
              ·
                refine ⟨4297701931369783074930481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22921076967305509732962565 4297701931369783074930481)
                ·
                  refine ⟨3223276448527337306197861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4297701931369783074930481 3223276448527337306197861)
                  ·
                    refine ⟨604364334098875744912099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3223276448527337306197861 604364334098875744912099)
                    ·
                      rfl

theorem cell23_3530986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_3530986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530986 prefixEnd_3530986 := by exact prefixLift 3530986
  have htrace : WordTrace (prefixWord ++ tailWord_3530986) baseStart_3530986 baseEnd_3530986 := by
    simpa [prefixWord, tailWord_3530986, baseEnd_3530986] using wordTrace_append hprefix tailTrace_3530986
  have hstable : (prefixWord ++ tailWord_3530986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530986).length < 2 ^ (prefixWord ++ tailWord_3530986).sum := by decide
  have hdescent : baseEnd_3530986 < baseStart_3530986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3530993 : List Nat := [1, 2, 2, 2, 2, 1, 5, 1, 3, 2, 2]
def baseStart_3530993 : Nat := 118140960795 + 3530993 * 2 ^ 59
def prefixEnd_3530993 : Nat := 4983230072969 + 3 ^ 40 * 3530993 * 2
def baseEnd_3530993 : Nat := 1813096596661208707348765

theorem tailTrace_3530993 : CollatzResearch.WordTrace tailWord_3530993 prefixEnd_3530993 1813096596661208707348765 := by
  unfold tailWord_3530993
  simp only [CollatzResearch.WordTrace]
  refine ⟨128785894896822881438597633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85857263264548587625731755 128785894896822881438597633)
  ·
    refine ⟨96589421172617161078948225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128785894896822881438597633 96589421172617161078948225)
    ·
      refine ⟨72442065879462870809211169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96589421172617161078948225 72442065879462870809211169)
      ·
        refine ⟨54331549409597153106908377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72442065879462870809211169 54331549409597153106908377)
        ·
          refine ⟨40748662057197864830181283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54331549409597153106908377 40748662057197864830181283)
          ·
            refine ⟨61122993085796797245271925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40748662057197864830181283 61122993085796797245271925)
            ·
              refine ⟨5730280601793449741744243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61122993085796797245271925 5730280601793449741744243)
              ·
                refine ⟨8595420902690174612616365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5730280601793449741744243 8595420902690174612616365)
                ·
                  refine ⟨3223282838508815479731137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8595420902690174612616365 3223282838508815479731137)
                  ·
                    refine ⟨2417462128881611609798353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3223282838508815479731137 2417462128881611609798353)
                    ·
                      refine ⟨1813096596661208707348765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2417462128881611609798353 1813096596661208707348765)
                      ·
                        rfl

theorem cell23_3530993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_3530993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3530993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3530993 prefixEnd_3530993 := by exact prefixLift 3530993
  have htrace : WordTrace (prefixWord ++ tailWord_3530993) baseStart_3530993 baseEnd_3530993 := by
    simpa [prefixWord, tailWord_3530993, baseEnd_3530993] using wordTrace_append hprefix tailTrace_3530993
  have hstable : (prefixWord ++ tailWord_3530993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3530993).length < 2 ^ (prefixWord ++ tailWord_3530993).sum := by decide
  have hdescent : baseEnd_3530993 < baseStart_3530993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3530993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531006 : List Nat := [4, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4]
def baseStart_3531006 : Nat := 118140960795 + 3531006 * 2 ^ 59
def prefixEnd_3531006 : Nat := 4983230072969 + 3 ^ 40 * 3531006 * 2
def baseEnd_3531006 : Nat := 1813103271909717156486205

theorem tailTrace_3531006 : CollatzResearch.WordTrace tailWord_3531006 prefixEnd_3531006 1813103271909717156486205 := by
  unfold tailWord_3531006
  simp only [CollatzResearch.WordTrace]
  refine ⟨16098296130721973082352609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85857579363850523105880581 16098296130721973082352609)
  ·
    refine ⟨12073722098041479811764457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16098296130721973082352609 12073722098041479811764457)
    ·
      refine ⟨9055291573531109858823343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12073722098041479811764457 9055291573531109858823343)
      ·
        refine ⟨13582937360296664788235015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9055291573531109858823343 13582937360296664788235015)
        ·
          refine ⟨20374406040444997182352523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13582937360296664788235015 20374406040444997182352523)
          ·
            refine ⟨30561609060667495773528785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20374406040444997182352523 30561609060667495773528785)
            ·
              refine ⟨22921206795500621830146589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30561609060667495773528785 22921206795500621830146589)
              ·
                refine ⟨8595452548312733186304971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22921206795500621830146589 8595452548312733186304971)
                ·
                  refine ⟨12893178822469099779457457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8595452548312733186304971 12893178822469099779457457)
                  ·
                    refine ⟨9669884116851824834593093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12893178822469099779457457 9669884116851824834593093)
                    ·
                      refine ⟨1813103271909717156486205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9669884116851824834593093 1813103271909717156486205)
                      ·
                        rfl

theorem cell23_3531006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_3531006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531006 prefixEnd_3531006 := by exact prefixLift 3531006
  have htrace : WordTrace (prefixWord ++ tailWord_3531006) baseStart_3531006 baseEnd_3531006 := by
    simpa [prefixWord, tailWord_3531006, baseEnd_3531006] using wordTrace_append hprefix tailTrace_3531006
  have hstable : (prefixWord ++ tailWord_3531006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531006).length < 2 ^ (prefixWord ++ tailWord_3531006).sum := by decide
  have hdescent : baseEnd_3531006 < baseStart_3531006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531010 : List Nat := [3, 4, 1, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_3531010 : Nat := 118140960795 + 3531010 * 2 ^ 59
def prefixEnd_3531010 : Nat := 4983230072969 + 3 ^ 40 * 3531010 * 2
def baseEnd_3531010 : Nat := 1813105325832335140836187

theorem tailTrace_3531010 : CollatzResearch.WordTrace tailWord_3531010 prefixEnd_3531010 1813105325832335140836187 := by
  unfold tailWord_3531010
  simp only [CollatzResearch.WordTrace]
  refine ⟨32196628734440323335491621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85857676625174195561310989 32196628734440323335491621)
  ·
    refine ⟨6036867887707560625404679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32196628734440323335491621 6036867887707560625404679)
    ·
      refine ⟨9055301831561340938107019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6036867887707560625404679 9055301831561340938107019)
      ·
        refine ⟨13582952747342011407160529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9055301831561340938107019 13582952747342011407160529)
        ·
          refine ⟨10187214560506508555370397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13582952747342011407160529 10187214560506508555370397)
          ·
            refine ⟨3820205460189940708263899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10187214560506508555370397 3820205460189940708263899)
            ·
              refine ⟨5730308190284911062395849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3820205460189940708263899 5730308190284911062395849)
              ·
                refine ⟨4297731142713683296796887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5730308190284911062395849 4297731142713683296796887)
                ·
                  refine ⟨6446596714070524945195331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4297731142713683296796887 6446596714070524945195331)
                  ·
                    refine ⟨9669895071105787417792997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6446596714070524945195331 9669895071105787417792997)
                    ·
                      refine ⟨1813105325832335140836187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9669895071105787417792997 1813105325832335140836187)
                      ·
                        rfl

theorem cell23_3531010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_3531010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531010 prefixEnd_3531010 := by exact prefixLift 3531010
  have htrace : WordTrace (prefixWord ++ tailWord_3531010) baseStart_3531010 baseEnd_3531010 := by
    simpa [prefixWord, tailWord_3531010, baseEnd_3531010] using wordTrace_append hprefix tailTrace_3531010
  have hstable : (prefixWord ++ tailWord_3531010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531010).length < 2 ^ (prefixWord ++ tailWord_3531010).sum := by decide
  have hdescent : baseEnd_3531010 < baseStart_3531010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531043 : List Nat := [1, 1, 1, 4, 2, 2, 4, 2, 2, 1, 3]
def baseStart_3531043 : Nat := 118140960795 + 3531043 * 2 ^ 59
def prefixEnd_3531043 : Nat := 4983230072969 + 3 ^ 40 * 3531043 * 2
def baseEnd_3531043 : Nat := 1813122270693933511723535

theorem tailTrace_3531043 : CollatzResearch.WordTrace tailWord_3531043 prefixEnd_3531043 1813122270693933511723535 := by
  unfold tailWord_3531043
  simp only [CollatzResearch.WordTrace]
  refine ⟨128787718546641739977917783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85858479031094493318611855 128787718546641739977917783)
  ·
    refine ⟨193181577819962609966876675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128787718546641739977917783 193181577819962609966876675)
    ·
      refine ⟨289772366729943914950315013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193181577819962609966876675 289772366729943914950315013)
      ·
        refine ⟨54332318761864484053184065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 289772366729943914950315013 54332318761864484053184065)
        ·
          refine ⟨40749239071398363039888049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54332318761864484053184065 40749239071398363039888049)
          ·
            refine ⟨30561929303548772279916037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40749239071398363039888049 30561929303548772279916037)
            ·
              refine ⟨5730361744415394802484257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30561929303548772279916037 5730361744415394802484257)
              ·
                refine ⟨4297771308311546101863193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5730361744415394802484257 4297771308311546101863193)
                ·
                  refine ⟨3223328481233659576397395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4297771308311546101863193 3223328481233659576397395)
                  ·
                    refine ⟨4834992721850489364596093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3223328481233659576397395 4834992721850489364596093)
                    ·
                      refine ⟨1813122270693933511723535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4834992721850489364596093 1813122270693933511723535)
                      ·
                        rfl

theorem cell23_3531043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_3531043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531043 prefixEnd_3531043 := by exact prefixLift 3531043
  have htrace : WordTrace (prefixWord ++ tailWord_3531043) baseStart_3531043 baseEnd_3531043 := by
    simpa [prefixWord, tailWord_3531043, baseEnd_3531043] using wordTrace_append hprefix tailTrace_3531043
  have hstable : (prefixWord ++ tailWord_3531043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531043).length < 2 ^ (prefixWord ++ tailWord_3531043).sum := by decide
  have hdescent : baseEnd_3531043 < baseStart_3531043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531044 : List Nat := [2, 3, 1, 3, 1, 4, 2, 2, 1, 2, 2]
def baseStart_3531044 : Nat := 118140960795 + 3531044 * 2 ^ 59
def prefixEnd_3531044 : Nat := 4983230072969 + 3 ^ 40 * 3531044 * 2
def baseEnd_3531044 : Nat := 1813122784174588007811031

theorem tailTrace_3531044 : CollatzResearch.WordTrace tailWord_3531044 prefixEnd_3531044 1813122784174588007811031 := by
  unfold tailWord_3531044
  simp only [CollatzResearch.WordTrace]
  refine ⟨64393877509819058574352093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85858503346425411432469457 64393877509819058574352093)
  ·
    refine ⟨24147704066182146965382035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64393877509819058574352093 24147704066182146965382035)
    ·
      refine ⟨36221556099273220448073053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24147704066182146965382035 36221556099273220448073053)
      ·
        refine ⟨13583083537227457668027395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36221556099273220448073053 13583083537227457668027395)
        ·
          refine ⟨20374625305841186502041093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13583083537227457668027395 20374625305841186502041093)
          ·
            refine ⟨3820242244845222469132705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20374625305841186502041093 3820242244845222469132705)
            ·
              refine ⟨2865181683633916851849529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3820242244845222469132705 2865181683633916851849529)
              ·
                refine ⟨2148886262725437638887147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2865181683633916851849529 2148886262725437638887147)
                ·
                  refine ⟨3223329394088156458330721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2148886262725437638887147 3223329394088156458330721)
                  ·
                    refine ⟨2417497045566117343748041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3223329394088156458330721 2417497045566117343748041)
                    ·
                      refine ⟨1813122784174588007811031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2417497045566117343748041 1813122784174588007811031)
                      ·
                        rfl

theorem cell23_3531044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_3531044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531044 prefixEnd_3531044 := by exact prefixLift 3531044
  have htrace : WordTrace (prefixWord ++ tailWord_3531044) baseStart_3531044 baseEnd_3531044 := by
    simpa [prefixWord, tailWord_3531044, baseEnd_3531044] using wordTrace_append hprefix tailTrace_3531044
  have hstable : (prefixWord ++ tailWord_3531044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531044).length < 2 ^ (prefixWord ++ tailWord_3531044).sum := by decide
  have hdescent : baseEnd_3531044 < baseStart_3531044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531059 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 2, 6]
def baseStart_3531059 : Nat := 118140960795 + 3531059 * 2 ^ 59
def prefixEnd_3531059 : Nat := 4983230072969 + 3 ^ 40 * 3531059 * 2
def baseEnd_3531059 : Nat := 604376828794801816374487

theorem tailTrace_3531059 : CollatzResearch.WordTrace tailWord_3531059 prefixEnd_3531059 604376828794801816374487 := by
  unfold tailWord_3531059
  simp only [CollatzResearch.WordTrace]
  refine ⟨128788302114583774710500231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85858868076389183140333487 128788302114583774710500231)
  ·
    refine ⟨193182453171875662065750347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128788302114583774710500231 193182453171875662065750347)
    ·
      refine ⟨289773679757813493098625521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193182453171875662065750347 289773679757813493098625521)
      ·
        refine ⟨217330259818360119823969141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289773679757813493098625521 217330259818360119823969141)
        ·
          refine ⟨20374711857971261233497107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 217330259818360119823969141 20374711857971261233497107)
          ·
            refine ⟨30562067786956891850245661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20374711857971261233497107 30562067786956891850245661)
            ·
              refine ⟨11460775420108834443842123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30562067786956891850245661 11460775420108834443842123)
              ·
                refine ⟨17191163130163251665763185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11460775420108834443842123 17191163130163251665763185)
                ·
                  refine ⟨12893372347622438749322389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17191163130163251665763185 12893372347622438749322389)
                  ·
                    refine ⟨604376828794801816374487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12893372347622438749322389 604376828794801816374487)
                    ·
                      rfl

theorem cell23_3531059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 6].length) (baseStart_3531059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531059 prefixEnd_3531059 := by exact prefixLift 3531059
  have htrace : WordTrace (prefixWord ++ tailWord_3531059) baseStart_3531059 baseEnd_3531059 := by
    simpa [prefixWord, tailWord_3531059, baseEnd_3531059] using wordTrace_append hprefix tailTrace_3531059
  have hstable : (prefixWord ++ tailWord_3531059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531059).length < 2 ^ (prefixWord ++ tailWord_3531059).sum := by decide
  have hdescent : baseEnd_3531059 < baseStart_3531059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531060 : List Nat := [2, 5, 1, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_3531060 : Nat := 118140960795 + 3531060 * 2 ^ 59
def prefixEnd_3531060 : Nat := 4983230072969 + 3 ^ 40 * 3531060 * 2
def baseEnd_3531060 : Nat := 1813130999865059945210957

theorem tailTrace_3531060 : CollatzResearch.WordTrace tailWord_3531060 prefixEnd_3531060 1813130999865059945210957 := by
  unfold tailWord_3531060
  simp only [CollatzResearch.WordTrace]
  refine ⟨64394169293790075940643317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85858892391720101254191089 64394169293790075940643317)
  ·
    refine ⟨6036953371292819619435311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 64394169293790075940643317 6036953371292819619435311)
    ·
      refine ⟨9055430056939229429152967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6036953371292819619435311 9055430056939229429152967)
      ·
        refine ⟨13583145085408844143729451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9055430056939229429152967 13583145085408844143729451)
        ·
          refine ⟨20374717628113266215594177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13583145085408844143729451 20374717628113266215594177)
          ·
            refine ⟨15281038221084949661695633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20374717628113266215594177 15281038221084949661695633)
            ·
              refine ⟨11460778665813712246271725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15281038221084949661695633 11460778665813712246271725)
              ·
                refine ⟨4297791999680142092351897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11460778665813712246271725 4297791999680142092351897)
                ·
                  refine ⟨3223343999760106569263923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4297791999680142092351897 3223343999760106569263923)
                  ·
                    refine ⟨4835015999640159853895885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3223343999760106569263923 4835015999640159853895885)
                    ·
                      refine ⟨1813130999865059945210957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4835015999640159853895885 1813130999865059945210957)
                      ·
                        rfl

theorem cell23_3531060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_3531060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531060 prefixEnd_3531060 := by exact prefixLift 3531060
  have htrace : WordTrace (prefixWord ++ tailWord_3531060) baseStart_3531060 baseEnd_3531060 := by
    simpa [prefixWord, tailWord_3531060, baseEnd_3531060] using wordTrace_append hprefix tailTrace_3531060
  have hstable : (prefixWord ++ tailWord_3531060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531060).length < 2 ^ (prefixWord ++ tailWord_3531060).sum := by decide
  have hdescent : baseEnd_3531060 < baseStart_3531060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531079 : List Nat := [1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_3531079 : Nat := 118140960795 + 3531079 * 2 ^ 59
def prefixEnd_3531079 : Nat := 4983230072969 + 3 ^ 40 * 3531079 * 2
def baseEnd_3531079 : Nat := 1813140755997495370873369

theorem tailTrace_3531079 : CollatzResearch.WordTrace tailWord_3531079 prefixEnd_3531079 1813140755997495370873369 := by
  unfold tailWord_3531079
  simp only [CollatzResearch.WordTrace]
  refine ⟨128789031574511318126228291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85859354383007545417485527 128789031574511318126228291)
  ·
    refine ⟨193183547361766977189342437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128789031574511318126228291 193183547361766977189342437)
    ·
      refine ⟨36221915130331308223001707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193183547361766977189342437 36221915130331308223001707)
      ·
        refine ⟨54332872695496962334502561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36221915130331308223001707 54332872695496962334502561)
        ·
          refine ⟨40749654521622721750876921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54332872695496962334502561 40749654521622721750876921)
          ·
            refine ⟨30562240891217041313157691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40749654521622721750876921 30562240891217041313157691)
            ·
              refine ⟨45843361336825561969736537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30562240891217041313157691 45843361336825561969736537)
              ·
                refine ⟨34382521002619171477302403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45843361336825561969736537 34382521002619171477302403)
                ·
                  refine ⟨51573781503928757215953605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34382521002619171477302403 51573781503928757215953605)
                  ·
                    refine ⟨9670084031986641977991301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51573781503928757215953605 9670084031986641977991301)
                    ·
                      refine ⟨1813140755997495370873369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9670084031986641977991301 1813140755997495370873369)
                      ·
                        rfl

theorem cell23_3531079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_3531079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531079 prefixEnd_3531079 := by exact prefixLift 3531079
  have htrace : WordTrace (prefixWord ++ tailWord_3531079) baseStart_3531079 baseEnd_3531079 := by
    simpa [prefixWord, tailWord_3531079, baseEnd_3531079] using wordTrace_append hprefix tailTrace_3531079
  have hstable : (prefixWord ++ tailWord_3531079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531079).length < 2 ^ (prefixWord ++ tailWord_3531079).sum := by decide
  have hdescent : baseEnd_3531079 < baseStart_3531079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531106 : List Nat := [3, 3, 2, 1, 1, 2, 1, 3, 7]
def baseStart_3531106 : Nat := 118140960795 + 3531106 * 2 ^ 59
def prefixEnd_3531106 : Nat := 4983230072969 + 3 ^ 40 * 3531106 * 2
def baseEnd_3531106 : Nat := 201461624441685196137305

theorem tailTrace_3531106 : CollatzResearch.WordTrace tailWord_3531106 prefixEnd_3531106 201461624441685196137305 := by
  unfold tailWord_3531106
  simp only [CollatzResearch.WordTrace]
  refine ⟨32197504086353375434365293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85860010896942334491640781 32197504086353375434365293)
  ·
    refine ⟨12074064032382515787886985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32197504086353375434365293 12074064032382515787886985)
    ·
      refine ⟨9055548024286886840915239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12074064032382515787886985 9055548024286886840915239)
      ·
        refine ⟨13583322036430330261372859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9055548024286886840915239 13583322036430330261372859)
        ·
          refine ⟨20374983054645495392059289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13583322036430330261372859 20374983054645495392059289)
          ·
            refine ⟨15281237290984121544044467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20374983054645495392059289 15281237290984121544044467)
            ·
              refine ⟨22921855936476182316066701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15281237290984121544044467 22921855936476182316066701)
              ·
                refine ⟨8595695976178568368525013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22921855936476182316066701 8595695976178568368525013)
                ·
                  refine ⟨201461624441685196137305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8595695976178568368525013 201461624441685196137305)
                  ·
                    rfl

theorem cell23_3531106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_3531106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531106 prefixEnd_3531106 := by exact prefixLift 3531106
  have htrace : WordTrace (prefixWord ++ tailWord_3531106) baseStart_3531106 baseEnd_3531106 := by
    simpa [prefixWord, tailWord_3531106, baseEnd_3531106] using wordTrace_append hprefix tailTrace_3531106
  have hstable : (prefixWord ++ tailWord_3531106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531106).length < 2 ^ (prefixWord ++ tailWord_3531106).sum := by decide
  have hdescent : baseEnd_3531106 < baseStart_3531106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531117 : List Nat := [1, 5, 1, 1, 1, 2, 5, 1, 2, 2, 2]
def baseStart_3531117 : Nat := 118140960795 + 3531117 * 2 ^ 59
def prefixEnd_3531117 : Nat := 4983230072969 + 3 ^ 40 * 3531117 * 2
def baseEnd_3531117 : Nat := 1813160268262366222198195

theorem tailTrace_3531117 : CollatzResearch.WordTrace tailWord_3531117 prefixEnd_3531117 1813160268262366222198195 := by
  unfold tailWord_3531117
  simp only [CollatzResearch.WordTrace]
  refine ⟨128790417548373650616111605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85860278365582433744074403 128790417548373650616111605)
  ·
    refine ⟨12074101645160029745260463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128790417548373650616111605 12074101645160029745260463)
    ·
      refine ⟨18111152467740044617890695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12074101645160029745260463 18111152467740044617890695)
      ·
        refine ⟨27166728701610066926836043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18111152467740044617890695 27166728701610066926836043)
        ·
          refine ⟨40750093052415100390254065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27166728701610066926836043 40750093052415100390254065)
          ·
            refine ⟨30562569789311325292690549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40750093052415100390254065 30562569789311325292690549)
            ·
              refine ⟨2865240917747936746189739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30562569789311325292690549 2865240917747936746189739)
              ·
                refine ⟨4297861376621905119284609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2865240917747936746189739 4297861376621905119284609)
                ·
                  refine ⟨3223396032466428839463457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4297861376621905119284609 3223396032466428839463457)
                  ·
                    refine ⟨2417547024349821629597593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3223396032466428839463457 2417547024349821629597593)
                    ·
                      refine ⟨1813160268262366222198195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2417547024349821629597593 1813160268262366222198195)
                      ·
                        rfl

theorem cell23_3531117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_3531117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531117 prefixEnd_3531117 := by exact prefixLift 3531117
  have htrace : WordTrace (prefixWord ++ tailWord_3531117) baseStart_3531117 baseEnd_3531117 := by
    simpa [prefixWord, tailWord_3531117, baseEnd_3531117] using wordTrace_append hprefix tailTrace_3531117
  have hstable : (prefixWord ++ tailWord_3531117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531117).length < 2 ^ (prefixWord ++ tailWord_3531117).sum := by decide
  have hdescent : baseEnd_3531117 < baseStart_3531117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531119 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 6, 5]
def baseStart_3531119 : Nat := 118140960795 + 3531119 * 2 ^ 59
def prefixEnd_3531119 : Nat := 4983230072969 + 3 ^ 40 * 3531119 * 2
def baseEnd_3531119 : Nat := 604387098407891738124395

theorem tailTrace_3531119 : CollatzResearch.WordTrace tailWord_3531119 prefixEnd_3531119 604387098407891738124395 := by
  unfold tailWord_3531119
  simp only [CollatzResearch.WordTrace]
  refine ⟨128790490494366404957684411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85860326996244269971789607 128790490494366404957684411)
  ·
    refine ⟨193185735741549607436526617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128790490494366404957684411 193185735741549607436526617)
    ·
      refine ⟨144889301806162205577394963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193185735741549607436526617 144889301806162205577394963)
      ·
        refine ⟨217333952709243308366092445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144889301806162205577394963 217333952709243308366092445)
        ·
          refine ⟨81500232265966240637284667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217333952709243308366092445 81500232265966240637284667)
          ·
            refine ⟨122250348398949360955927001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81500232265966240637284667 122250348398949360955927001)
            ·
              refine ⟨91687761299212020716945251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122250348398949360955927001 91687761299212020716945251)
              ·
                refine ⟨137531641948818031075417877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91687761299212020716945251 137531641948818031075417877)
                ·
                  refine ⟨6446795716350845206660213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 137531641948818031075417877 6446795716350845206660213)
                  ·
                    refine ⟨604387098407891738124395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6446795716350845206660213 604387098407891738124395)
                    ·
                      rfl

theorem cell23_3531119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 5].length) (baseStart_3531119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531119 prefixEnd_3531119 := by exact prefixLift 3531119
  have htrace : WordTrace (prefixWord ++ tailWord_3531119) baseStart_3531119 baseEnd_3531119 := by
    simpa [prefixWord, tailWord_3531119, baseEnd_3531119] using wordTrace_append hprefix tailTrace_3531119
  have hstable : (prefixWord ++ tailWord_3531119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531119).length < 2 ^ (prefixWord ++ tailWord_3531119).sum := by decide
  have hdescent : baseEnd_3531119 < baseStart_3531119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531129 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 3, 2, 5]
def baseStart_3531129 : Nat := 118140960795 + 3531129 * 2 ^ 59
def prefixEnd_3531129 : Nat := 4983230072969 + 3 ^ 40 * 3531129 * 2
def baseEnd_3531129 : Nat := 1813166430030220175248139

theorem tailTrace_3531129 : CollatzResearch.WordTrace tailWord_3531129 prefixEnd_3531129 1813166430030220175248139 := by
  unfold tailWord_3531129
  simp only [CollatzResearch.WordTrace]
  refine ⟨128790855224330176665548441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85860570149553451110365627 128790855224330176665548441)
  ·
    refine ⟨96593141418247632499161331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128790855224330176665548441 96593141418247632499161331)
    ·
      refine ⟨144889712127371448748741997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96593141418247632499161331 144889712127371448748741997)
      ·
        refine ⟨54333642047764293280778249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144889712127371448748741997 54333642047764293280778249)
        ·
          refine ⟨40750231535823219960583687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54333642047764293280778249 40750231535823219960583687)
          ·
            refine ⟨61125347303734829940875531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40750231535823219960583687 61125347303734829940875531)
            ·
              refine ⟨91688020955602244911313297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61125347303734829940875531 91688020955602244911313297)
              ·
                refine ⟨68766015716701683683484973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91688020955602244911313297 68766015716701683683484973)
                ·
                  refine ⟨25787255893763131381306865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68766015716701683683484973 25787255893763131381306865)
                  ·
                    refine ⟨19340441920322348535980149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25787255893763131381306865 19340441920322348535980149)
                    ·
                      refine ⟨1813166430030220175248139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19340441920322348535980149 1813166430030220175248139)
                      ·
                        rfl

theorem cell23_3531129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_3531129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531129 prefixEnd_3531129 := by exact prefixLift 3531129
  have htrace : WordTrace (prefixWord ++ tailWord_3531129) baseStart_3531129 baseEnd_3531129 := by
    simpa [prefixWord, tailWord_3531129, baseEnd_3531129] using wordTrace_append hprefix tailTrace_3531129
  have hstable : (prefixWord ++ tailWord_3531129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531129).length < 2 ^ (prefixWord ++ tailWord_3531129).sum := by decide
  have hdescent : baseEnd_3531129 < baseStart_3531129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531193 : List Nat := [1, 2, 1, 4, 3, 1, 1, 3, 2, 2, 3]
def baseStart_3531193 : Nat := 118140960795 + 3531193 * 2 ^ 59
def prefixEnd_3531193 : Nat := 4983230072969 + 3 ^ 40 * 3531193 * 2
def baseEnd_3531193 : Nat := 1813199292792107924847845

theorem tailTrace_3531193 : CollatzResearch.WordTrace tailWord_3531193 prefixEnd_3531193 1813199292792107924847845 := by
  unfold tailWord_3531193
  simp only [CollatzResearch.WordTrace]
  refine ⟨128793189496098315595878233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85862126330732210397252155 128793189496098315595878233)
  ·
    refine ⟨96594892122073736696908675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128793189496098315595878233 96594892122073736696908675)
    ·
      refine ⟨144892338183110605045363013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96594892122073736696908675 144892338183110605045363013)
      ·
        refine ⟨27167313409333238446005565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 144892338183110605045363013 27167313409333238446005565)
        ·
          refine ⟨10187742528499964417252087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27167313409333238446005565 10187742528499964417252087)
          ·
            refine ⟨15281613792749946625878131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10187742528499964417252087 15281613792749946625878131)
            ·
              refine ⟨22922420689124919938817197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15281613792749946625878131 22922420689124919938817197)
              ·
                refine ⟨8595907758421844977056449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22922420689124919938817197 8595907758421844977056449)
                ·
                  refine ⟨6446930818816383732792337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8595907758421844977056449 6446930818816383732792337)
                  ·
                    refine ⟨4835198114112287799594253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6446930818816383732792337 4835198114112287799594253)
                    ·
                      refine ⟨1813199292792107924847845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4835198114112287799594253 1813199292792107924847845)
                      ·
                        rfl

theorem cell23_3531193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_3531193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531193 prefixEnd_3531193 := by exact prefixLift 3531193
  have htrace : WordTrace (prefixWord ++ tailWord_3531193) baseStart_3531193 baseEnd_3531193 := by
    simpa [prefixWord, tailWord_3531193, baseEnd_3531193] using wordTrace_append hprefix tailTrace_3531193
  have hstable : (prefixWord ++ tailWord_3531193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531193).length < 2 ^ (prefixWord ++ tailWord_3531193).sum := by decide
  have hdescent : baseEnd_3531193 < baseStart_3531193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531199 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 8]
def baseStart_3531199 : Nat := 118140960795 + 3531199 * 2 ^ 59
def prefixEnd_3531199 : Nat := 4983230072969 + 3 ^ 40 * 3531199 * 2
def baseEnd_3531199 : Nat := 1813202373676034901372817

theorem tailTrace_3531199 : CollatzResearch.WordTrace tailWord_3531199 prefixEnd_3531199 1813202373676034901372817 := by
  unfold tailWord_3531199
  simp only [CollatzResearch.WordTrace]
  refine ⟨128793408334076578620596651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85862272222717719080397767 128793408334076578620596651)
  ·
    refine ⟨193190112501114867930894977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128793408334076578620596651 193190112501114867930894977)
    ·
      refine ⟨144892584375836150948171233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193190112501114867930894977 144892584375836150948171233)
      ·
        refine ⟨108669438281877113211128425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144892584375836150948171233 108669438281877113211128425)
        ·
          refine ⟨81502078711407834908346319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108669438281877113211128425 81502078711407834908346319)
          ·
            refine ⟨122253118067111752362519479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81502078711407834908346319 122253118067111752362519479)
            ·
              refine ⟨183379677100667628543779219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122253118067111752362519479 183379677100667628543779219)
              ·
                refine ⟨275069515651001442815668829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183379677100667628543779219 275069515651001442815668829)
                ·
                  refine ⟨103151068369125541055875811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 275069515651001442815668829 103151068369125541055875811)
                  ·
                    refine ⟨154726602553688311583813717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 103151068369125541055875811 154726602553688311583813717)
                    ·
                      refine ⟨1813202373676034901372817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 154726602553688311583813717 1813202373676034901372817)
                      ·
                        rfl

theorem cell23_3531199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_3531199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531199 prefixEnd_3531199 := by exact prefixLift 3531199
  have htrace : WordTrace (prefixWord ++ tailWord_3531199) baseStart_3531199 baseEnd_3531199 := by
    simpa [prefixWord, tailWord_3531199, baseEnd_3531199] using wordTrace_append hprefix tailTrace_3531199
  have hstable : (prefixWord ++ tailWord_3531199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531199).length < 2 ^ (prefixWord ++ tailWord_3531199).sum := by decide
  have hdescent : baseEnd_3531199 < baseStart_3531199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531226 : List Nat := [3, 1, 1, 2, 3, 1, 1, 1, 5, 5]
def baseStart_3531226 : Nat := 118140960795 + 3531226 * 2 ^ 59
def prefixEnd_3531226 : Nat := 4983230072969 + 3 ^ 40 * 3531226 * 2
def baseEnd_3531226 : Nat := 604405412551235431911731

theorem tailTrace_3531226 : CollatzResearch.WordTrace tailWord_3531226 prefixEnd_3531226 604405412551235431911731 := by
  unfold tailWord_3531226
  simp only [CollatzResearch.WordTrace]
  refine ⟨32198598276244690557957383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85862928736652508154553021 32198598276244690557957383)
  ·
    refine ⟨48297897414367035836936075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32198598276244690557957383 48297897414367035836936075)
    ·
      refine ⟨72446846121550553755404113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48297897414367035836936075 72446846121550553755404113)
      ·
        refine ⟨54335134591162915316553085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72446846121550553755404113 54335134591162915316553085)
        ·
          refine ⟨20375675471686093243707407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54335134591162915316553085 20375675471686093243707407)
          ·
            refine ⟨30563513207529139865561111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20375675471686093243707407 30563513207529139865561111)
            ·
              refine ⟨45845269811293709798341667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30563513207529139865561111 45845269811293709798341667)
              ·
                refine ⟨68767904716940564697512501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45845269811293709798341667 68767904716940564697512501)
                ·
                  refine ⟨6446991067213177940391797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68767904716940564697512501 6446991067213177940391797)
                  ·
                    refine ⟨604405412551235431911731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6446991067213177940391797 604405412551235431911731)
                    ·
                      rfl

theorem cell23_3531226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_3531226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531226 prefixEnd_3531226 := by exact prefixLift 3531226
  have htrace : WordTrace (prefixWord ++ tailWord_3531226) baseStart_3531226 baseEnd_3531226 := by
    simpa [prefixWord, tailWord_3531226, baseEnd_3531226] using wordTrace_append hprefix tailTrace_3531226
  have hstable : (prefixWord ++ tailWord_3531226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531226).length < 2 ^ (prefixWord ++ tailWord_3531226).sum := by decide
  have hdescent : baseEnd_3531226 < baseStart_3531226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531233 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 1, 5, 2]
def baseStart_3531233 : Nat := 118140960795 + 3531233 * 2 ^ 59
def prefixEnd_3531233 : Nat := 4983230072969 + 3 ^ 40 * 3531233 * 2
def baseEnd_3531233 : Nat := 1813219832018287768347661

theorem tailTrace_3531233 : CollatzResearch.WordTrace tailWord_3531233 prefixEnd_3531233 1813219832018287768347661 := by
  unfold tailWord_3531233
  simp only [CollatzResearch.WordTrace]
  refine ⟨128794648415953402427334353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85863098943968934951556235 128794648415953402427334353)
  ·
    refine ⟨96595986311965051820500765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128794648415953402427334353 96595986311965051820500765)
    ·
      refine ⟨36223494866986894432687787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96595986311965051820500765 36223494866986894432687787)
      ·
        refine ⟨54335242300480341649031681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36223494866986894432687787 54335242300480341649031681)
        ·
          refine ⟨40751431725360256236773761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54335242300480341649031681 40751431725360256236773761)
          ·
            refine ⟨30563573794020192177580321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40751431725360256236773761 30563573794020192177580321)
            ·
              refine ⟨22922680345515144133185241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30563573794020192177580321 22922680345515144133185241)
              ·
                refine ⟨17192010259136358099888931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22922680345515144133185241 17192010259136358099888931)
                ·
                  refine ⟨25788015388704537149833397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17192010259136358099888931 25788015388704537149833397)
                  ·
                    refine ⟨2417626442691050357796881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25788015388704537149833397 2417626442691050357796881)
                    ·
                      refine ⟨1813219832018287768347661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2417626442691050357796881 1813219832018287768347661)
                      ·
                        rfl

theorem cell23_3531233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_3531233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531233 prefixEnd_3531233 := by exact prefixLift 3531233
  have htrace : WordTrace (prefixWord ++ tailWord_3531233) baseStart_3531233 baseEnd_3531233 := by
    simpa [prefixWord, tailWord_3531233, baseEnd_3531233] using wordTrace_append hprefix tailTrace_3531233
  have hstable : (prefixWord ++ tailWord_3531233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531233).length < 2 ^ (prefixWord ++ tailWord_3531233).sum := by decide
  have hdescent : baseEnd_3531233 < baseStart_3531233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531240 : List Nat := [2, 1, 4, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_3531240 : Nat := 118140960795 + 3531240 * 2 ^ 59
def prefixEnd_3531240 : Nat := 4983230072969 + 3 ^ 40 * 3531240 * 2
def baseEnd_3531240 : Nat := 1813223426382869240960129

theorem tailTrace_3531240 : CollatzResearch.WordTrace tailWord_3531240 prefixEnd_3531240 1813223426382869240960129 := by
  unfold tailWord_3531240
  simp only [CollatzResearch.WordTrace]
  refine ⟨64397451863464021311419587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85863269151285361748559449 64397451863464021311419587)
  ·
    refine ⟨96596177795196031967129381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64397451863464021311419587 96596177795196031967129381)
    ·
      refine ⟨18111783336599255993836759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96596177795196031967129381 18111783336599255993836759)
      ·
        refine ⟨27167675004898883990755139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18111783336599255993836759 27167675004898883990755139)
        ·
          refine ⟨40751512507348325986132709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27167675004898883990755139 40751512507348325986132709)
          ·
            refine ⟨7640908595127811122399883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40751512507348325986132709 7640908595127811122399883)
            ·
              refine ⟨11461362892691716683599825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7640908595127811122399883 11461362892691716683599825)
              ·
                refine ⟨8596022169518787512699869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11461362892691716683599825 8596022169518787512699869)
                ·
                  refine ⟨3223508313569545317262451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8596022169518787512699869 3223508313569545317262451)
                  ·
                    refine ⟨4835262470354317975893677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3223508313569545317262451 4835262470354317975893677)
                    ·
                      refine ⟨1813223426382869240960129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4835262470354317975893677 1813223426382869240960129)
                      ·
                        rfl

theorem cell23_3531240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_3531240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531240 prefixEnd_3531240 := by exact prefixLift 3531240
  have htrace : WordTrace (prefixWord ++ tailWord_3531240) baseStart_3531240 baseEnd_3531240 := by
    simpa [prefixWord, tailWord_3531240, baseEnd_3531240] using wordTrace_append hprefix tailTrace_3531240
  have hstable : (prefixWord ++ tailWord_3531240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531240).length < 2 ^ (prefixWord ++ tailWord_3531240).sum := by decide
  have hdescent : baseEnd_3531240 < baseStart_3531240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531256 : List Nat := [2, 1, 2, 1, 1, 4, 1, 4, 1, 6]
def baseStart_3531256 : Nat := 118140960795 + 3531256 * 2 ^ 59
def prefixEnd_3531256 : Nat := 4983230072969 + 3 ^ 40 * 3531256 * 2
def baseEnd_3531256 : Nat := 604410547357780392786685

theorem tailTrace_3531256 : CollatzResearch.WordTrace tailWord_3531256 prefixEnd_3531256 604410547357780392786685 := by
  unfold tailWord_3531256
  simp only [CollatzResearch.WordTrace]
  refine ⟨64397743647435038677710811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85863658196580051570281081 64397743647435038677710811)
  ·
    refine ⟨96596615471152558016566217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64397743647435038677710811 96596615471152558016566217)
    ·
      refine ⟨72447461603364418512424663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96596615471152558016566217 72447461603364418512424663)
      ·
        refine ⟨108671192405046627768636995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72447461603364418512424663 108671192405046627768636995)
        ·
          refine ⟨163006788607569941652955493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108671192405046627768636995 163006788607569941652955493)
          ·
            refine ⟨30563772863919364059929155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163006788607569941652955493 30563772863919364059929155)
            ·
              refine ⟨45845659295879046089893733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30563772863919364059929155 45845659295879046089893733)
              ·
                refine ⟨8596061117977321141855075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45845659295879046089893733 8596061117977321141855075)
                ·
                  refine ⟨12894091676965981712782613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8596061117977321141855075 12894091676965981712782613)
                  ·
                    refine ⟨604410547357780392786685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12894091676965981712782613 604410547357780392786685)
                    ·
                      rfl

theorem cell23_3531256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_3531256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531256 prefixEnd_3531256 := by exact prefixLift 3531256
  have htrace : WordTrace (prefixWord ++ tailWord_3531256) baseStart_3531256 baseEnd_3531256 := by
    simpa [prefixWord, tailWord_3531256, baseEnd_3531256] using wordTrace_append hprefix tailTrace_3531256
  have hstable : (prefixWord ++ tailWord_3531256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531256).length < 2 ^ (prefixWord ++ tailWord_3531256).sum := by decide
  have hdescent : baseEnd_3531256 < baseStart_3531256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531263 : List Nat := [1, 1, 2, 2, 1, 2, 5, 3, 1, 1, 4]
def baseStart_3531263 : Nat := 118140960795 + 3531263 * 2 ^ 59
def prefixEnd_3531263 : Nat := 4983230072969 + 3 ^ 40 * 3531263 * 2
def baseEnd_3531263 : Nat := 1813235236437922650972523

theorem tailTrace_3531263 : CollatzResearch.WordTrace tailWord_3531263 prefixEnd_3531263 1813235236437922650972523 := by
  unfold tailWord_3531263
  simp only [CollatzResearch.WordTrace]
  refine ⟨128795742605844717550926443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85863828403896478367284295 128795742605844717550926443)
  ·
    refine ⟨193193613908767076326389665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128795742605844717550926443 193193613908767076326389665)
    ·
      refine ⟨144895210431575307244792249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193193613908767076326389665 144895210431575307244792249)
      ·
        refine ⟨108671407823681480433594187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144895210431575307244792249 108671407823681480433594187)
        ·
          refine ⟨163007111735522220650391281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108671407823681480433594187 163007111735522220650391281)
          ·
            refine ⟨122255333801641665487793461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163007111735522220650391281 122255333801641665487793461)
            ·
              refine ⟨11461437543903906139480637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122255333801641665487793461 11461437543903906139480637)
              ·
                refine ⟨4298039078963964802305239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11461437543903906139480637 4298039078963964802305239)
                ·
                  refine ⟨6447058618445947203457859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4298039078963964802305239 6447058618445947203457859)
                  ·
                    refine ⟨9670587927668920805186789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6447058618445947203457859 9670587927668920805186789)
                    ·
                      refine ⟨1813235236437922650972523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9670587927668920805186789 1813235236437922650972523)
                      ·
                        rfl

theorem cell23_3531263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 1, 4].length) (baseStart_3531263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531263 prefixEnd_3531263 := by exact prefixLift 3531263
  have htrace : WordTrace (prefixWord ++ tailWord_3531263) baseStart_3531263 baseEnd_3531263 := by
    simpa [prefixWord, tailWord_3531263, baseEnd_3531263] using wordTrace_append hprefix tailTrace_3531263
  have hstable : (prefixWord ++ tailWord_3531263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531263).length < 2 ^ (prefixWord ++ tailWord_3531263).sum := by decide
  have hdescent : baseEnd_3531263 < baseStart_3531263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531273 : List Nat := [1, 2, 1, 1, 3, 1, 2, 6, 2, 4]
def baseStart_3531273 : Nat := 118140960795 + 3531273 * 2 ^ 59
def prefixEnd_3531273 : Nat := 4983230072969 + 3 ^ 40 * 3531273 * 2
def baseEnd_3531273 : Nat := 604413457081489203949159

theorem tailTrace_3531273 : CollatzResearch.WordTrace tailWord_3531273 prefixEnd_3531273 604413457081489203949159 := by
  unfold tailWord_3531273
  simp only [CollatzResearch.WordTrace]
  refine ⟨128796107335808489258790473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85864071557205659505860315 128796107335808489258790473)
  ·
    refine ⟨96597080501856366944092855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128796107335808489258790473 96597080501856366944092855)
    ·
      refine ⟨144895620752784550416139283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96597080501856366944092855 144895620752784550416139283)
      ·
        refine ⟨217343431129176825624208925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144895620752784550416139283 217343431129176825624208925)
        ·
          refine ⟨81503786673441309609078347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217343431129176825624208925 81503786673441309609078347)
          ·
            refine ⟨122255680010161964413617521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81503786673441309609078347 122255680010161964413617521)
            ·
              refine ⟨91691760007621473310213141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122255680010161964413617521 91691760007621473310213141)
              ·
                refine ⟨4298051250357256561416241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 91691760007621473310213141 4298051250357256561416241)
                ·
                  refine ⟨3223538437767942421062181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4298051250357256561416241 3223538437767942421062181)
                  ·
                    refine ⟨604413457081489203949159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3223538437767942421062181 604413457081489203949159)
                    ·
                      rfl

theorem cell23_3531273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 4].length) (baseStart_3531273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531273 prefixEnd_3531273 := by exact prefixLift 3531273
  have htrace : WordTrace (prefixWord ++ tailWord_3531273) baseStart_3531273 baseEnd_3531273 := by
    simpa [prefixWord, tailWord_3531273, baseEnd_3531273] using wordTrace_append hprefix tailTrace_3531273
  have hstable : (prefixWord ++ tailWord_3531273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531273).length < 2 ^ (prefixWord ++ tailWord_3531273).sum := by decide
  have hdescent : baseEnd_3531273 < baseStart_3531273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531293 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_3531293 : Nat := 118140960795 + 3531293 * 2 ^ 59
def prefixEnd_3531293 : Nat := 4983230072969 + 3 ^ 40 * 3531293 * 2
def baseEnd_3531293 : Nat := 1813250640857557533597385

theorem tailTrace_3531293 : CollatzResearch.WordTrace tailWord_3531293 prefixEnd_3531293 1813250640857557533597385 := by
  unfold tailWord_3531293
  simp only [CollatzResearch.WordTrace]
  refine ⟨128796836795736032674518533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85864557863824021783012355 128796836795736032674518533)
  ·
    refine ⟨24149406899200506126472225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128796836795736032674518533 24149406899200506126472225)
    ·
      refine ⟨18112055174400379594854169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24149406899200506126472225 18112055174400379594854169)
      ·
        refine ⟨13584041380800284696140627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18112055174400379594854169 13584041380800284696140627)
        ·
          refine ⟨20376062071200427044210941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13584041380800284696140627 20376062071200427044210941)
          ·
            refine ⟨7641023276700160141579103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20376062071200427044210941 7641023276700160141579103)
            ·
              refine ⟨11461534915050240212368655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7641023276700160141579103 11461534915050240212368655)
              ·
                refine ⟨17192302372575360318552983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11461534915050240212368655 17192302372575360318552983)
                ·
                  refine ⟨25788453558863040477829475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17192302372575360318552983 25788453558863040477829475)
                  ·
                    refine ⟨38682680338294560716744213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25788453558863040477829475 38682680338294560716744213)
                    ·
                      refine ⟨1813250640857557533597385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38682680338294560716744213 1813250640857557533597385)
                      ·
                        rfl

theorem cell23_3531293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_3531293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531293 prefixEnd_3531293 := by exact prefixLift 3531293
  have htrace : WordTrace (prefixWord ++ tailWord_3531293) baseStart_3531293 baseEnd_3531293 := by
    simpa [prefixWord, tailWord_3531293, baseEnd_3531293] using wordTrace_append hprefix tailTrace_3531293
  have hstable : (prefixWord ++ tailWord_3531293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531293).length < 2 ^ (prefixWord ++ tailWord_3531293).sum := by decide
  have hdescent : baseEnd_3531293 < baseStart_3531293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531313 : List Nat := [1, 2, 2, 3, 1, 1, 2, 4, 1, 3, 3]
def baseStart_3531313 : Nat := 118140960795 + 3531313 * 2 ^ 59
def prefixEnd_3531313 : Nat := 4983230072969 + 3 ^ 40 * 3531313 * 2
def baseEnd_3531313 : Nat := 1813260910470647455347293

theorem tailTrace_3531313 : CollatzResearch.WordTrace tailWord_3531313 prefixEnd_3531313 1813260910470647455347293 := by
  unfold tailWord_3531313
  simp only [CollatzResearch.WordTrace]
  refine ⟨128797566255663576090246593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85865044170442384060164395 128797566255663576090246593)
  ·
    refine ⟨96598174691747682067684945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128797566255663576090246593 96598174691747682067684945)
    ·
      refine ⟨72448631018810761550763709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96598174691747682067684945 72448631018810761550763709)
      ·
        refine ⟨27168236632054035581536391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72448631018810761550763709 27168236632054035581536391)
        ·
          refine ⟨40752354948081053372304587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27168236632054035581536391 40752354948081053372304587)
          ·
            refine ⟨61128532422121580058456881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40752354948081053372304587 61128532422121580058456881)
            ·
              refine ⟨45846399316591185043842661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61128532422121580058456881 45846399316591185043842661)
              ·
                refine ⟨8596199871860847195720499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45846399316591185043842661 8596199871860847195720499)
                ·
                  refine ⟨12894299807791270793580749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8596199871860847195720499 12894299807791270793580749)
                  ·
                    refine ⟨4835362427921726547592781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12894299807791270793580749 4835362427921726547592781)
                    ·
                      refine ⟨1813260910470647455347293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4835362427921726547592781 1813260910470647455347293)
                      ·
                        rfl

theorem cell23_3531313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_3531313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531313 prefixEnd_3531313 := by exact prefixLift 3531313
  have htrace : WordTrace (prefixWord ++ tailWord_3531313) baseStart_3531313 baseEnd_3531313 := by
    simpa [prefixWord, tailWord_3531313, baseEnd_3531313] using wordTrace_append hprefix tailTrace_3531313
  have hstable : (prefixWord ++ tailWord_3531313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531313).length < 2 ^ (prefixWord ++ tailWord_3531313).sum := by decide
  have hdescent : baseEnd_3531313 < baseStart_3531313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531314 : List Nat := [3, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2]
def baseStart_3531314 : Nat := 118140960795 + 3531314 * 2 ^ 59
def prefixEnd_3531314 : Nat := 4983230072969 + 3 ^ 40 * 3531314 * 2
def baseEnd_3531314 : Nat := 1813261423951301951434789

theorem tailTrace_3531314 : CollatzResearch.WordTrace tailWord_3531314 prefixEnd_3531314 1813261423951301951434789 := by
  unfold tailWord_3531314
  simp only [CollatzResearch.WordTrace]
  refine ⟨32199400682164988315258249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85865068485773302174021997 32199400682164988315258249)
  ·
    refine ⟨24149550511623741236443687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32199400682164988315258249 24149550511623741236443687)
    ·
      refine ⟨36224325767435611854665531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24149550511623741236443687 36224325767435611854665531)
      ·
        refine ⟨54336488651153417781998297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36224325767435611854665531 54336488651153417781998297)
        ·
          refine ⟨40752366488365063336498723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54336488651153417781998297 40752366488365063336498723)
          ·
            refine ⟨61128549732547595004748085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40752366488365063336498723 61128549732547595004748085)
            ·
              refine ⟨5730801537426337031695133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61128549732547595004748085 5730801537426337031695133)
              ·
                refine ⟨2149050576534876386885675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5730801537426337031695133 2149050576534876386885675)
                ·
                  refine ⟨3223575864802314580328513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2149050576534876386885675 3223575864802314580328513)
                  ·
                    refine ⟨2417681898601735935246385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3223575864802314580328513 2417681898601735935246385)
                    ·
                      refine ⟨1813261423951301951434789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2417681898601735935246385 1813261423951301951434789)
                      ·
                        rfl

theorem cell23_3531314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2].length) (baseStart_3531314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531314 prefixEnd_3531314 := by exact prefixLift 3531314
  have htrace : WordTrace (prefixWord ++ tailWord_3531314) baseStart_3531314 baseEnd_3531314 := by
    simpa [prefixWord, tailWord_3531314, baseEnd_3531314] using wordTrace_append hprefix tailTrace_3531314
  have hstable : (prefixWord ++ tailWord_3531314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531314).length < 2 ^ (prefixWord ++ tailWord_3531314).sum := by decide
  have hdescent : baseEnd_3531314 < baseStart_3531314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531340 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 3, 3, 2]
def baseStart_3531340 : Nat := 118140960795 + 3531340 * 2 ^ 59
def prefixEnd_3531340 : Nat := 4983230072969 + 3 ^ 40 * 3531340 * 2
def baseEnd_3531340 : Nat := 1813274774448318849709669

theorem tailTrace_3531340 : CollatzResearch.WordTrace tailWord_3531340 prefixEnd_3531340 1813274774448318849709669 := by
  unfold tailWord_3531340
  simp only [CollatzResearch.WordTrace]
  refine ⟨64399275513282879850739737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85865700684377173134319649 64399275513282879850739737)
  ·
    refine ⟨48299456634962159888054803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64399275513282879850739737 48299456634962159888054803)
    ·
      refine ⟨72449184952443239832082205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48299456634962159888054803 72449184952443239832082205)
      ·
        refine ⟨27168444357166214937030827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72449184952443239832082205 27168444357166214937030827)
        ·
          refine ⟨40752666535749322405546241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27168444357166214937030827 40752666535749322405546241)
          ·
            refine ⟨30564499901811991804159681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40752666535749322405546241 30564499901811991804159681)
            ·
              refine ⟨22923374926358993853119761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30564499901811991804159681 22923374926358993853119761)
              ·
                refine ⟨17192531194769245389839821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22923374926358993853119761 17192531194769245389839821)
                ·
                  refine ⟨6447199198038467021189933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17192531194769245389839821 6447199198038467021189933)
                  ·
                    refine ⟨2417699699264425132946225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6447199198038467021189933 2417699699264425132946225)
                    ·
                      refine ⟨1813274774448318849709669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2417699699264425132946225 1813274774448318849709669)
                      ·
                        rfl

theorem cell23_3531340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_3531340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531340 prefixEnd_3531340 := by exact prefixLift 3531340
  have htrace : WordTrace (prefixWord ++ tailWord_3531340) baseStart_3531340 baseEnd_3531340 := by
    simpa [prefixWord, tailWord_3531340, baseEnd_3531340] using wordTrace_append hprefix tailTrace_3531340
  have hstable : (prefixWord ++ tailWord_3531340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531340).length < 2 ^ (prefixWord ++ tailWord_3531340).sum := by decide
  have hdescent : baseEnd_3531340 < baseStart_3531340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531393 : List Nat := [1, 2, 4, 2, 1, 1, 2, 3, 7]
def baseStart_3531393 : Nat := 118140960795 + 3531393 * 2 ^ 59
def prefixEnd_3531393 : Nat := 4983230072969 + 3 ^ 40 * 3531393 * 2
def baseEnd_3531393 : Nat := 201477998769223015816325

theorem tailTrace_3531393 : CollatzResearch.WordTrace tailWord_3531393 prefixEnd_3531393 201477998769223015816325 := by
  unfold tailWord_3531393
  simp only [CollatzResearch.WordTrace]
  refine ⟨128800484095373749753158833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85866989396915833168772555 128800484095373749753158833)
  ·
    refine ⟨96600363071530312314869125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128800484095373749753158833 96600363071530312314869125)
    ·
      refine ⟨18112568075911933559037961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96600363071530312314869125 18112568075911933559037961)
      ·
        refine ⟨13584426056933950169278471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18112568075911933559037961 13584426056933950169278471)
        ·
          refine ⟨20376639085400925253917707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13584426056933950169278471 20376639085400925253917707)
          ·
            refine ⟨30564958628101387880876561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20376639085400925253917707 30564958628101387880876561)
            ·
              refine ⟨22923718971076040910657421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30564958628101387880876561 22923718971076040910657421)
              ·
                refine ⟨8596394614153515341496533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22923718971076040910657421 8596394614153515341496533)
                ·
                  refine ⟨201477998769223015816325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8596394614153515341496533 201477998769223015816325)
                  ·
                    rfl

theorem cell23_3531393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 7].length) (baseStart_3531393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531393 prefixEnd_3531393 := by exact prefixLift 3531393
  have htrace : WordTrace (prefixWord ++ tailWord_3531393) baseStart_3531393 baseEnd_3531393 := by
    simpa [prefixWord, tailWord_3531393, baseEnd_3531393] using wordTrace_append hprefix tailTrace_3531393
  have hstable : (prefixWord ++ tailWord_3531393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531393).length < 2 ^ (prefixWord ++ tailWord_3531393).sum := by decide
  have hdescent : baseEnd_3531393 < baseStart_3531393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531410 : List Nat := [3, 2, 3, 1, 2, 2, 1, 2, 7]
def baseStart_3531410 : Nat := 118140960795 + 3531410 * 2 ^ 59
def prefixEnd_3531410 : Nat := 4983230072969 + 3 ^ 40 * 3531410 * 2
def baseEnd_3531410 : Nat := 201478968677125952870483

theorem tailTrace_3531410 : CollatzResearch.WordTrace tailWord_3531410 prefixEnd_3531410 201478968677125952870483 := by
  unfold tailWord_3531410
  simp only [CollatzResearch.WordTrace]
  refine ⟨32200276034078040414131921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85867402757541441104351789 32200276034078040414131921)
  ·
    refine ⟨24150207025558530310598941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32200276034078040414131921 24150207025558530310598941)
    ·
      refine ⟨9056327634584448866474603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24150207025558530310598941 9056327634584448866474603)
      ·
        refine ⟨13584491451876673299711905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9056327634584448866474603 13584491451876673299711905)
        ·
          refine ⟨10188368588907504974783929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13584491451876673299711905 10188368588907504974783929)
          ·
            refine ⟨7641276441680628731087947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10188368588907504974783929 7641276441680628731087947)
            ·
              refine ⟨11461914662520943096631921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7641276441680628731087947 11461914662520943096631921)
              ·
                refine ⟨8596435996890707322473941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11461914662520943096631921 8596435996890707322473941)
                ·
                  refine ⟨201478968677125952870483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8596435996890707322473941 201478968677125952870483)
                  ·
                    rfl

theorem cell23_3531410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_3531410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531410 prefixEnd_3531410 := by exact prefixLift 3531410
  have htrace : WordTrace (prefixWord ++ tailWord_3531410) baseStart_3531410 baseEnd_3531410 := by
    simpa [prefixWord, tailWord_3531410, baseEnd_3531410] using wordTrace_append hprefix tailTrace_3531410
  have hstable : (prefixWord ++ tailWord_3531410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531410).length < 2 ^ (prefixWord ++ tailWord_3531410).sum := by decide
  have hdescent : baseEnd_3531410 < baseStart_3531410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531438 : List Nat := [4, 1, 4, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_3531438 : Nat := 118140960795 + 3531438 * 2 ^ 59
def prefixEnd_3531438 : Nat := 4983230072969 + 3 ^ 40 * 3531438 * 2
def baseEnd_3531438 : Nat := 1813325095552459466284219

theorem tailTrace_3531438 : CollatzResearch.WordTrace tailWord_3531438 prefixEnd_3531438 1813325095552459466284219 := by
  unfold tailWord_3531438
  simp only [CollatzResearch.WordTrace]
  refine ⟨16100265672526340304818371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85868083586807148292364645 16100265672526340304818371)
  ·
    refine ⟨24150398508789510457227557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16100265672526340304818371 24150398508789510457227557)
    ·
      refine ⟨4528199720398033210730167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24150398508789510457227557 4528199720398033210730167)
      ·
        refine ⟨6792299580597049816095251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4528199720398033210730167 6792299580597049816095251)
        ·
          refine ⟨10188449370895574724142877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6792299580597049816095251 10188449370895574724142877)
          ·
            refine ⟨3820668514085840521553579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10188449370895574724142877 3820668514085840521553579)
            ·
              refine ⟨5731002771128760782330369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3820668514085840521553579 5731002771128760782330369)
              ·
                refine ⟨4298252078346570586747777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5731002771128760782330369 4298252078346570586747777)
                ·
                  refine ⟨3223689058759927940060833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4298252078346570586747777 3223689058759927940060833)
                  ·
                    refine ⟨2417766794069945955045625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3223689058759927940060833 2417766794069945955045625)
                    ·
                      refine ⟨1813325095552459466284219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2417766794069945955045625 1813325095552459466284219)
                      ·
                        rfl

theorem cell23_3531438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_3531438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531438 prefixEnd_3531438 := by exact prefixLift 3531438
  have htrace : WordTrace (prefixWord ++ tailWord_3531438) baseStart_3531438 baseEnd_3531438 := by
    simpa [prefixWord, tailWord_3531438, baseEnd_3531438] using wordTrace_append hprefix tailTrace_3531438
  have hstable : (prefixWord ++ tailWord_3531438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531438).length < 2 ^ (prefixWord ++ tailWord_3531438).sum := by decide
  have hdescent : baseEnd_3531438 < baseStart_3531438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531460 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_3531460 : Nat := 118140960795 + 3531460 * 2 ^ 59
def prefixEnd_3531460 : Nat := 4983230072969 + 3 ^ 40 * 3531460 * 2
def baseEnd_3531460 : Nat := 1813336392126858380209117

theorem tailTrace_3531460 : CollatzResearch.WordTrace tailWord_3531460 prefixEnd_3531460 1813336392126858380209117 := by
  unfold tailWord_3531460
  simp only [CollatzResearch.WordTrace]
  refine ⟨64401463893065510097923917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85868618524087346797231889 64401463893065510097923917)
  ·
    refine ⟨24150548959899566286721469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64401463893065510097923917 24150548959899566286721469)
    ·
      refine ⟨9056455859962337357520551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24150548959899566286721469 9056455859962337357520551)
      ·
        refine ⟨13584683789943506036280827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9056455859962337357520551 13584683789943506036280827)
        ·
          refine ⟨20377025684915259054421241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13584683789943506036280827 20377025684915259054421241)
          ·
            refine ⟨15282769263686444290815931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20377025684915259054421241 15282769263686444290815931)
            ·
              refine ⟨22924153895529666436223897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15282769263686444290815931 22924153895529666436223897)
              ·
                refine ⟨17193115421647249827167923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22924153895529666436223897 17193115421647249827167923)
                ·
                  refine ⟨25789673132470874740751885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17193115421647249827167923 25789673132470874740751885)
                  ·
                    refine ⟨9671127424676578027781957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25789673132470874740751885 9671127424676578027781957)
                    ·
                      refine ⟨1813336392126858380209117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9671127424676578027781957 1813336392126858380209117)
                      ·
                        rfl

theorem cell23_3531460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_3531460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531460 prefixEnd_3531460 := by exact prefixLift 3531460
  have htrace : WordTrace (prefixWord ++ tailWord_3531460) baseStart_3531460 baseEnd_3531460 := by
    simpa [prefixWord, tailWord_3531460, baseEnd_3531460] using wordTrace_append hprefix tailTrace_3531460
  have hstable : (prefixWord ++ tailWord_3531460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531460).length < 2 ^ (prefixWord ++ tailWord_3531460).sum := by decide
  have hdescent : baseEnd_3531460 < baseStart_3531460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531473 : List Nat := [1, 2, 2, 1, 2, 3, 1, 1, 2, 4, 4]
def baseStart_3531473 : Nat := 118140960795 + 3531473 * 2 ^ 59
def prefixEnd_3531473 : Nat := 4983230072969 + 3 ^ 40 * 3531473 * 2
def baseEnd_3531473 : Nat := 1813343067375366829346557

theorem tailTrace_3531473 : CollatzResearch.WordTrace tailWord_3531473 prefixEnd_3531473 1813343067375366829346557 := by
  unfold tailWord_3531473
  simp only [CollatzResearch.WordTrace]
  refine ⟨128803401935083923416071073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85868934623389282277380715 128803401935083923416071073)
  ·
    refine ⟨96602551451312942562053305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128803401935083923416071073 96602551451312942562053305)
    ·
      refine ⟨72451913588484706921539979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96602551451312942562053305 72451913588484706921539979)
      ·
        refine ⟨108677870382727060382309969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72451913588484706921539979 108677870382727060382309969)
        ·
          refine ⟨81508402787045295286732477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108677870382727060382309969 81508402787045295286732477)
          ·
            refine ⟨30565651045141985732524679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81508402787045295286732477 30565651045141985732524679)
            ·
              refine ⟨45848476567712978598787019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30565651045141985732524679 45848476567712978598787019)
              ·
                refine ⟨68772714851569467898180529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45848476567712978598787019 68772714851569467898180529)
                ·
                  refine ⟨51579536138677100923635397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68772714851569467898180529 51579536138677100923635397)
                  ·
                    refine ⟨9671163026001956423181637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 51579536138677100923635397 9671163026001956423181637)
                    ·
                      refine ⟨1813343067375366829346557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9671163026001956423181637 1813343067375366829346557)
                      ·
                        rfl

theorem cell23_3531473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_3531473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531473 prefixEnd_3531473 := by exact prefixLift 3531473
  have htrace : WordTrace (prefixWord ++ tailWord_3531473) baseStart_3531473 baseEnd_3531473 := by
    simpa [prefixWord, tailWord_3531473, baseEnd_3531473] using wordTrace_append hprefix tailTrace_3531473
  have hstable : (prefixWord ++ tailWord_3531473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531473).length < 2 ^ (prefixWord ++ tailWord_3531473).sum := by decide
  have hdescent : baseEnd_3531473 < baseStart_3531473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531480 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 1, 4, 3]
def baseStart_3531480 : Nat := 118140960795 + 3531480 * 2 ^ 59
def prefixEnd_3531480 : Nat := 4983230072969 + 3 ^ 40 * 3531480 * 2
def baseEnd_3531480 : Nat := 1813346661739948301959025

theorem tailTrace_3531480 : CollatzResearch.WordTrace tailWord_3531480 prefixEnd_3531480 1813346661739948301959025 := by
  unfold tailWord_3531480
  simp only [CollatzResearch.WordTrace]
  refine ⟨64401828623029281805787947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85869104830705709074383929 64401828623029281805787947)
  ·
    refine ⟨96602742934543922708681921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64401828623029281805787947 96602742934543922708681921)
    ·
      refine ⟨72452057200907942031511441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96602742934543922708681921 72452057200907942031511441)
      ·
        refine ⟨54339042900680956523633581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72452057200907942031511441 54339042900680956523633581)
        ·
          refine ⟨20377141087755358696362593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54339042900680956523633581 20377141087755358696362593)
          ·
            refine ⟨15282855815816519022271945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20377141087755358696362593 15282855815816519022271945)
            ·
              refine ⟨11462141861862389266703959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15282855815816519022271945 11462141861862389266703959)
              ·
                refine ⟨17193212792793583900055939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11462141861862389266703959 17193212792793583900055939)
                ·
                  refine ⟨25789819189190375850083909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17193212792793583900055939 25789819189190375850083909)
                  ·
                    refine ⟨4835591097973195471890733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25789819189190375850083909 4835591097973195471890733)
                    ·
                      refine ⟨1813346661739948301959025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4835591097973195471890733 1813346661739948301959025)
                      ·
                        rfl

theorem cell23_3531480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_3531480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531480 prefixEnd_3531480 := by exact prefixLift 3531480
  have htrace : WordTrace (prefixWord ++ tailWord_3531480) baseStart_3531480 baseEnd_3531480 := by
    simpa [prefixWord, tailWord_3531480, baseEnd_3531480] using wordTrace_append hprefix tailTrace_3531480
  have hstable : (prefixWord ++ tailWord_3531480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531480).length < 2 ^ (prefixWord ++ tailWord_3531480).sum := by decide
  have hdescent : baseEnd_3531480 < baseStart_3531480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531504 : List Nat := [2, 1, 1, 1, 3, 1, 7, 2, 1, 4]
def baseStart_3531504 : Nat := 118140960795 + 3531504 * 2 ^ 59
def prefixEnd_3531504 : Nat := 4983230072969 + 3 ^ 40 * 3531504 * 2
def baseEnd_3531504 : Nat := 604452995091885402686305

theorem tailTrace_3531504 : CollatzResearch.WordTrace tailWord_3531504 prefixEnd_3531504 604452995091885402686305 := by
  unfold tailWord_3531504
  simp only [CollatzResearch.WordTrace]
  refine ⟨64402266298985807855224783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85869688398647743806966377 64402266298985807855224783)
  ·
    refine ⟨96603399448478711782837175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64402266298985807855224783 96603399448478711782837175)
    ·
      refine ⟨144905099172718067674255763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96603399448478711782837175 144905099172718067674255763)
      ·
        refine ⟨217357648759077101511383645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144905099172718067674255763 217357648759077101511383645)
        ·
          refine ⟨81509118284653913066768867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 217357648759077101511383645 81509118284653913066768867)
          ·
            refine ⟨122263677426980869600153301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81509118284653913066768867 122263677426980869600153301)
            ·
              refine ⟨2865554939694864131253593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 122263677426980869600153301 2865554939694864131253593)
              ·
                refine ⟨2149166204771148098440195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2865554939694864131253593 2149166204771148098440195)
                ·
                  refine ⟨3223749307156722147660293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2149166204771148098440195 3223749307156722147660293)
                  ·
                    refine ⟨604452995091885402686305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3223749307156722147660293 604452995091885402686305)
                    ·
                      rfl

theorem cell23_3531504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 2, 1, 4].length) (baseStart_3531504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531504 prefixEnd_3531504 := by exact prefixLift 3531504
  have htrace : WordTrace (prefixWord ++ tailWord_3531504) baseStart_3531504 baseEnd_3531504 := by
    simpa [prefixWord, tailWord_3531504, baseEnd_3531504] using wordTrace_append hprefix tailTrace_3531504
  have hstable : (prefixWord ++ tailWord_3531504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531504).length < 2 ^ (prefixWord ++ tailWord_3531504).sum := by decide
  have hdescent : baseEnd_3531504 < baseStart_3531504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531530 : List Nat := [3, 1, 2, 2, 1, 2, 3, 1, 3, 5]
def baseStart_3531530 : Nat := 118140960795 + 3531530 * 2 ^ 59
def prefixEnd_3531530 : Nat := 4983230072969 + 3 ^ 40 * 3531530 * 2
def baseEnd_3531530 : Nat := 604457445257557702111265

theorem tailTrace_3531530 : CollatzResearch.WordTrace tailWord_3531530 prefixEnd_3531530 604457445257557702111265 := by
  unfold tailWord_3531530
  simp only [CollatzResearch.WordTrace]
  refine ⟨32201370223969355537724011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85870320597251614767264029 32201370223969355537724011)
  ·
    refine ⟨48302055335954033306586017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32201370223969355537724011 48302055335954033306586017)
    ·
      refine ⟨36226541501965524979939513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48302055335954033306586017 36226541501965524979939513)
      ·
        refine ⟨27169906126474143734954635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36226541501965524979939513 27169906126474143734954635)
        ·
          refine ⟨40754859189711215602431953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27169906126474143734954635 40754859189711215602431953)
          ·
            refine ⟨30566144392283411701823965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40754859189711215602431953 30566144392283411701823965)
            ·
              refine ⟨11462304147106279388183987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30566144392283411701823965 11462304147106279388183987)
              ·
                refine ⟨17193456220659419082275981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11462304147106279388183987 17193456220659419082275981)
                ·
                  refine ⟨6447546082747282155853493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17193456220659419082275981 6447546082747282155853493)
                  ·
                    refine ⟨604457445257557702111265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6447546082747282155853493 604457445257557702111265)
                    ·
                      rfl

theorem cell23_3531530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_3531530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531530 prefixEnd_3531530 := by exact prefixLift 3531530
  have htrace : WordTrace (prefixWord ++ tailWord_3531530) baseStart_3531530 baseEnd_3531530 := by
    simpa [prefixWord, tailWord_3531530, baseEnd_3531530] using wordTrace_append hprefix tailTrace_3531530
  have hstable : (prefixWord ++ tailWord_3531530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531530).length < 2 ^ (prefixWord ++ tailWord_3531530).sum := by decide
  have hdescent : baseEnd_3531530 < baseStart_3531530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531537 : List Nat := [1, 2, 2, 1, 1, 3, 3, 3, 2, 3, 2]
def baseStart_3531537 : Nat := 118140960795 + 3531537 * 2 ^ 59
def prefixEnd_3531537 : Nat := 4983230072969 + 3 ^ 40 * 3531537 * 2
def baseEnd_3531537 : Nat := 1813375930137254578946263

theorem tailTrace_3531537 : CollatzResearch.WordTrace tailWord_3531537 prefixEnd_3531537 1813375930137254578946263 := by
  unfold tailWord_3531537
  simp only [CollatzResearch.WordTrace]
  refine ⟨128805736206852062346400865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85870490804568041564267243 128805736206852062346400865)
  ·
    refine ⟨96604302155139046759800649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128805736206852062346400865 96604302155139046759800649)
    ·
      refine ⟨72453226616354285069850487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96604302155139046759800649 72453226616354285069850487)
      ·
        refine ⟨108679839924531427604775731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72453226616354285069850487 108679839924531427604775731)
        ·
          refine ⟨163019759886797141407163597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108679839924531427604775731 163019759886797141407163597)
          ·
            refine ⟨61132409957548928027686349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163019759886797141407163597 61132409957548928027686349)
            ·
              refine ⟨22924653734080848010382381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61132409957548928027686349 22924653734080848010382381)
              ·
                refine ⟨8596745150280318003893393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22924653734080848010382381 8596745150280318003893393)
                ·
                  refine ⟨6447558862710238502920045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8596745150280318003893393 6447558862710238502920045)
                  ·
                    refine ⟨2417834573516339438595017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6447558862710238502920045 2417834573516339438595017)
                    ·
                      refine ⟨1813375930137254578946263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2417834573516339438595017 1813375930137254578946263)
                      ·
                        rfl

theorem cell23_3531537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 3, 2].length) (baseStart_3531537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531537 prefixEnd_3531537 := by exact prefixLift 3531537
  have htrace : WordTrace (prefixWord ++ tailWord_3531537) baseStart_3531537 baseEnd_3531537 := by
    simpa [prefixWord, tailWord_3531537, baseEnd_3531537] using wordTrace_append hprefix tailTrace_3531537
  have hstable : (prefixWord ++ tailWord_3531537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531537).length < 2 ^ (prefixWord ++ tailWord_3531537).sum := by decide
  have hdescent : baseEnd_3531537 < baseStart_3531537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531544 : List Nat := [2, 1, 2, 3, 1, 1, 1, 7, 1, 1, 3]
def baseStart_3531544 : Nat := 118140960795 + 3531544 * 2 ^ 59
def prefixEnd_3531544 : Nat := 4983230072969 + 3 ^ 40 * 3531544 * 2
def baseEnd_3531544 : Nat := 1813379524501836051558731

theorem tailTrace_3531544 : CollatzResearch.WordTrace tailWord_3531544 prefixEnd_3531544 1813379524501836051558731 := by
  unfold tailWord_3531544
  simp only [CollatzResearch.WordTrace]
  refine ⟨64402995758913351270952843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85870661011884468361270457 64402995758913351270952843)
  ·
    refine ⟨96604493638370026906429265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64402995758913351270952843 96604493638370026906429265)
    ·
      refine ⟨72453370228777520179821949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96604493638370026906429265 72453370228777520179821949)
      ·
        refine ⟨27170013835791570067433231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72453370228777520179821949 27170013835791570067433231)
        ·
          refine ⟨40755020753687355101149847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27170013835791570067433231 40755020753687355101149847)
          ·
            refine ⟨61132531130531032651724771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40755020753687355101149847 61132531130531032651724771)
            ·
              refine ⟨91698796695796548977587157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61132531130531032651724771 91698796695796548977587157)
              ·
                refine ⟨2149190547557731616662199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 91698796695796548977587157 2149190547557731616662199)
                ·
                  refine ⟨3223785821336597424993299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2149190547557731616662199 3223785821336597424993299)
                  ·
                    refine ⟨4835678732004896137489949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3223785821336597424993299 4835678732004896137489949)
                    ·
                      refine ⟨1813379524501836051558731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4835678732004896137489949 1813379524501836051558731)
                      ·
                        rfl

theorem cell23_3531544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_3531544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531544 prefixEnd_3531544 := by exact prefixLift 3531544
  have htrace : WordTrace (prefixWord ++ tailWord_3531544) baseStart_3531544 baseEnd_3531544 := by
    simpa [prefixWord, tailWord_3531544, baseEnd_3531544] using wordTrace_append hprefix tailTrace_3531544
  have hstable : (prefixWord ++ tailWord_3531544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531544).length < 2 ^ (prefixWord ++ tailWord_3531544).sum := by decide
  have hdescent : baseEnd_3531544 < baseStart_3531544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531554 : List Nat := [3, 3, 1, 1, 2, 2, 2, 2, 2, 3, 2]
def baseStart_3531554 : Nat := 118140960795 + 3531554 * 2 ^ 59
def prefixEnd_3531554 : Nat := 4983230072969 + 3 ^ 40 * 3531554 * 2
def baseEnd_3531554 : Nat := 1813384659308381012433685

theorem tailTrace_3531554 : CollatzResearch.WordTrace tailWord_3531554 prefixEnd_3531554 1813384659308381012433685 := by
  unfold tailWord_3531554
  simp only [CollatzResearch.WordTrace]
  refine ⟨32201589061947618562442429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85870904165193649499846477 32201589061947618562442429)
  ·
    refine ⟨12075595898230356960915911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32201589061947618562442429 12075595898230356960915911)
    ·
      refine ⟨18113393847345535441373867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12075595898230356960915911 18113393847345535441373867)
      ·
        refine ⟨27170090771018303162060801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18113393847345535441373867 27170090771018303162060801)
        ·
          refine ⟨20377568078263727371545601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27170090771018303162060801 20377568078263727371545601)
          ·
            refine ⟨15283176058697795528659201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20377568078263727371545601 15283176058697795528659201)
            ·
              refine ⟨11462382044023346646494401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15283176058697795528659201 11462382044023346646494401)
              ·
                refine ⟨8596786533017509984870801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11462382044023346646494401 8596786533017509984870801)
                ·
                  refine ⟨6447589899763132488653101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8596786533017509984870801 6447589899763132488653101)
                  ·
                    refine ⟨2417846212411174683244913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6447589899763132488653101 2417846212411174683244913)
                    ·
                      refine ⟨1813384659308381012433685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2417846212411174683244913 1813384659308381012433685)
                      ·
                        rfl

theorem cell23_3531554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_3531554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531554 prefixEnd_3531554 := by exact prefixLift 3531554
  have htrace : WordTrace (prefixWord ++ tailWord_3531554) baseStart_3531554 baseEnd_3531554 := by
    simpa [prefixWord, tailWord_3531554, baseEnd_3531554] using wordTrace_append hprefix tailTrace_3531554
  have hstable : (prefixWord ++ tailWord_3531554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531554).length < 2 ^ (prefixWord ++ tailWord_3531554).sum := by decide
  have hdescent : baseEnd_3531554 < baseStart_3531554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531560 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 3, 6]
def baseStart_3531560 : Nat := 118140960795 + 3531560 * 2 ^ 59
def prefixEnd_3531560 : Nat := 4983230072969 + 3 ^ 40 * 3531560 * 2
def baseEnd_3531560 : Nat := 604462580064102662986219

theorem tailTrace_3531560 : CollatzResearch.WordTrace tailWord_3531560 prefixEnd_3531560 604462580064102662986219 := by
  unfold tailWord_3531560
  simp only [CollatzResearch.WordTrace]
  refine ⟨64403287542884368637244067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85871050057179158182992089 64403287542884368637244067)
  ·
    refine ⟨96604931314326552955866101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64403287542884368637244067 96604931314326552955866101)
    ·
      refine ⟨9056712310718114339612447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96604931314326552955866101 9056712310718114339612447)
      ·
        refine ⟨13585068466077171509418671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9056712310718114339612447 13585068466077171509418671)
        ·
          refine ⟨20377602699115757264128007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13585068466077171509418671 20377602699115757264128007)
          ·
            refine ⟨30566404048673635896192011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20377602699115757264128007 30566404048673635896192011)
            ·
              refine ⟨45849606073010453844288017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30566404048673635896192011 45849606073010453844288017)
              ·
                refine ⟨34387204554757840383216013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45849606073010453844288017 34387204554757840383216013)
                ·
                  refine ⟨12895201708034190143706005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34387204554757840383216013 12895201708034190143706005)
                  ·
                    refine ⟨604462580064102662986219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12895201708034190143706005 604462580064102662986219)
                    ·
                      rfl

theorem cell23_3531560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_3531560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531560 prefixEnd_3531560 := by exact prefixLift 3531560
  have htrace : WordTrace (prefixWord ++ tailWord_3531560) baseStart_3531560 baseEnd_3531560 := by
    simpa [prefixWord, tailWord_3531560, baseEnd_3531560] using wordTrace_append hprefix tailTrace_3531560
  have hstable : (prefixWord ++ tailWord_3531560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531560).length < 2 ^ (prefixWord ++ tailWord_3531560).sum := by decide
  have hdescent : baseEnd_3531560 < baseStart_3531560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531570 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5]
def baseStart_3531570 : Nat := 118140960795 + 3531570 * 2 ^ 59
def prefixEnd_3531570 : Nat := 4983230072969 + 3 ^ 40 * 3531570 * 2
def baseEnd_3531570 : Nat := 1813392874998852949833611

theorem tailTrace_3531570 : CollatzResearch.WordTrace tailWord_3531570 prefixEnd_3531570 1813392874998852949833611 := by
  unfold tailWord_3531570
  simp only [CollatzResearch.WordTrace]
  refine ⟨32201734953933127245588041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85871293210488339321568109 32201734953933127245588041)
  ·
    refine ⟨24151301215449845434191031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32201734953933127245588041 24151301215449845434191031)
    ·
      refine ⟨36226951823174768151286547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24151301215449845434191031 36226951823174768151286547)
      ·
        refine ⟨54340427734762152226929821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36226951823174768151286547 54340427734762152226929821)
        ·
          refine ⟨20377660400535807085098683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54340427734762152226929821 20377660400535807085098683)
          ·
            refine ⟨30566490600803710627648025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20377660400535807085098683 30566490600803710627648025)
            ·
              refine ⟨22924867950602782970736019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30566490600803710627648025 22924867950602782970736019)
              ·
                refine ⟨34387301925904174456104029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22924867950602782970736019 34387301925904174456104029)
                ·
                  refine ⟨12895238222214065421039011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34387301925904174456104029 12895238222214065421039011)
                  ·
                    refine ⟨19342857333321098131558517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12895238222214065421039011 19342857333321098131558517)
                    ·
                      refine ⟨1813392874998852949833611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19342857333321098131558517 1813392874998852949833611)
                      ·
                        rfl

theorem cell23_3531570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_3531570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531570 prefixEnd_3531570 := by exact prefixLift 3531570
  have htrace : WordTrace (prefixWord ++ tailWord_3531570) baseStart_3531570 baseEnd_3531570 := by
    simpa [prefixWord, tailWord_3531570, baseEnd_3531570] using wordTrace_append hprefix tailTrace_3531570
  have hstable : (prefixWord ++ tailWord_3531570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531570).length < 2 ^ (prefixWord ++ tailWord_3531570).sum := by decide
  have hdescent : baseEnd_3531570 < baseStart_3531570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531587 : List Nat := [1, 1, 1, 3, 1, 4, 2, 4, 1, 2, 3]
def baseStart_3531587 : Nat := 118140960795 + 3531587 * 2 ^ 59
def prefixEnd_3531587 : Nat := 4983230072969 + 3 ^ 40 * 3531587 * 2
def baseEnd_3531587 : Nat := 1813401604169979383321033

theorem tailTrace_3531587 : CollatzResearch.WordTrace tailWord_3531587 prefixEnd_3531587 1813401604169979383321033 := by
  unfold tailWord_3531587
  simp only [CollatzResearch.WordTrace]
  refine ⟨128807559856670920885721015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85871706571113947257147343 128807559856670920885721015)
  ·
    refine ⟨193211339785006381328581523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128807559856670920885721015 193211339785006381328581523)
    ·
      refine ⟨289817009677509571992872285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193211339785006381328581523 289817009677509571992872285)
      ·
        refine ⟨108681378629066089497327107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289817009677509571992872285 108681378629066089497327107)
        ·
          refine ⟨163022067943599134245990661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108681378629066089497327107 163022067943599134245990661)
          ·
            refine ⟨30566637739424837671123249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163022067943599134245990661 30566637739424837671123249)
            ·
              refine ⟨22924978304568628253342437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30566637739424837671123249 22924978304568628253342437)
              ·
                refine ⟨4298433432106617797501707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22924978304568628253342437 4298433432106617797501707)
                ·
                  refine ⟨6447650148159926696252561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4298433432106617797501707 6447650148159926696252561)
                  ·
                    refine ⟨4835737611119945022189421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6447650148159926696252561 4835737611119945022189421)
                    ·
                      refine ⟨1813401604169979383321033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4835737611119945022189421 1813401604169979383321033)
                      ·
                        rfl

theorem cell23_3531587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 2, 3].length) (baseStart_3531587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531587 prefixEnd_3531587 := by exact prefixLift 3531587
  have htrace : WordTrace (prefixWord ++ tailWord_3531587) baseStart_3531587 baseEnd_3531587 := by
    simpa [prefixWord, tailWord_3531587, baseEnd_3531587] using wordTrace_append hprefix tailTrace_3531587
  have hstable : (prefixWord ++ tailWord_3531587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531587).length < 2 ^ (prefixWord ++ tailWord_3531587).sum := by decide
  have hdescent : baseEnd_3531587 < baseStart_3531587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531601 : List Nat := [1, 2, 2, 1, 6, 2, 2, 1, 1, 1, 4]
def baseStart_3531601 : Nat := 118140960795 + 3531601 * 2 ^ 59
def prefixEnd_3531601 : Nat := 4983230072969 + 3 ^ 40 * 3531601 * 2
def baseEnd_3531601 : Nat := 1813408792899142328545969

theorem tailTrace_3531601 : CollatzResearch.WordTrace tailWord_3531601 prefixEnd_3531601 1813408792899142328545969 := by
  unfold tailWord_3531601
  simp only [CollatzResearch.WordTrace]
  refine ⟨128808070478620201276730657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85872046985746800851153771 128808070478620201276730657)
  ·
    refine ⟨96606052858965150957547993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128808070478620201276730657 96606052858965150957547993)
    ·
      refine ⟨72454539644223863218160995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96606052858965150957547993 72454539644223863218160995)
      ·
        refine ⟨108681809466335794827241493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72454539644223863218160995 108681809466335794827241493)
        ·
          refine ⟨5094459818734490382526945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 108681809466335794827241493 5094459818734490382526945)
          ·
            refine ⟨3820844864050867786895209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5094459818734490382526945 3820844864050867786895209)
            ·
              refine ⟨2865633648038150840171407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3820844864050867786895209 2865633648038150840171407)
              ·
                refine ⟨4298450472057226260257111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2865633648038150840171407 4298450472057226260257111)
                ·
                  refine ⟨6447675708085839390385667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4298450472057226260257111 6447675708085839390385667)
                  ·
                    refine ⟨9671513562128759085578501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6447675708085839390385667 9671513562128759085578501)
                    ·
                      refine ⟨1813408792899142328545969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9671513562128759085578501 1813408792899142328545969)
                      ·
                        rfl

theorem cell23_3531601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 1, 1, 4].length) (baseStart_3531601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531601 prefixEnd_3531601 := by exact prefixLift 3531601
  have htrace : WordTrace (prefixWord ++ tailWord_3531601) baseStart_3531601 baseEnd_3531601 := by
    simpa [prefixWord, tailWord_3531601, baseEnd_3531601] using wordTrace_append hprefix tailTrace_3531601
  have hstable : (prefixWord ++ tailWord_3531601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531601).length < 2 ^ (prefixWord ++ tailWord_3531601).sum := by decide
  have hdescent : baseEnd_3531601 < baseStart_3531601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531618 : List Nat := [3, 3, 2, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_3531618 : Nat := 118140960795 + 3531618 * 2 ^ 59
def prefixEnd_3531618 : Nat := 4983230072969 + 3 ^ 40 * 3531618 * 2
def baseEnd_3531618 : Nat := 1813417522070268762033391

theorem tailTrace_3531618 : CollatzResearch.WordTrace tailWord_3531618 prefixEnd_3531618 1813417522070268762033391 := by
  unfold tailWord_3531618
  simp only [CollatzResearch.WordTrace]
  refine ⟨32202172629889653295024877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85872460346372408786733005 32202172629889653295024877)
  ·
    refine ⟨12075814736208619985634329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32202172629889653295024877 12075814736208619985634329)
    ·
      refine ⟨9056861052156464989225747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12075814736208619985634329 9056861052156464989225747)
      ·
        refine ⟨13585291578234697483838621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9056861052156464989225747 13585291578234697483838621)
        ·
          refine ⟨5094484341838011556439483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13585291578234697483838621 5094484341838011556439483)
          ·
            refine ⟨7641726512757017334659225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5094484341838011556439483 7641726512757017334659225)
            ·
              refine ⟨5731294884567763000994419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7641726512757017334659225 5731294884567763000994419)
              ·
                refine ⟨8596942326851644501491629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5731294884567763000994419 8596942326851644501491629)
                ·
                  refine ⟨3223853372569366688059361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8596942326851644501491629 3223853372569366688059361)
                  ·
                    refine ⟨2417890029427025016044521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3223853372569366688059361 2417890029427025016044521)
                    ·
                      refine ⟨1813417522070268762033391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2417890029427025016044521 1813417522070268762033391)
                      ·
                        rfl

theorem cell23_3531618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_3531618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531618 prefixEnd_3531618 := by exact prefixLift 3531618
  have htrace : WordTrace (prefixWord ++ tailWord_3531618) baseStart_3531618 baseEnd_3531618 := by
    simpa [prefixWord, tailWord_3531618, baseEnd_3531618] using wordTrace_append hprefix tailTrace_3531618
  have hstable : (prefixWord ++ tailWord_3531618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531618).length < 2 ^ (prefixWord ++ tailWord_3531618).sum := by decide
  have hdescent : baseEnd_3531618 < baseStart_3531618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531627 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 5, 3, 2]
def baseStart_3531627 : Nat := 118140960795 + 3531627 * 2 ^ 59
def prefixEnd_3531627 : Nat := 4983230072969 + 3 ^ 40 * 3531627 * 2
def baseEnd_3531627 : Nat := 1813422143396159226820849

theorem tailTrace_3531627 : CollatzResearch.WordTrace tailWord_3531627 prefixEnd_3531627 1813422143396159226820849 := by
  unfold tailWord_3531627
  simp only [CollatzResearch.WordTrace]
  refine ⟨128809018776526007717177135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85872679184350671811451423 128809018776526007717177135)
  ·
    refine ⟨193213528164789011575765703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128809018776526007717177135 193213528164789011575765703)
    ·
      refine ⟨289820292247183517363648555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193213528164789011575765703 289820292247183517363648555)
      ·
        refine ⟨434730438370775276045472833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289820292247183517363648555 434730438370775276045472833)
        ·
          refine ⟨326047828778081457034104625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434730438370775276045472833 326047828778081457034104625)
          ·
            refine ⟨244535871583561092775578469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 326047828778081457034104625 244535871583561092775578469)
            ·
              refine ⟨45850475921917704895420963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244535871583561092775578469 45850475921917704895420963)
              ·
                refine ⟨68775713882876557343131445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45850475921917704895420963 68775713882876557343131445)
                ·
                  refine ⟨6447723176519677250918573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68775713882876557343131445 6447723176519677250918573)
                  ·
                    refine ⟨2417896191194878969094465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6447723176519677250918573 2417896191194878969094465)
                    ·
                      refine ⟨1813422143396159226820849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2417896191194878969094465 1813422143396159226820849)
                      ·
                        rfl

theorem cell23_3531627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 3, 2].length) (baseStart_3531627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531627 prefixEnd_3531627 := by exact prefixLift 3531627
  have htrace : WordTrace (prefixWord ++ tailWord_3531627) baseStart_3531627 baseEnd_3531627 := by
    simpa [prefixWord, tailWord_3531627, baseEnd_3531627] using wordTrace_append hprefix tailTrace_3531627
  have hstable : (prefixWord ++ tailWord_3531627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531627).length < 2 ^ (prefixWord ++ tailWord_3531627).sum := by decide
  have hdescent : baseEnd_3531627 < baseStart_3531627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531634 : List Nat := [3, 2, 1, 2, 1, 1, 2, 5, 2, 1, 3]
def baseStart_3531634 : Nat := 118140960795 + 3531634 * 2 ^ 59
def prefixEnd_3531634 : Nat := 4983230072969 + 3 ^ 40 * 3531634 * 2
def baseEnd_3531634 : Nat := 1813425737760740699433317

theorem tailTrace_3531634 : CollatzResearch.WordTrace tailWord_3531634 prefixEnd_3531634 1813425737760740699433317 := by
  unfold tailWord_3531634
  simp only [CollatzResearch.WordTrace]
  refine ⟨32202318521875161978170489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85872849391667098608454637 32202318521875161978170489)
  ·
    refine ⟨24151738891406371483627867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32202318521875161978170489 24151738891406371483627867)
    ·
      refine ⟨36227608337109557225441801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24151738891406371483627867 36227608337109557225441801)
      ·
        refine ⟨27170706252832167919081351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36227608337109557225441801 27170706252832167919081351)
        ·
          refine ⟨40756059379248251878622027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27170706252832167919081351 40756059379248251878622027)
          ·
            refine ⟨61134089068872377817933041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40756059379248251878622027 61134089068872377817933041)
            ·
              refine ⟨45850566801654283363449781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61134089068872377817933041 45850566801654283363449781)
              ·
                refine ⟨4298490637655089065323417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45850566801654283363449781 4298490637655089065323417)
                ·
                  refine ⟨3223867978241316798992563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4298490637655089065323417 3223867978241316798992563)
                  ·
                    refine ⟨4835801967361975198488845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3223867978241316798992563 4835801967361975198488845)
                    ·
                      refine ⟨1813425737760740699433317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4835801967361975198488845 1813425737760740699433317)
                      ·
                        rfl

theorem cell23_3531634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_3531634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531634 prefixEnd_3531634 := by exact prefixLift 3531634
  have htrace : WordTrace (prefixWord ++ tailWord_3531634) baseStart_3531634 baseEnd_3531634 := by
    simpa [prefixWord, tailWord_3531634, baseEnd_3531634] using wordTrace_append hprefix tailTrace_3531634
  have hstable : (prefixWord ++ tailWord_3531634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531634).length < 2 ^ (prefixWord ++ tailWord_3531634).sum := by decide
  have hdescent : baseEnd_3531634 < baseStart_3531634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531660 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 1, 3, 5]
def baseStart_3531660 : Nat := 118140960795 + 3531660 * 2 ^ 59
def prefixEnd_3531660 : Nat := 4983230072969 + 3 ^ 40 * 3531660 * 2
def baseEnd_3531660 : Nat := 1813439088257757597708197

theorem tailTrace_3531660 : CollatzResearch.WordTrace tailWord_3531660 prefixEnd_3531660 1813439088257757597708197 := by
  unfold tailWord_3531660
  simp only [CollatzResearch.WordTrace]
  refine ⟨64405111192703227176564217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85873481590270969568752289 64405111192703227176564217)
  ·
    refine ⟨48303833394527420382423163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64405111192703227176564217 48303833394527420382423163)
    ·
      refine ⟨72455750091791130573634745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48303833394527420382423163 72455750091791130573634745)
      ·
        refine ⟨54341812568843347930226059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72455750091791130573634745 54341812568843347930226059)
        ·
          refine ⟨81512718853265021895339089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54341812568843347930226059 81512718853265021895339089)
          ·
            refine ⟨61134539139948766421504317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81512718853265021895339089 61134539139948766421504317)
            ·
              refine ⟨22925452177480787408064119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61134539139948766421504317 22925452177480787408064119)
              ·
                refine ⟨34388178266221181112096179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22925452177480787408064119 34388178266221181112096179)
                ·
                  refine ⟨51582267399331771668144269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34388178266221181112096179 51582267399331771668144269)
                  ·
                    refine ⟨19343350274749414375554101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51582267399331771668144269 19343350274749414375554101)
                    ·
                      refine ⟨1813439088257757597708197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19343350274749414375554101 1813439088257757597708197)
                      ·
                        rfl

theorem cell23_3531660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_3531660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531660 prefixEnd_3531660 := by exact prefixLift 3531660
  have htrace : WordTrace (prefixWord ++ tailWord_3531660) baseStart_3531660 baseEnd_3531660 := by
    simpa [prefixWord, tailWord_3531660, baseEnd_3531660] using wordTrace_append hprefix tailTrace_3531660
  have hstable : (prefixWord ++ tailWord_3531660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531660).length < 2 ^ (prefixWord ++ tailWord_3531660).sum := by decide
  have hdescent : baseEnd_3531660 < baseStart_3531660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531677 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_3531677 : Nat := 118140960795 + 3531677 * 2 ^ 59
def prefixEnd_3531677 : Nat := 4983230072969 + 3 ^ 40 * 3531677 * 2
def baseEnd_3531677 : Nat := 1813447817428884031195619

theorem tailTrace_3531677 : CollatzResearch.WordTrace tailWord_3531677 prefixEnd_3531677 1813447817428884031195619 := by
  unfold tailWord_3531677
  simp only [CollatzResearch.WordTrace]
  refine ⟨128810842426344866256497285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85873894950896577504331523 128810842426344866256497285)
  ·
    refine ⟨24152032954939662423093241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128810842426344866256497285 24152032954939662423093241)
    ·
      refine ⟨18114024716204746817319931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24152032954939662423093241 18114024716204746817319931)
      ·
        refine ⟨27171037074307120225979897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18114024716204746817319931 27171037074307120225979897)
        ·
          refine ⟨20378277805730340169484923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27171037074307120225979897 20378277805730340169484923)
          ·
            refine ⟨30567416708595510254227385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20378277805730340169484923 30567416708595510254227385)
            ·
              refine ⟨22925562531446632690670539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30567416708595510254227385 22925562531446632690670539)
              ·
                refine ⟨34388343797169949036005809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22925562531446632690670539 34388343797169949036005809)
                ·
                  refine ⟨25791257847877461777004357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34388343797169949036005809 25791257847877461777004357)
                  ·
                    refine ⟨4835860846477024083188317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25791257847877461777004357 4835860846477024083188317)
                    ·
                      refine ⟨1813447817428884031195619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4835860846477024083188317 1813447817428884031195619)
                      ·
                        rfl

theorem cell23_3531677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_3531677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531677 prefixEnd_3531677 := by exact prefixLift 3531677
  have htrace : WordTrace (prefixWord ++ tailWord_3531677) baseStart_3531677 baseEnd_3531677 := by
    simpa [prefixWord, tailWord_3531677, baseEnd_3531677] using wordTrace_append hprefix tailTrace_3531677
  have hstable : (prefixWord ++ tailWord_3531677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531677).length < 2 ^ (prefixWord ++ tailWord_3531677).sum := by decide
  have hdescent : baseEnd_3531677 < baseStart_3531677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531727 : List Nat := [1, 1, 2, 1, 1, 6, 2, 2, 2, 5]
def baseStart_3531727 : Nat := 118140960795 + 3531727 * 2 ^ 59
def prefixEnd_3531727 : Nat := 4983230072969 + 3 ^ 40 * 3531727 * 2
def baseEnd_3531727 : Nat := 604491163820536278523463

theorem tailTrace_3531727 : CollatzResearch.WordTrace tailWord_3531727 prefixEnd_3531727 604491163820536278523463 := by
  unfold tailWord_3531727
  simp only [CollatzResearch.WordTrace]
  refine ⟨128812666076163724795817435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85875110717442483197211623 128812666076163724795817435)
  ·
    refine ⟨193218999114245587193726153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128812666076163724795817435 193218999114245587193726153)
    ·
      refine ⟨144914249335684190395294615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193218999114245587193726153 144914249335684190395294615)
      ·
        refine ⟨217371374003526285592941923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144914249335684190395294615 217371374003526285592941923)
        ·
          refine ⟨326057061005289428389412885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217371374003526285592941923 326057061005289428389412885)
          ·
            refine ⟨15283924734622941955753729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 326057061005289428389412885 15283924734622941955753729)
            ·
              refine ⟨11462943550967206466815297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15283924734622941955753729 11462943550967206466815297)
              ·
                refine ⟨8597207663225404850111473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11462943550967206466815297 8597207663225404850111473)
                ·
                  refine ⟨6447905747419053637583605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8597207663225404850111473 6447905747419053637583605)
                  ·
                    refine ⟨604491163820536278523463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6447905747419053637583605 604491163820536278523463)
                    ·
                      rfl

theorem cell23_3531727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 5].length) (baseStart_3531727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531727 prefixEnd_3531727 := by exact prefixLift 3531727
  have htrace : WordTrace (prefixWord ++ tailWord_3531727) baseStart_3531727 baseEnd_3531727 := by
    simpa [prefixWord, tailWord_3531727, baseEnd_3531727] using wordTrace_append hprefix tailTrace_3531727
  have hstable : (prefixWord ++ tailWord_3531727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531727).length < 2 ^ (prefixWord ++ tailWord_3531727).sum := by decide
  have hdescent : baseEnd_3531727 < baseStart_3531727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531737 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 1, 2, 5]
def baseStart_3531737 : Nat := 118140960795 + 3531737 * 2 ^ 59
def prefixEnd_3531737 : Nat := 4983230072969 + 3 ^ 40 * 3531737 * 2
def baseEnd_3531737 : Nat := 1813478626268153796445343

theorem tailTrace_3531737 : CollatzResearch.WordTrace tailWord_3531737 prefixEnd_3531737 1813478626268153796445343 := by
  unfold tailWord_3531737
  simp only [CollatzResearch.WordTrace]
  refine ⟨128813030806127496503681465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85875353870751664335787643 128813030806127496503681465)
  ·
    refine ⟨96609773104595622377761099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128813030806127496503681465 96609773104595622377761099)
    ·
      refine ⟨144914659656893433566641649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96609773104595622377761099 144914659656893433566641649)
      ·
        refine ⟨108685994742670075174981237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144914659656893433566641649 108685994742670075174981237)
        ·
          refine ⟨10189312007125319547654491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108685994742670075174981237 10189312007125319547654491)
          ·
            refine ⟨15283968010687979321481737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10189312007125319547654491 15283968010687979321481737)
            ·
              refine ⟨11462976008015984491111303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15283968010687979321481737 11462976008015984491111303)
              ·
                refine ⟨17194464012023976736666955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11462976008015984491111303 17194464012023976736666955)
                ·
                  refine ⟨25791696018035965105000433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17194464012023976736666955 25791696018035965105000433)
                  ·
                    refine ⟨19343772013526973828750325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25791696018035965105000433 19343772013526973828750325)
                    ·
                      refine ⟨1813478626268153796445343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19343772013526973828750325 1813478626268153796445343)
                      ·
                        rfl

theorem cell23_3531737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_3531737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531737 prefixEnd_3531737 := by exact prefixLift 3531737
  have htrace : WordTrace (prefixWord ++ tailWord_3531737) baseStart_3531737 baseEnd_3531737 := by
    simpa [prefixWord, tailWord_3531737, baseEnd_3531737] using wordTrace_append hprefix tailTrace_3531737
  have hstable : (prefixWord ++ tailWord_3531737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531737).length < 2 ^ (prefixWord ++ tailWord_3531737).sum := by decide
  have hdescent : baseEnd_3531737 < baseStart_3531737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531747 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 4]
def baseStart_3531747 : Nat := 118140960795 + 3531747 * 2 ^ 59
def prefixEnd_3531747 : Nat := 4983230072969 + 3 ^ 40 * 3531747 * 2
def baseEnd_3531747 : Nat := 1813483761074698757320297

theorem tailTrace_3531747 : CollatzResearch.WordTrace tailWord_3531747 prefixEnd_3531747 1813483761074698757320297 := by
  unfold tailWord_3531747
  simp only [CollatzResearch.WordTrace]
  refine ⟨128813395536091268211545495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85875597024060845474363663 128813395536091268211545495)
  ·
    refine ⟨193220093304136902317318243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128813395536091268211545495 193220093304136902317318243)
    ·
      refine ⟨289830139956205353475977365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193220093304136902317318243 289830139956205353475977365)
      ·
        refine ⟨13585787810447125944186439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 289830139956205353475977365 13585787810447125944186439)
        ·
          refine ⟨20378681715670688916279659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13585787810447125944186439 20378681715670688916279659)
          ·
            refine ⟨30568022573506033374419489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20378681715670688916279659 30568022573506033374419489)
            ·
              refine ⟨22926016930129525030814617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30568022573506033374419489 22926016930129525030814617)
              ·
                refine ⟨17194512697597143773110963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22926016930129525030814617 17194512697597143773110963)
                ·
                  refine ⟨25791769046395715659666445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17194512697597143773110963 25791769046395715659666445)
                  ·
                    refine ⟨9671913392398393372374917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25791769046395715659666445 9671913392398393372374917)
                    ·
                      refine ⟨1813483761074698757320297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9671913392398393372374917 1813483761074698757320297)
                      ·
                        rfl

theorem cell23_3531747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_3531747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531747 prefixEnd_3531747 := by exact prefixLift 3531747
  have htrace : WordTrace (prefixWord ++ tailWord_3531747) baseStart_3531747 baseEnd_3531747 := by
    simpa [prefixWord, tailWord_3531747, baseEnd_3531747] using wordTrace_append hprefix tailTrace_3531747
  have hstable : (prefixWord ++ tailWord_3531747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531747).length < 2 ^ (prefixWord ++ tailWord_3531747).sum := by decide
  have hdescent : baseEnd_3531747 < baseStart_3531747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531777 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_3531777 : Nat := 118140960795 + 3531777 * 2 ^ 59
def prefixEnd_3531777 : Nat := 4983230072969 + 3 ^ 40 * 3531777 * 2
def baseEnd_3531777 : Nat := 1813499165494333639945159

theorem tailTrace_3531777 : CollatzResearch.WordTrace tailWord_3531777 prefixEnd_3531777 1813499165494333639945159 := by
  unfold tailWord_3531777
  simp only [CollatzResearch.WordTrace]
  refine ⟨128814489725982583335137585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85876326483988388890091723 128814489725982583335137585)
  ·
    refine ⟨96610867294486937501353189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128814489725982583335137585 96610867294486937501353189)
    ·
      refine ⟨18114537617716300781503723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96610867294486937501353189 18114537617716300781503723)
      ·
        refine ⟨27171806426574451172255585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18114537617716300781503723 27171806426574451172255585)
        ·
          refine ⟨20378854819930838379191689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27171806426574451172255585 20378854819930838379191689)
          ·
            refine ⟨15284141114948128784393767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20378854819930838379191689 15284141114948128784393767)
            ·
              refine ⟨22926211672422193176590651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15284141114948128784393767 22926211672422193176590651)
              ·
                refine ⟨34389317508633289764885977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22926211672422193176590651 34389317508633289764885977)
                ·
                  refine ⟨25791988131474967323664483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34389317508633289764885977 25791988131474967323664483)
                  ·
                    refine ⟨38687982197212450985496725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25791988131474967323664483 38687982197212450985496725)
                    ·
                      refine ⟨1813499165494333639945159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38687982197212450985496725 1813499165494333639945159)
                      ·
                        rfl

theorem cell23_3531777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_3531777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531777 prefixEnd_3531777 := by exact prefixLift 3531777
  have htrace : WordTrace (prefixWord ++ tailWord_3531777) baseStart_3531777 baseEnd_3531777 := by
    simpa [prefixWord, tailWord_3531777, baseEnd_3531777] using wordTrace_append hprefix tailTrace_3531777
  have hstable : (prefixWord ++ tailWord_3531777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531777).length < 2 ^ (prefixWord ++ tailWord_3531777).sum := by decide
  have hdescent : baseEnd_3531777 < baseStart_3531777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531787 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 8]
def baseStart_3531787 : Nat := 118140960795 + 3531787 * 2 ^ 59
def prefixEnd_3531787 : Nat := 4983230072969 + 3 ^ 40 * 3531787 * 2
def baseEnd_3531787 : Nat := 201500477811208733424457

theorem tailTrace_3531787 : CollatzResearch.WordTrace tailWord_3531787 prefixEnd_3531787 201500477811208733424457 := by
  unfold tailWord_3531787
  simp only [CollatzResearch.WordTrace]
  refine ⟨128814854455946355043001615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85876569637297570028667743 128814854455946355043001615)
  ·
    refine ⟨193222281683919532564502423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128814854455946355043001615 193222281683919532564502423)
    ·
      refine ⟨289833422525879298846753635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193222281683919532564502423 289833422525879298846753635)
      ·
        refine ⟨434750133788818948270130453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289833422525879298846753635 434750133788818948270130453)
        ·
          refine ⟨20378912521350888200162365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 434750133788818948270130453 20378912521350888200162365)
          ·
            refine ⟨7642092195506583075060887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20378912521350888200162365 7642092195506583075060887)
            ·
              refine ⟨11463138293259874612591331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7642092195506583075060887 11463138293259874612591331)
              ·
                refine ⟨17194707439889811918886997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11463138293259874612591331 17194707439889811918886997)
                ·
                  refine ⟨201500477811208733424457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17194707439889811918886997 201500477811208733424457)
                  ·
                    rfl

theorem cell23_3531787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 8].length) (baseStart_3531787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531787 prefixEnd_3531787 := by exact prefixLift 3531787
  have htrace : WordTrace (prefixWord ++ tailWord_3531787) baseStart_3531787 baseEnd_3531787 := by
    simpa [prefixWord, tailWord_3531787, baseEnd_3531787] using wordTrace_append hprefix tailTrace_3531787
  have hstable : (prefixWord ++ tailWord_3531787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531787).length < 2 ^ (prefixWord ++ tailWord_3531787).sum := by decide
  have hdescent : baseEnd_3531787 < baseStart_3531787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531824 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 1, 5, 2]
def baseStart_3531824 : Nat := 118140960795 + 3531824 * 2 ^ 59
def prefixEnd_3531824 : Nat := 4983230072969 + 3 ^ 40 * 3531824 * 2
def baseEnd_3531824 : Nat := 1813523299085094956057443

theorem tailTrace_3531824 : CollatzResearch.WordTrace tailWord_3531824 prefixEnd_3531824 1813523299085094956057443 := by
  unfold tailWord_3531824
  simp only [CollatzResearch.WordTrace]
  refine ⟨64408101978406155181049263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85877469304541540241399017 64408101978406155181049263)
  ·
    refine ⟨96612152967609232771573895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64408101978406155181049263 96612152967609232771573895)
    ·
      refine ⟨144918229451413849157360843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96612152967609232771573895 144918229451413849157360843)
      ·
        refine ⟨217377344177120773736041265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144918229451413849157360843 217377344177120773736041265)
        ·
          refine ⟨163033008132840580302030949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217377344177120773736041265 163033008132840580302030949)
          ·
            refine ⟨30568689024907608806630803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163033008132840580302030949 30568689024907608806630803)
            ·
              refine ⟨45853033537361413209946205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30568689024907608806630803 45853033537361413209946205)
              ·
                refine ⟨17194887576510529953729827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45853033537361413209946205 17194887576510529953729827)
                ·
                  refine ⟨25792331364765794930594741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17194887576510529953729827 25792331364765794930594741)
                  ·
                    refine ⟨2418031065446793274743257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25792331364765794930594741 2418031065446793274743257)
                    ·
                      refine ⟨1813523299085094956057443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2418031065446793274743257 1813523299085094956057443)
                      ·
                        rfl

theorem cell23_3531824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 1, 5, 2].length) (baseStart_3531824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531824 prefixEnd_3531824 := by exact prefixLift 3531824
  have htrace : WordTrace (prefixWord ++ tailWord_3531824) baseStart_3531824 baseEnd_3531824 := by
    simpa [prefixWord, tailWord_3531824, baseEnd_3531824] using wordTrace_append hprefix tailTrace_3531824
  have hstable : (prefixWord ++ tailWord_3531824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531824).length < 2 ^ (prefixWord ++ tailWord_3531824).sum := by decide
  have hdescent : baseEnd_3531824 < baseStart_3531824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531834 : List Nat := [3, 1, 1, 1, 3, 1, 4, 3, 1, 5]
def baseStart_3531834 : Nat := 118140960795 + 3531834 * 2 ^ 59
def prefixEnd_3531834 : Nat := 4983230072969 + 3 ^ 40 * 3531834 * 2
def baseEnd_3531834 : Nat := 604509477963879972310799

theorem tailTrace_3531834 : CollatzResearch.WordTrace tailWord_3531834 prefixEnd_3531834 604509477963879972310799 := by
  unfold tailWord_3531834
  simp only [CollatzResearch.WordTrace]
  refine ⟨32204142171694020517490639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85877712457850721379975037 32204142171694020517490639)
  ·
    refine ⟨48306213257541030776235959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32204142171694020517490639 48306213257541030776235959)
    ·
      refine ⟨72459319886311546164353939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48306213257541030776235959 72459319886311546164353939)
      ·
        refine ⟨108688979829467319246530909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72459319886311546164353939 108688979829467319246530909)
        ·
          refine ⟨40758367436050244717449091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108688979829467319246530909 40758367436050244717449091)
          ·
            refine ⟨61137551154075367076173637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40758367436050244717449091 61137551154075367076173637)
            ·
              refine ⟨11463290841389131326782557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61137551154075367076173637 11463290841389131326782557)
              ·
                refine ⟨4298734065520924247543459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11463290841389131326782557 4298734065520924247543459)
                ·
                  refine ⟨6448101098281386371315189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4298734065520924247543459 6448101098281386371315189)
                  ·
                    refine ⟨604509477963879972310799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6448101098281386371315189 604509477963879972310799)
                    ·
                      rfl

theorem cell23_3531834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_3531834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531834 prefixEnd_3531834 := by exact prefixLift 3531834
  have htrace : WordTrace (prefixWord ++ tailWord_3531834) baseStart_3531834 baseEnd_3531834 := by
    simpa [prefixWord, tailWord_3531834, baseEnd_3531834] using wordTrace_append hprefix tailTrace_3531834
  have hstable : (prefixWord ++ tailWord_3531834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531834).length < 2 ^ (prefixWord ++ tailWord_3531834).sum := by decide
  have hdescent : baseEnd_3531834 < baseStart_3531834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531854 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_3531854 : Nat := 118140960795 + 3531854 * 2 ^ 59
def prefixEnd_3531854 : Nat := 4983230072969 + 3 ^ 40 * 3531854 * 2
def baseEnd_3531854 : Nat := 1813538703504729838682305

theorem tailTrace_3531854 : CollatzResearch.WordTrace tailWord_3531854 prefixEnd_3531854 1813538703504729838682305 := by
  unfold tailWord_3531854
  simp only [CollatzResearch.WordTrace]
  refine ⟨16102162268337953185711327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85878198764469083657127077 16102162268337953185711327)
  ·
    refine ⟨24153243402506929778566991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16102162268337953185711327 24153243402506929778566991)
    ·
      refine ⟨36229865103760394667850487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24153243402506929778566991 36229865103760394667850487)
      ·
        refine ⟨54344797655640592001775731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36229865103760394667850487 54344797655640592001775731)
        ·
          refine ⟨81517196483460888002663597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54344797655640592001775731 81517196483460888002663597)
          ·
            refine ⟨30568948681297833000998849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81517196483460888002663597 30568948681297833000998849)
            ·
              refine ⟨22926711510973374750749137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30568948681297833000998849 22926711510973374750749137)
              ·
                refine ⟨17195033633230031063061853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22926711510973374750749137 17195033633230031063061853)
                ·
                  refine ⟨6448137612461261648648195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17195033633230031063061853 6448137612461261648648195)
                  ·
                    refine ⟨9672206418691892472972293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6448137612461261648648195 9672206418691892472972293)
                    ·
                      refine ⟨1813538703504729838682305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9672206418691892472972293 1813538703504729838682305)
                      ·
                        rfl

theorem cell23_3531854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_3531854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531854 prefixEnd_3531854 := by exact prefixLift 3531854
  have htrace : WordTrace (prefixWord ++ tailWord_3531854) baseStart_3531854 baseEnd_3531854 := by
    simpa [prefixWord, tailWord_3531854, baseEnd_3531854] using wordTrace_append hprefix tailTrace_3531854
  have hstable : (prefixWord ++ tailWord_3531854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531854).length < 2 ^ (prefixWord ++ tailWord_3531854).sum := by decide
  have hdescent : baseEnd_3531854 < baseStart_3531854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531871 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 5, 2, 2]
def baseStart_3531871 : Nat := 118140960795 + 3531871 * 2 ^ 59
def prefixEnd_3531871 : Nat := 4983230072969 + 3 ^ 40 * 3531871 * 2
def baseEnd_3531871 : Nat := 1813547432675856272169727

theorem tailTrace_3531871 : CollatzResearch.WordTrace tailWord_3531871 prefixEnd_3531871 1813547432675856272169727 := by
  unfold tailWord_3531871
  simp only [CollatzResearch.WordTrace]
  refine ⟨128817918187642037389059467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85878612125094691592706311 128817918187642037389059467)
  ·
    refine ⟨193226877281463056083589201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128817918187642037389059467 193226877281463056083589201)
    ·
      refine ⟨144920157961097292062691901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193226877281463056083589201 144920157961097292062691901)
      ·
        refine ⟨54345059235411484523509463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144920157961097292062691901 54345059235411484523509463)
        ·
          refine ⟨81517588853117226785264195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54345059235411484523509463 81517588853117226785264195)
          ·
            refine ⟨122276383279675840177896293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81517588853117226785264195 122276383279675840177896293)
            ·
              refine ⟨22926821864939220033355555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122276383279675840177896293 22926821864939220033355555)
              ·
                refine ⟨34390232797408830050033333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22926821864939220033355555 34390232797408830050033333)
                ·
                  refine ⟨3224084324757077817190625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34390232797408830050033333 3224084324757077817190625)
                  ·
                    refine ⟨2418063243567808362892969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3224084324757077817190625 2418063243567808362892969)
                    ·
                      refine ⟨1813547432675856272169727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2418063243567808362892969 1813547432675856272169727)
                      ·
                        rfl

theorem cell23_3531871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_3531871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531871 prefixEnd_3531871 := by exact prefixLift 3531871
  have htrace : WordTrace (prefixWord ++ tailWord_3531871) baseStart_3531871 baseEnd_3531871 := by
    simpa [prefixWord, tailWord_3531871, baseEnd_3531871] using wordTrace_append hprefix tailTrace_3531871
  have hstable : (prefixWord ++ tailWord_3531871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531871).length < 2 ^ (prefixWord ++ tailWord_3531871).sum := by decide
  have hdescent : baseEnd_3531871 < baseStart_3531871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531877 : List Nat := [1, 3, 1, 3, 2, 1, 1, 11]
def baseStart_3531877 : Nat := 118140960795 + 3531877 * 2 ^ 59
def prefixEnd_3531877 : Nat := 4983230072969 + 3 ^ 40 * 3531877 * 2
def baseEnd_3531877 : Nat := 67168537539251231433137

theorem tailTrace_3531877 : CollatzResearch.WordTrace tailWord_3531877 prefixEnd_3531877 67168537539251231433137 := by
  unfold tailWord_3531877
  simp only [CollatzResearch.WordTrace]
  refine ⟨128818137025620300413777885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85878758017080200275851923 128818137025620300413777885)
  ·
    refine ⟨48306801384607612655166707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128818137025620300413777885 48306801384607612655166707)
    ·
      refine ⟨72460202076911418982750061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48306801384607612655166707 72460202076911418982750061)
      ·
        refine ⟨27172575778841782118531273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72460202076911418982750061 27172575778841782118531273)
        ·
          refine ⟨20379431834131336588898455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27172575778841782118531273 20379431834131336588898455)
          ·
            refine ⟨30569147751197004883347683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20379431834131336588898455 30569147751197004883347683)
            ·
              refine ⟨45853721626795507325021525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30569147751197004883347683 45853721626795507325021525)
              ·
                refine ⟨67168537539251231433137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 45853721626795507325021525 67168537539251231433137)
                ·
                  rfl

theorem cell23_3531877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 11].length) (baseStart_3531877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531877 prefixEnd_3531877 := by exact prefixLift 3531877
  have htrace : WordTrace (prefixWord ++ tailWord_3531877) baseStart_3531877 baseEnd_3531877 := by
    simpa [prefixWord, tailWord_3531877, baseEnd_3531877] using wordTrace_append hprefix tailTrace_3531877
  have hstable : (prefixWord ++ tailWord_3531877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531877).length < 2 ^ (prefixWord ++ tailWord_3531877).sum := by decide
  have hdescent : baseEnd_3531877 < baseStart_3531877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531884 : List Nat := [2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 4]
def baseStart_3531884 : Nat := 118140960795 + 3531884 * 2 ^ 59
def prefixEnd_3531884 : Nat := 4983230072969 + 3 ^ 40 * 3531884 * 2
def baseEnd_3531884 : Nat := 1813554107924364721307167

theorem tailTrace_3531884 : CollatzResearch.WordTrace tailWord_3531884 prefixEnd_3531884 1813554107924364721307167 := by
  unfold tailWord_3531884
  simp only [CollatzResearch.WordTrace]
  refine ⟨64409196168297470304641353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85878928224396627072855137 64409196168297470304641353)
  ·
    refine ⟨48306897126223102728481015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64409196168297470304641353 48306897126223102728481015)
    ·
      refine ⟨72460345689334654092721523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48306897126223102728481015 72460345689334654092721523)
      ·
        refine ⟨108690518534001981139082285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72460345689334654092721523 108690518534001981139082285)
        ·
          refine ⟨40758944450250742927155857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108690518534001981139082285 40758944450250742927155857)
          ·
            refine ⟨30569208337688057195366893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40758944450250742927155857 30569208337688057195366893)
            ·
              refine ⟨11463453126633021448262585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30569208337688057195366893 11463453126633021448262585)
              ·
                refine ⟨8597589844974766086196939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11463453126633021448262585 8597589844974766086196939)
                ·
                  refine ⟨12896384767462149129295409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8597589844974766086196939 12896384767462149129295409)
                  ·
                    refine ⟨9672288575596611846971557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12896384767462149129295409 9672288575596611846971557)
                    ·
                      refine ⟨1813554107924364721307167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9672288575596611846971557 1813554107924364721307167)
                      ·
                        rfl

theorem cell23_3531884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_3531884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531884 prefixEnd_3531884 := by exact prefixLift 3531884
  have htrace : WordTrace (prefixWord ++ tailWord_3531884) baseStart_3531884 baseEnd_3531884 := by
    simpa [prefixWord, tailWord_3531884, baseEnd_3531884] using wordTrace_append hprefix tailTrace_3531884
  have hstable : (prefixWord ++ tailWord_3531884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531884).length < 2 ^ (prefixWord ++ tailWord_3531884).sum := by decide
  have hdescent : baseEnd_3531884 < baseStart_3531884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531907 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 1, 9]
def baseStart_3531907 : Nat := 118140960795 + 3531907 * 2 ^ 59
def prefixEnd_3531907 : Nat := 4983230072969 + 3 ^ 40 * 3531907 * 2
def baseEnd_3531907 : Nat := 604521972659806043773187

theorem tailTrace_3531907 : CollatzResearch.WordTrace tailWord_3531907 prefixEnd_3531907 604521972659806043773187 := by
  unfold tailWord_3531907
  simp only [CollatzResearch.WordTrace]
  refine ⟨128819231215511615537369975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85879487477007743691579983 128819231215511615537369975)
  ·
    refine ⟨193228846823267423306054963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128819231215511615537369975 193228846823267423306054963)
    ·
      refine ⟨289843270234901134959082445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193228846823267423306054963 289843270234901134959082445)
      ·
        refine ⟨108691226338087925609655917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 289843270234901134959082445 108691226338087925609655917)
        ·
          refine ⟨40759209876782972103620969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108691226338087925609655917 40759209876782972103620969)
          ·
            refine ⟨30569407407587229077715727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40759209876782972103620969 30569407407587229077715727)
            ·
              refine ⟨45854111111380843616573591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30569407407587229077715727 45854111111380843616573591)
              ·
                refine ⟨68781166667071265424860387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45854111111380843616573591 68781166667071265424860387)
                ·
                  refine ⟨103171750000606898137290581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68781166667071265424860387 103171750000606898137290581)
                  ·
                    refine ⟨604521972659806043773187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 103171750000606898137290581 604521972659806043773187)
                    ·
                      rfl

theorem cell23_3531907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 9].length) (baseStart_3531907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531907 prefixEnd_3531907 := by exact prefixLift 3531907
  have htrace : WordTrace (prefixWord ++ tailWord_3531907) baseStart_3531907 baseEnd_3531907 := by
    simpa [prefixWord, tailWord_3531907, baseEnd_3531907] using wordTrace_append hprefix tailTrace_3531907
  have hstable : (prefixWord ++ tailWord_3531907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531907).length < 2 ^ (prefixWord ++ tailWord_3531907).sum := by decide
  have hdescent : baseEnd_3531907 < baseStart_3531907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531954 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 2, 6]
def baseStart_3531954 : Nat := 118140960795 + 3531954 * 2 ^ 59
def prefixEnd_3531954 : Nat := 4983230072969 + 3 ^ 40 * 3531954 * 2
def baseEnd_3531954 : Nat := 604530017190059815810615

theorem tailTrace_3531954 : CollatzResearch.WordTrace tailWord_3531954 prefixEnd_3531954 604530017190059815810615 := by
  unfold tailWord_3531954
  simp only [CollatzResearch.WordTrace]
  refine ⟨32205236361585335641082729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85880630297560895042887277 32205236361585335641082729)
  ·
    refine ⟨24153927271189001730812047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32205236361585335641082729 24153927271189001730812047)
    ·
      refine ⟨36230890906783502596218071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24153927271189001730812047 36230890906783502596218071)
      ·
        refine ⟨54346336360175253894327107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36230890906783502596218071 54346336360175253894327107)
        ·
          refine ⟨81519504540262880841490661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54346336360175253894327107 81519504540262880841490661)
          ·
            refine ⟨15284907101299290157779499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81519504540262880841490661 15284907101299290157779499)
            ·
              refine ⟨22927360651948935236669249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15284907101299290157779499 22927360651948935236669249)
              ·
                refine ⟨17195520488961701427501937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22927360651948935236669249 17195520488961701427501937)
                ·
                  refine ⟨12896640366721276070626453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17195520488961701427501937 12896640366721276070626453)
                  ·
                    refine ⟨604530017190059815810615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12896640366721276070626453 604530017190059815810615)
                    ·
                      rfl

theorem cell23_3531954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_3531954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531954 prefixEnd_3531954 := by exact prefixLift 3531954
  have htrace : WordTrace (prefixWord ++ tailWord_3531954) baseStart_3531954 baseEnd_3531954 := by
    simpa [prefixWord, tailWord_3531954, baseEnd_3531954] using wordTrace_append hprefix tailTrace_3531954
  have hstable : (prefixWord ++ tailWord_3531954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531954).length < 2 ^ (prefixWord ++ tailWord_3531954).sum := by decide
  have hdescent : baseEnd_3531954 < baseStart_3531954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531972 : List Nat := [2, 3, 3, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_3531972 : Nat := 118140960795 + 3531972 * 2 ^ 59
def prefixEnd_3531972 : Nat := 4983230072969 + 3 ^ 40 * 3531972 * 2
def baseEnd_3531972 : Nat := 1813599294221960377006763

theorem tailTrace_3531972 : CollatzResearch.WordTrace tailWord_3531972 prefixEnd_3531972 1813599294221960377006763 := by
  unfold tailWord_3531972
  simp only [CollatzResearch.WordTrace]
  refine ⟨64410800980138065819243085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85881067973517421092324113 64410800980138065819243085)
  ·
    refine ⟨24154050367551774682216157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64410800980138065819243085 24154050367551774682216157)
    ·
      refine ⟨9057768887831915505831059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24154050367551774682216157 9057768887831915505831059)
      ·
        refine ⟨13586653331747873258746589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9057768887831915505831059 13586653331747873258746589)
        ·
          refine ⟨5094994999405452472029971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13586653331747873258746589 5094994999405452472029971)
          ·
            refine ⟨7642492499108178708044957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5094994999405452472029971 7642492499108178708044957)
            ·
              refine ⟨2865934687165567015516859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7642492499108178708044957 2865934687165567015516859)
              ·
                refine ⟨4298902030748350523275289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2865934687165567015516859 4298902030748350523275289)
                ·
                  refine ⟨3224176523061262892456467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4298902030748350523275289 3224176523061262892456467)
                  ·
                    refine ⟨4836264784591894338684701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3224176523061262892456467 4836264784591894338684701)
                    ·
                      refine ⟨1813599294221960377006763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4836264784591894338684701 1813599294221960377006763)
                      ·
                        rfl

theorem cell23_3531972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_3531972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531972 prefixEnd_3531972 := by exact prefixLift 3531972
  have htrace : WordTrace (prefixWord ++ tailWord_3531972) baseStart_3531972 baseEnd_3531972 := by
    simpa [prefixWord, tailWord_3531972, baseEnd_3531972] using wordTrace_append hprefix tailTrace_3531972
  have hstable : (prefixWord ++ tailWord_3531972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531972).length < 2 ^ (prefixWord ++ tailWord_3531972).sum := by decide
  have hdescent : baseEnd_3531972 < baseStart_3531972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3531978 : List Nat := [3, 1, 2, 1, 3, 2, 3, 1, 1, 4, 2]
def baseStart_3531978 : Nat := 118140960795 + 3531978 * 2 ^ 59
def prefixEnd_3531978 : Nat := 4983230072969 + 3 ^ 40 * 3531978 * 2
def baseEnd_3531978 : Nat := 1813602375105887353531735

theorem tailTrace_3531978 : CollatzResearch.WordTrace tailWord_3531978 prefixEnd_3531978 1813602375105887353531735 := by
  unfold tailWord_3531978
  simp only [CollatzResearch.WordTrace]
  refine ⟨32205455199563598665801147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85881213865502929775469725 32205455199563598665801147)
  ·
    refine ⟨48308182799345397998701721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32205455199563598665801147 48308182799345397998701721)
    ·
      refine ⟨36231137099509048499026291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48308182799345397998701721 36231137099509048499026291)
      ·
        refine ⟨54346705649263572748539437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36231137099509048499026291 54346705649263572748539437)
        ·
          refine ⟨20380014618473839780702289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54346705649263572748539437 20380014618473839780702289)
          ·
            refine ⟨15285010963855379835526717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20380014618473839780702289 15285010963855379835526717)
            ·
              refine ⟨5731879111445767438322519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15285010963855379835526717 5731879111445767438322519)
              ·
                refine ⟨8597818667168651157483779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5731879111445767438322519 8597818667168651157483779)
                ·
                  refine ⟨12896728000752976736225669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8597818667168651157483779 12896728000752976736225669)
                  ·
                    refine ⟨2418136500141183138042313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12896728000752976736225669 2418136500141183138042313)
                    ·
                      refine ⟨1813602375105887353531735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2418136500141183138042313 1813602375105887353531735)
                      ·
                        rfl

theorem cell23_3531978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_3531978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3531978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3531978 prefixEnd_3531978 := by exact prefixLift 3531978
  have htrace : WordTrace (prefixWord ++ tailWord_3531978) baseStart_3531978 baseEnd_3531978 := by
    simpa [prefixWord, tailWord_3531978, baseEnd_3531978] using wordTrace_append hprefix tailTrace_3531978
  have hstable : (prefixWord ++ tailWord_3531978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3531978).length < 2 ^ (prefixWord ++ tailWord_3531978).sum := by decide
  have hdescent : baseEnd_3531978 < baseStart_3531978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3531978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532018 : List Nat := [3, 2, 1, 3, 3, 2, 1, 1, 7]
def baseStart_3532018 : Nat := 118140960795 + 3532018 * 2 ^ 59
def prefixEnd_3532018 : Nat := 4983230072969 + 3 ^ 40 * 3532018 * 2
def baseEnd_3532018 : Nat := 201513657148007466336839

theorem tailTrace_3532018 : CollatzResearch.WordTrace tailWord_3532018 prefixEnd_3532018 201513657148007466336839 := by
  unfold tailWord_3532018
  simp only [CollatzResearch.WordTrace]
  refine ⟨32205819929527370373665177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85882186478739654329773805 32205819929527370373665177)
  ·
    refine ⟨24154364947145527780248883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32205819929527370373665177 24154364947145527780248883)
    ·
      refine ⟨36231547420718291670373325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24154364947145527780248883 36231547420718291670373325)
      ·
        refine ⟨13586830282769359376389997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36231547420718291670373325 13586830282769359376389997)
        ·
          refine ⟨5095061356038509766146249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13586830282769359376389997 5095061356038509766146249)
          ·
            refine ⟨3821296017028882324609687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5095061356038509766146249 3821296017028882324609687)
            ·
              refine ⟨5731944025543323486914531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3821296017028882324609687 5731944025543323486914531)
              ·
                refine ⟨8597916038314985230371797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5731944025543323486914531 8597916038314985230371797)
                ·
                  refine ⟨201513657148007466336839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8597916038314985230371797 201513657148007466336839)
                  ·
                    rfl

theorem cell23_3532018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_3532018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532018 prefixEnd_3532018 := by exact prefixLift 3532018
  have htrace : WordTrace (prefixWord ++ tailWord_3532018) baseStart_3532018 baseEnd_3532018 := by
    simpa [prefixWord, tailWord_3532018, baseEnd_3532018] using wordTrace_append hprefix tailTrace_3532018
  have hstable : (prefixWord ++ tailWord_3532018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532018).length < 2 ^ (prefixWord ++ tailWord_3532018).sum := by decide
  have hdescent : baseEnd_3532018 < baseStart_3532018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532051 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 6, 4, 2]
def baseStart_3532051 : Nat := 118140960795 + 3532051 * 2 ^ 59
def prefixEnd_3532051 : Nat := 4983230072969 + 3 ^ 40 * 3532051 * 2
def baseEnd_3532051 : Nat := 1813639859193665567918899

theorem tailTrace_3532051 : CollatzResearch.WordTrace tailWord_3532051 prefixEnd_3532051 1813639859193665567918899 := by
  unfold tailWord_3532051
  simp only [CollatzResearch.WordTrace]
  refine ⟨128824483326989928130612007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85882988884659952087074671 128824483326989928130612007)
  ·
    refine ⟨193236724990484892195918011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128824483326989928130612007 193236724990484892195918011)
    ·
      refine ⟨289855087485727338293877017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193236724990484892195918011 289855087485727338293877017)
      ·
        refine ⟨217391315614295503720407763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289855087485727338293877017 217391315614295503720407763)
        ·
          refine ⟨326086973421443255580611645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217391315614295503720407763 326086973421443255580611645)
          ·
            refine ⟨122282615033041220842729367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326086973421443255580611645 122282615033041220842729367)
            ·
              refine ⟨183423922549561831264094051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 122282615033041220842729367 183423922549561831264094051)
              ·
                refine ⟨275135883824342746896141077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183423922549561831264094051 275135883824342746896141077)
                ·
                  refine ⟨12896994554266066260756613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 275135883824342746896141077 12896994554266066260756613)
                  ·
                    refine ⟨2418186478924887423891865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12896994554266066260756613 2418186478924887423891865)
                    ·
                      refine ⟨1813639859193665567918899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2418186478924887423891865 1813639859193665567918899)
                      ·
                        rfl

theorem cell23_3532051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 4, 2].length) (baseStart_3532051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532051 prefixEnd_3532051 := by exact prefixLift 3532051
  have htrace : WordTrace (prefixWord ++ tailWord_3532051) baseStart_3532051 baseEnd_3532051 := by
    simpa [prefixWord, tailWord_3532051, baseEnd_3532051] using wordTrace_append hprefix tailTrace_3532051
  have hstable : (prefixWord ++ tailWord_3532051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532051).length < 2 ^ (prefixWord ++ tailWord_3532051).sum := by decide
  have hdescent : baseEnd_3532051 < baseStart_3532051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532068 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 2, 4, 2]
def baseStart_3532068 : Nat := 118140960795 + 3532068 * 2 ^ 59
def prefixEnd_3532068 : Nat := 4983230072969 + 3 ^ 40 * 3532068 * 2
def baseEnd_3532068 : Nat := 1813648588364792001406321

theorem tailTrace_3532068 : CollatzResearch.WordTrace tailWord_3532068 prefixEnd_3532068 1813648588364792001406321 := by
  unfold tailWord_3532068
  simp only [CollatzResearch.WordTrace]
  refine ⟨64412551683964170016990429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85883402245285560022653905 64412551683964170016990429)
  ·
    refine ⟨24154706881486563756371411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64412551683964170016990429 24154706881486563756371411)
    ·
      refine ⟨36232060322229845634557117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24154706881486563756371411 36232060322229845634557117)
      ·
        refine ⟨13587022620836192112958919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36232060322229845634557117 13587022620836192112958919)
        ·
          refine ⟨20380533931254288169438379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13587022620836192112958919 20380533931254288169438379)
          ·
            refine ⟨30570800896881432254157569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20380533931254288169438379 30570800896881432254157569)
            ·
              refine ⟨22928100672661074190618177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30570800896881432254157569 22928100672661074190618177)
              ·
                refine ⟨17196075504495805642963633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22928100672661074190618177 17196075504495805642963633)
                ·
                  refine ⟨12897056628371854232222725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17196075504495805642963633 12897056628371854232222725)
                  ·
                    refine ⟨2418198117819722668541761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12897056628371854232222725 2418198117819722668541761)
                    ·
                      refine ⟨1813648588364792001406321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2418198117819722668541761 1813648588364792001406321)
                      ·
                        rfl

theorem cell23_3532068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_3532068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532068 prefixEnd_3532068 := by exact prefixLift 3532068
  have htrace : WordTrace (prefixWord ++ tailWord_3532068) baseStart_3532068 baseEnd_3532068 := by
    simpa [prefixWord, tailWord_3532068, baseEnd_3532068] using wordTrace_append hprefix tailTrace_3532068
  have hstable : (prefixWord ++ tailWord_3532068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532068).length < 2 ^ (prefixWord ++ tailWord_3532068).sum := by decide
  have hdescent : baseEnd_3532068 < baseStart_3532068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532102 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3532102 : Nat := 118140960795 + 3532102 * 2 ^ 59
def prefixEnd_3532102 : Nat := 4983230072969 + 3 ^ 40 * 3532102 * 2
def baseEnd_3532102 : Nat := 1813666046707044868381165

theorem tailTrace_3532102 : CollatzResearch.WordTrace tailWord_3532102 prefixEnd_3532102 1813666046707044868381165 := by
  unfold tailWord_3532102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4025823232806411370022455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85884228966536775893812373 4025823232806411370022455)
  ·
    refine ⟨6038734849209617055033683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4025823232806411370022455 6038734849209617055033683)
    ·
      refine ⟨9058102273814425582550525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6038734849209617055033683 9058102273814425582550525)
      ·
        refine ⟨3396788352680409593456447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9058102273814425582550525 3396788352680409593456447)
        ·
          refine ⟨5095182529020614390184671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3396788352680409593456447 5095182529020614390184671)
          ·
            refine ⟨7642773793530921585277007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5095182529020614390184671 7642773793530921585277007)
            ·
              refine ⟨11464160690296382377915511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7642773793530921585277007 11464160690296382377915511)
              ·
                refine ⟨17196241035444573566873267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11464160690296382377915511 17196241035444573566873267)
                ·
                  refine ⟨25794361553166860350309901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17196241035444573566873267 25794361553166860350309901)
                  ·
                    refine ⟨9672885582437572631366213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25794361553166860350309901 9672885582437572631366213)
                    ·
                      refine ⟨1813666046707044868381165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9672885582437572631366213 1813666046707044868381165)
                      ·
                        rfl

theorem cell23_3532102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3532102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532102 prefixEnd_3532102 := by exact prefixLift 3532102
  have htrace : WordTrace (prefixWord ++ tailWord_3532102) baseStart_3532102 baseEnd_3532102 := by
    simpa [prefixWord, tailWord_3532102, baseEnd_3532102] using wordTrace_append hprefix tailTrace_3532102
  have hstable : (prefixWord ++ tailWord_3532102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532102).length < 2 ^ (prefixWord ++ tailWord_3532102).sum := by decide
  have hdescent : baseEnd_3532102 < baseStart_3532102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532142 : List Nat := [4, 1, 2, 4, 1, 1, 3, 1, 6]
def baseStart_3532142 : Nat := 118140960795 + 3532142 * 2 ^ 59
def prefixEnd_3532142 : Nat := 4983230072969 + 3 ^ 40 * 3532142 * 2
def baseEnd_3532142 : Nat := 201520731770358301320109

theorem tailTrace_3532142 : CollatzResearch.WordTrace tailWord_3532142 prefixEnd_3532142 201520731770358301320109 := by
  unfold tailWord_3532142
  simp only [CollatzResearch.WordTrace]
  refine ⟨16103475296207531334021835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85885201579773500448116453 16103475296207531334021835)
  ·
    refine ⟨24155212944311297001032753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16103475296207531334021835 24155212944311297001032753)
    ·
      refine ⟨18116409708233472750774565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24155212944311297001032753 18116409708233472750774565)
      ·
        refine ⟨3396826820293776140770231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18116409708233472750774565 3396826820293776140770231)
        ·
          refine ⟨5095240230440664211155347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3396826820293776140770231 5095240230440664211155347)
          ·
            refine ⟨7642860345660996316733021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5095240230440664211155347 7642860345660996316733021)
            ·
              refine ⟨2866072629622873618774883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7642860345660996316733021 2866072629622873618774883)
              ·
                refine ⟨4299108944434310428162325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2866072629622873618774883 4299108944434310428162325)
                ·
                  refine ⟨201520731770358301320109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4299108944434310428162325 201520731770358301320109)
                  ·
                    rfl

theorem cell23_3532142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_3532142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532142 prefixEnd_3532142 := by exact prefixLift 3532142
  have htrace : WordTrace (prefixWord ++ tailWord_3532142) baseStart_3532142 baseEnd_3532142 := by
    simpa [prefixWord, tailWord_3532142, baseEnd_3532142] using wordTrace_append hprefix tailTrace_3532142
  have hstable : (prefixWord ++ tailWord_3532142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532142).length < 2 ^ (prefixWord ++ tailWord_3532142).sum := by decide
  have hdescent : baseEnd_3532142 < baseStart_3532142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532162 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_3532162 : Nat := 118140960795 + 3532162 * 2 ^ 59
def prefixEnd_3532162 : Nat := 4983230072969 + 3 ^ 40 * 3532162 * 2
def baseEnd_3532162 : Nat := 1813696855546314633630889

theorem tailTrace_3532162 : CollatzResearch.WordTrace tailWord_3532162 prefixEnd_3532162 1813696855546314633630889 := by
  unfold tailWord_3532162
  simp only [CollatzResearch.WordTrace]
  refine ⟨32207132957396948521975685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85885687886391862725268493 32207132957396948521975685)
  ·
    refine ⟨6038837429511927847870441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32207132957396948521975685 6038837429511927847870441)
    ·
      refine ⟨4529128072133945885902831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6038837429511927847870441 4529128072133945885902831)
      ·
        refine ⟨6793692108200918828854247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4529128072133945885902831 6793692108200918828854247)
        ·
          refine ⟨10190538162301378243281371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6793692108200918828854247 10190538162301378243281371)
          ·
            refine ⟨15285807243452067364922057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10190538162301378243281371 15285807243452067364922057)
            ·
              refine ⟨11464355432589050523691543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15285807243452067364922057 11464355432589050523691543)
              ·
                refine ⟨17196533148883575785537315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11464355432589050523691543 17196533148883575785537315)
                ·
                  refine ⟨25794799723325363678305973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17196533148883575785537315 25794799723325363678305973)
                  ·
                    refine ⟨2418262474061752844841185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25794799723325363678305973 2418262474061752844841185)
                    ·
                      refine ⟨1813696855546314633630889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2418262474061752844841185 1813696855546314633630889)
                      ·
                        rfl

theorem cell23_3532162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_3532162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532162 prefixEnd_3532162 := by exact prefixLift 3532162
  have htrace : WordTrace (prefixWord ++ tailWord_3532162) baseStart_3532162 baseEnd_3532162 := by
    simpa [prefixWord, tailWord_3532162, baseEnd_3532162] using wordTrace_append hprefix tailTrace_3532162
  have hstable : (prefixWord ++ tailWord_3532162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532162).length < 2 ^ (prefixWord ++ tailWord_3532162).sum := by decide
  have hdescent : baseEnd_3532162 < baseStart_3532162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532168 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 4, 4]
def baseStart_3532168 : Nat := 118140960795 + 3532168 * 2 ^ 59
def prefixEnd_3532168 : Nat := 4983230072969 + 3 ^ 40 * 3532168 * 2
def baseEnd_3532168 : Nat := 604566645476747203385287

theorem tailTrace_3532168 : CollatzResearch.WordTrace tailWord_3532168 prefixEnd_3532168 604566645476747203385287 := by
  unfold tailWord_3532168
  simp only [CollatzResearch.WordTrace]
  refine ⟨64414375333783028556310579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85885833778377371408414105 64414375333783028556310579)
  ·
    refine ⟨96621563000674542834465869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64414375333783028556310579 96621563000674542834465869)
    ·
      refine ⟨36233086125252953562924701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96621563000674542834465869 36233086125252953562924701)
      ·
        refine ⟨13587407296969857586096763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36233086125252953562924701 13587407296969857586096763)
        ·
          refine ⟨20381110945454786379145145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13587407296969857586096763 20381110945454786379145145)
          ·
            refine ⟨15285833209091089784358859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20381110945454786379145145 15285833209091089784358859)
            ·
              refine ⟨22928749813636634676538289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15285833209091089784358859 22928749813636634676538289)
              ·
                refine ⟨17196562360227476007403717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22928749813636634676538289 17196562360227476007403717)
                ·
                  refine ⟨3224355442542651751388197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17196562360227476007403717 3224355442542651751388197)
                  ·
                    refine ⟨604566645476747203385287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3224355442542651751388197 604566645476747203385287)
                    ·
                      rfl

theorem cell23_3532168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_3532168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532168 prefixEnd_3532168 := by exact prefixLift 3532168
  have htrace : WordTrace (prefixWord ++ tailWord_3532168) baseStart_3532168 baseEnd_3532168 := by
    simpa [prefixWord, tailWord_3532168, baseEnd_3532168] using wordTrace_append hprefix tailTrace_3532168
  have hstable : (prefixWord ++ tailWord_3532168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532168).length < 2 ^ (prefixWord ++ tailWord_3532168).sum := by decide
  have hdescent : baseEnd_3532168 < baseStart_3532168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532169 : List Nat := [1, 2, 1, 1, 7, 2, 1, 3, 1, 1, 3]
def baseStart_3532169 : Nat := 118140960795 + 3532169 * 2 ^ 59
def prefixEnd_3532169 : Nat := 4983230072969 + 3 ^ 40 * 3532169 * 2
def baseEnd_3532169 : Nat := 1813700449910896106243357

theorem tailTrace_3532169 : CollatzResearch.WordTrace tailWord_3532169 prefixEnd_3532169 1813700449910896106243357 := by
  unfold tailWord_3532169
  simp only [CollatzResearch.WordTrace]
  refine ⟨128828787140562434283407561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85885858093708289522271707 128828787140562434283407561)
  ·
    refine ⟨96621590355421825712555671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128828787140562434283407561 96621590355421825712555671)
    ·
      refine ⟨144932385533132738568833507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96621590355421825712555671 144932385533132738568833507)
      ·
        refine ⟨217398578299699107853250261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144932385533132738568833507 217398578299699107853250261)
        ·
          refine ⟨5095279178899197840310553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 217398578299699107853250261 5095279178899197840310553)
          ·
            refine ⟨3821459384174398380232915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5095279178899197840310553 3821459384174398380232915)
            ·
              refine ⟨5732189076261597570349373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3821459384174398380232915 5732189076261597570349373)
              ·
                refine ⟨2149570903598099088881015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5732189076261597570349373 2149570903598099088881015)
                ·
                  refine ⟨3224356355397148633321523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2149570903598099088881015 3224356355397148633321523)
                  ·
                    refine ⟨4836534533095722949982285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3224356355397148633321523 4836534533095722949982285)
                    ·
                      refine ⟨1813700449910896106243357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4836534533095722949982285 1813700449910896106243357)
                      ·
                        rfl

theorem cell23_3532169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 1, 1, 3].length) (baseStart_3532169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532169 prefixEnd_3532169 := by exact prefixLift 3532169
  have htrace : WordTrace (prefixWord ++ tailWord_3532169) baseStart_3532169 baseEnd_3532169 := by
    simpa [prefixWord, tailWord_3532169, baseEnd_3532169] using wordTrace_append hprefix tailTrace_3532169
  have hstable : (prefixWord ++ tailWord_3532169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532169).length < 2 ^ (prefixWord ++ tailWord_3532169).sum := by decide
  have hdescent : baseEnd_3532169 < baseStart_3532169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532171 : List Nat := [1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 4]
def baseStart_3532171 : Nat := 118140960795 + 3532171 * 2 ^ 59
def prefixEnd_3532171 : Nat := 4983230072969 + 3 ^ 40 * 3532171 * 2
def baseEnd_3532171 : Nat := 1813701476872205098418347

theorem tailTrace_3532171 : CollatzResearch.WordTrace tailWord_3532171 prefixEnd_3532171 1813701476872205098418347 := by
  unfold tailWord_3532171
  simp only [CollatzResearch.WordTrace]
  refine ⟨128828860086555188624980367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85885906724370125749986911 128828860086555188624980367)
  ·
    refine ⟨193243290129832782937470551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128828860086555188624980367 193243290129832782937470551)
    ·
      refine ⟨289864935194749174406205827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193243290129832782937470551 289864935194749174406205827)
      ·
        refine ⟨434797402792123761609308741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289864935194749174406205827 434797402792123761609308741)
        ·
          refine ⟨81524513023523205301745389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 434797402792123761609308741 81524513023523205301745389)
          ·
            refine ⟨30571692383821201988154521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81524513023523205301745389 30571692383821201988154521)
            ·
              refine ⟨22928769287865901491115891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30571692383821201988154521 22928769287865901491115891)
              ·
                refine ⟨34393153931798852236673837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22928769287865901491115891 34393153931798852236673837)
                ·
                  refine ⟨12897432724424569588752689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34393153931798852236673837 12897432724424569588752689)
                  ·
                    refine ⟨9673074543318427191564517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12897432724424569588752689 9673074543318427191564517)
                    ·
                      refine ⟨1813701476872205098418347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9673074543318427191564517 1813701476872205098418347)
                      ·
                        rfl

theorem cell23_3532171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 4].length) (baseStart_3532171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532171 prefixEnd_3532171 := by exact prefixLift 3532171
  have htrace : WordTrace (prefixWord ++ tailWord_3532171) baseStart_3532171 baseEnd_3532171 := by
    simpa [prefixWord, tailWord_3532171, baseEnd_3532171] using wordTrace_append hprefix tailTrace_3532171
  have hstable : (prefixWord ++ tailWord_3532171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532171).length < 2 ^ (prefixWord ++ tailWord_3532171).sum := by decide
  have hdescent : baseEnd_3532171 < baseStart_3532171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532208 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 6, 1, 3]
def baseStart_3532208 : Nat := 118140960795 + 3532208 * 2 ^ 59
def prefixEnd_3532208 : Nat := 4983230072969 + 3 ^ 40 * 3532208 * 2
def baseEnd_3532208 : Nat := 1813720475656421453655677

theorem tailTrace_3532208 : CollatzResearch.WordTrace tailWord_3532208 prefixEnd_3532208 1813720475656421453655677 := by
  unfold tailWord_3532208
  simp only [CollatzResearch.WordTrace]
  refine ⟨64415104793710571972038639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85886806391614095962718185 64415104793710571972038639)
  ·
    refine ⟨96622657190565857958057959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64415104793710571972038639 96622657190565857958057959)
    ·
      refine ⟨144933985785848786937086939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96622657190565857958057959 144933985785848786937086939)
      ·
        refine ⟨217400978678773180405630409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144933985785848786937086939 217400978678773180405630409)
        ·
          refine ⟨163050734009079885304222807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217400978678773180405630409 163050734009079885304222807)
          ·
            refine ⟨244576101013619827956334211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163050734009079885304222807 244576101013619827956334211)
            ·
              refine ⟨366864151520429741934501317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244576101013619827956334211 366864151520429741934501317)
              ·
                refine ⟨68787028410080576612718997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 366864151520429741934501317 68787028410080576612718997)
                ·
                  refine ⟨3224391956722527028721203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 68787028410080576612718997 3224391956722527028721203)
                  ·
                    refine ⟨4836587935083790543081805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3224391956722527028721203 4836587935083790543081805)
                    ·
                      refine ⟨1813720475656421453655677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4836587935083790543081805 1813720475656421453655677)
                      ·
                        rfl

theorem cell23_3532208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 6, 1, 3].length) (baseStart_3532208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532208 prefixEnd_3532208 := by exact prefixLift 3532208
  have htrace : WordTrace (prefixWord ++ tailWord_3532208) baseStart_3532208 baseEnd_3532208 := by
    simpa [prefixWord, tailWord_3532208, baseEnd_3532208] using wordTrace_append hprefix tailTrace_3532208
  have hstable : (prefixWord ++ tailWord_3532208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532208).length < 2 ^ (prefixWord ++ tailWord_3532208).sum := by decide
  have hdescent : baseEnd_3532208 < baseStart_3532208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532235 : List Nat := [1, 1, 1, 1, 3, 3, 2, 5, 1, 3, 2]
def baseStart_3532235 : Nat := 118140960795 + 3532235 * 2 ^ 59
def prefixEnd_3532235 : Nat := 4983230072969 + 3 ^ 40 * 3532235 * 2
def baseEnd_3532235 : Nat := 1813734339634092848018053

theorem tailTrace_3532235 : CollatzResearch.WordTrace tailWord_3532235 prefixEnd_3532235 1813734339634092848018053 := by
  unfold tailWord_3532235
  simp only [CollatzResearch.WordTrace]
  refine ⟨128831194358323327555310159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85887462905548885036873439 128831194358323327555310159)
  ·
    refine ⟨193246791537484991332965239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128831194358323327555310159 193246791537484991332965239)
    ·
      refine ⟨289870187306227486999447859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193246791537484991332965239 289870187306227486999447859)
      ·
        refine ⟨434805280959341230499171789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289870187306227486999447859 434805280959341230499171789)
        ·
          refine ⟨163051980359752961437189421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 434805280959341230499171789 163051980359752961437189421)
          ·
            refine ⟨61144492634907360538946033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163051980359752961437189421 61144492634907360538946033)
            ·
              refine ⟨45858369476180520404209525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61144492634907360538946033 45858369476180520404209525)
              ·
                refine ⟨4299222138391923787894643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45858369476180520404209525 4299222138391923787894643)
                ·
                  refine ⟨6448833207587885681841965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4299222138391923787894643 6448833207587885681841965)
                  ·
                    refine ⟨2418312452845457130690737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6448833207587885681841965 2418312452845457130690737)
                    ·
                      refine ⟨1813734339634092848018053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2418312452845457130690737 1813734339634092848018053)
                      ·
                        rfl

theorem cell23_3532235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 3, 2].length) (baseStart_3532235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532235 prefixEnd_3532235 := by exact prefixLift 3532235
  have htrace : WordTrace (prefixWord ++ tailWord_3532235) baseStart_3532235 baseEnd_3532235 := by
    simpa [prefixWord, tailWord_3532235, baseEnd_3532235] using wordTrace_append hprefix tailTrace_3532235
  have hstable : (prefixWord ++ tailWord_3532235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532235).length < 2 ^ (prefixWord ++ tailWord_3532235).sum := by decide
  have hdescent : baseEnd_3532235 < baseStart_3532235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532271 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 9]
def baseStart_3532271 : Nat := 118140960795 + 3532271 * 2 ^ 59
def prefixEnd_3532271 : Nat := 4983230072969 + 3 ^ 40 * 3532271 * 2
def baseEnd_3532271 : Nat := 201528091659739411907543

theorem tailTrace_3532271 : CollatzResearch.WordTrace tailWord_3532271 prefixEnd_3532271 201528091659739411907543 := by
  unfold tailWord_3532271
  simp only [CollatzResearch.WordTrace]
  refine ⟨128832507386192905703620667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85888338257461937135747111 128832507386192905703620667)
  ·
    refine ⟨193248761079289358555431001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128832507386192905703620667 193248761079289358555431001)
    ·
      refine ⟨144936570809467018916573251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193248761079289358555431001 144936570809467018916573251)
      ·
        refine ⟨217404856214200528374859877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144936570809467018916573251 217404856214200528374859877)
        ·
          refine ⟨40763410540162599070286227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217404856214200528374859877 40763410540162599070286227)
          ·
            refine ⟨61145115810243898605429341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40763410540162599070286227 61145115810243898605429341)
            ·
              refine ⟨22929418428841461977036003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61145115810243898605429341 22929418428841461977036003)
              ·
                refine ⟨34394127643262192965554005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22929418428841461977036003 34394127643262192965554005)
                ·
                  refine ⟨201528091659739411907543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 34394127643262192965554005 201528091659739411907543)
                  ·
                    rfl

theorem cell23_3532271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 9].length) (baseStart_3532271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532271 prefixEnd_3532271 := by exact prefixLift 3532271
  have htrace : WordTrace (prefixWord ++ tailWord_3532271) baseStart_3532271 baseEnd_3532271 := by
    simpa [prefixWord, tailWord_3532271, baseEnd_3532271] using wordTrace_append hprefix tailTrace_3532271
  have hstable : (prefixWord ++ tailWord_3532271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532271).length < 2 ^ (prefixWord ++ tailWord_3532271).sum := by decide
  have hdescent : baseEnd_3532271 < baseStart_3532271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532281 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 7]
def baseStart_3532281 : Nat := 118140960795 + 3532281 * 2 ^ 59
def prefixEnd_3532281 : Nat := 4983230072969 + 3 ^ 40 * 3532281 * 2
def baseEnd_3532281 : Nat := 1813757959744199668042841

theorem tailTrace_3532281 : CollatzResearch.WordTrace tailWord_3532281 prefixEnd_3532281 1813757959744199668042841 := by
  unfold tailWord_3532281
  simp only [CollatzResearch.WordTrace]
  refine ⟨128832872116156677411484697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85888581410771118274323131 128832872116156677411484697)
  ·
    refine ⟨96624654087117508058613523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128832872116156677411484697 96624654087117508058613523)
    ·
      refine ⟨144936981130676262087920285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96624654087117508058613523 144936981130676262087920285)
      ·
        refine ⟨54351367924003598282970107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144936981130676262087920285 54351367924003598282970107)
        ·
          refine ⟨81527051886005397424455161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54351367924003598282970107 81527051886005397424455161)
          ·
            refine ⟨61145288914504048068341371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81527051886005397424455161 61145288914504048068341371)
            ·
              refine ⟨91717933371756072102512057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61145288914504048068341371 91717933371756072102512057)
              ·
                refine ⟨68788450028817054076884043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91717933371756072102512057 68788450028817054076884043)
                ·
                  refine ⟨103182675043225581115326065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 68788450028817054076884043 103182675043225581115326065)
                  ·
                    refine ⟨77387006282419185836494549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103182675043225581115326065 77387006282419185836494549)
                    ·
                      refine ⟨1813757959744199668042841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77387006282419185836494549 1813757959744199668042841)
                      ·
                        rfl

theorem cell23_3532281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_3532281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532281 prefixEnd_3532281 := by exact prefixLift 3532281
  have htrace : WordTrace (prefixWord ++ tailWord_3532281) baseStart_3532281 baseEnd_3532281 := by
    simpa [prefixWord, tailWord_3532281, baseEnd_3532281] using wordTrace_append hprefix tailTrace_3532281
  have hstable : (prefixWord ++ tailWord_3532281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532281).length < 2 ^ (prefixWord ++ tailWord_3532281).sum := by decide
  have hdescent : baseEnd_3532281 < baseStart_3532281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532286 : List Nat := [4, 2, 2, 3, 1, 1, 1, 3, 1, 3, 2]
def baseStart_3532286 : Nat := 118140960795 + 3532286 * 2 ^ 59
def prefixEnd_3532286 : Nat := 4983230072969 + 3 ^ 40 * 3532286 * 2
def baseEnd_3532286 : Nat := 1813760527147472148480319

theorem tailTrace_3532286 : CollatzResearch.WordTrace tailWord_3532286 prefixEnd_3532286 1813760527147472148480319 := by
  unfold tailWord_3532286
  simp only [CollatzResearch.WordTrace]
  refine ⟨16104131810142320408177089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85888702987425708843611141 16104131810142320408177089)
  ·
    refine ⟨12078098857606740306132817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16104131810142320408177089 12078098857606740306132817)
    ·
      refine ⟨9058574143205055229599613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12078098857606740306132817 9058574143205055229599613)
      ·
        refine ⟨3396965303701895711099855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9058574143205055229599613 3396965303701895711099855)
        ·
          refine ⟨5095447955552843566649783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3396965303701895711099855 5095447955552843566649783)
          ·
            refine ⟨7643171933329265349974675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5095447955552843566649783 7643171933329265349974675)
            ·
              refine ⟨11464757899993898024962013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7643171933329265349974675 11464757899993898024962013)
              ·
                refine ⟨4299284212497711759360755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11464757899993898024962013 4299284212497711759360755)
                ·
                  refine ⟨6448926318746567639041133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4299284212497711759360755 6448926318746567639041133)
                  ·
                    refine ⟨2418347369529962864640425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6448926318746567639041133 2418347369529962864640425)
                    ·
                      refine ⟨1813760527147472148480319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2418347369529962864640425 1813760527147472148480319)
                      ·
                        rfl

theorem cell23_3532286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_3532286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532286 prefixEnd_3532286 := by exact prefixLift 3532286
  have htrace : WordTrace (prefixWord ++ tailWord_3532286) baseStart_3532286 baseEnd_3532286 := by
    simpa [prefixWord, tailWord_3532286, baseEnd_3532286] using wordTrace_append hprefix tailTrace_3532286
  have hstable : (prefixWord ++ tailWord_3532286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532286).length < 2 ^ (prefixWord ++ tailWord_3532286).sum := by decide
  have hdescent : baseEnd_3532286 < baseStart_3532286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532392 : List Nat := [2, 1, 4, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_3532392 : Nat := 118140960795 + 3532392 * 2 ^ 59
def prefixEnd_3532392 : Nat := 4983230072969 + 3 ^ 40 * 3532392 * 2
def baseEnd_3532392 : Nat := 1813814956096848733754831

theorem tailTrace_3532392 : CollatzResearch.WordTrace tailWord_3532392 prefixEnd_3532392 1813814956096848733754831 := by
  unfold tailWord_3532392
  simp only [CollatzResearch.WordTrace]
  refine ⟨64418460309377271684387715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85891280412503028912516953 64418460309377271684387715)
  ·
    refine ⟨96627690464065907526581573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64418460309377271684387715 96627690464065907526581573)
    ·
      refine ⟨18117691962012357661234045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96627690464065907526581573 18117691962012357661234045)
      ·
        refine ⟨6794134485754634122962767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18117691962012357661234045 6794134485754634122962767)
        ·
          refine ⟨10191201728631951184444151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6794134485754634122962767 10191201728631951184444151)
          ·
            refine ⟨15286802592947926776666227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10191201728631951184444151 15286802592947926776666227)
            ·
              refine ⟨22930203889421890164999341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15286802592947926776666227 22930203889421890164999341)
              ·
                refine ⟨8598826458533208811874753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22930203889421890164999341 8598826458533208811874753)
                ·
                  refine ⟨6449119843899906608906065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8598826458533208811874753 6449119843899906608906065)
                  ·
                    refine ⟨4836839882924929956679549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6449119843899906608906065 4836839882924929956679549)
                    ·
                      refine ⟨1813814956096848733754831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4836839882924929956679549 1813814956096848733754831)
                      ·
                        rfl

theorem cell23_3532392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_3532392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532392 prefixEnd_3532392 := by exact prefixLift 3532392
  have htrace : WordTrace (prefixWord ++ tailWord_3532392) baseStart_3532392 baseEnd_3532392 := by
    simpa [prefixWord, tailWord_3532392, baseEnd_3532392] using wordTrace_append hprefix tailTrace_3532392
  have hstable : (prefixWord ++ tailWord_3532392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532392).length < 2 ^ (prefixWord ++ tailWord_3532392).sum := by decide
  have hdescent : baseEnd_3532392 < baseStart_3532392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532408 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 7, 5]
def baseStart_3532408 : Nat := 118140960795 + 3532408 * 2 ^ 59
def prefixEnd_3532408 : Nat := 4983230072969 + 3 ^ 40 * 3532408 * 2
def baseEnd_3532408 : Nat := 604607723929106890384919

theorem tailTrace_3532408 : CollatzResearch.WordTrace tailWord_3532408 prefixEnd_3532408 604607723929106890384919 := by
  unfold tailWord_3532408
  simp only [CollatzResearch.WordTrace]
  refine ⟨64418752093348289050678939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85891669457797718734238585 64418752093348289050678939)
  ·
    refine ⟨96628128140022433576018409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64418752093348289050678939 96628128140022433576018409)
    ·
      refine ⟨72471096105016825182013807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96628128140022433576018409 72471096105016825182013807)
      ·
        refine ⟨108706644157525237773020711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72471096105016825182013807 108706644157525237773020711)
        ·
          refine ⟨163059966236287856659531067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108706644157525237773020711 163059966236287856659531067)
          ·
            refine ⟨244589949354431784989296601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163059966236287856659531067 244589949354431784989296601)
            ·
              refine ⟨183442462015823838741972451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244589949354431784989296601 183442462015823838741972451)
              ·
                refine ⟨275163693023735758112958677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183442462015823838741972451 275163693023735758112958677)
                ·
                  refine ⟨6449149055243806830772469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 275163693023735758112958677 6449149055243806830772469)
                  ·
                    refine ⟨604607723929106890384919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6449149055243806830772469 604607723929106890384919)
                    ·
                      rfl

theorem cell23_3532408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_3532408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532408 prefixEnd_3532408 := by exact prefixLift 3532408
  have htrace : WordTrace (prefixWord ++ tailWord_3532408) baseStart_3532408 baseEnd_3532408 := by
    simpa [prefixWord, tailWord_3532408, baseEnd_3532408] using wordTrace_append hprefix tailTrace_3532408
  have hstable : (prefixWord ++ tailWord_3532408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532408).length < 2 ^ (prefixWord ++ tailWord_3532408).sum := by decide
  have hdescent : baseEnd_3532408 < baseStart_3532408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532449 : List Nat := [1, 2, 3, 3, 2, 1, 3, 1, 2, 3, 2]
def baseStart_3532449 : Nat := 118140960795 + 3532449 * 2 ^ 59
def prefixEnd_3532449 : Nat := 4983230072969 + 3 ^ 40 * 3532449 * 2
def baseEnd_3532449 : Nat := 1813844224494155010742069

theorem tailTrace_3532449 : CollatzResearch.WordTrace tailWord_3532449 prefixEnd_3532449 1813844224494155010742069 := by
  unfold tailWord_3532449
  simp only [CollatzResearch.WordTrace]
  refine ⟨128838999579548042103600401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85892666386365361402400267 128838999579548042103600401)
  ·
    refine ⟨96629249684661031577700301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128838999579548042103600401 96629249684661031577700301)
    ·
      refine ⟨36235968631747886841637613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96629249684661031577700301 36235968631747886841637613)
      ·
        refine ⟨13588488236905457565614105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36235968631747886841637613 13588488236905457565614105)
        ·
          refine ⟨10191366177679093174210579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13588488236905457565614105 10191366177679093174210579)
          ·
            refine ⟨15287049266518639761315869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10191366177679093174210579 15287049266518639761315869)
            ·
              refine ⟨5732643474944489910493451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15287049266518639761315869 5732643474944489910493451)
              ·
                refine ⟨8598965212416734865740177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5732643474944489910493451 8598965212416734865740177)
                ·
                  refine ⟨6449223909312551149305133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8598965212416734865740177 6449223909312551149305133)
                  ·
                    refine ⟨2418458965992206680989425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6449223909312551149305133 2418458965992206680989425)
                    ·
                      refine ⟨1813844224494155010742069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2418458965992206680989425 1813844224494155010742069)
                      ·
                        rfl

theorem cell23_3532449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_3532449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532449 prefixEnd_3532449 := by exact prefixLift 3532449
  have htrace : WordTrace (prefixWord ++ tailWord_3532449) baseStart_3532449 baseEnd_3532449 := by
    simpa [prefixWord, tailWord_3532449, baseEnd_3532449] using wordTrace_append hprefix tailTrace_3532449
  have hstable : (prefixWord ++ tailWord_3532449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532449).length < 2 ^ (prefixWord ++ tailWord_3532449).sum := by decide
  have hdescent : baseEnd_3532449 < baseStart_3532449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532479 : List Nat := [1, 1, 2, 2, 2, 3, 4, 1, 3, 2, 2]
def baseStart_3532479 : Nat := 118140960795 + 3532479 * 2 ^ 59
def prefixEnd_3532479 : Nat := 4983230072969 + 3 ^ 40 * 3532479 * 2
def baseEnd_3532479 : Nat := 1813859628913789893366931

theorem tailTrace_3532479 : CollatzResearch.WordTrace tailWord_3532479 prefixEnd_3532479 1813859628913789893366931 := by
  unfold tailWord_3532479
  simp only [CollatzResearch.WordTrace]
  refine ⟨128840093769439357227192491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85893395846292904818128327 128840093769439357227192491)
  ·
    refine ⟨193260140654159035840788737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128840093769439357227192491 193260140654159035840788737)
    ·
      refine ⟨144945105490619276880591553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193260140654159035840788737 144945105490619276880591553)
      ·
        refine ⟨108708829117964457660443665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144945105490619276880591553 108708829117964457660443665)
        ·
          refine ⟨81531621838473343245332749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108708829117964457660443665 81531621838473343245332749)
          ·
            refine ⟨30574358189427503716999781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81531621838473343245332749 30574358189427503716999781)
            ·
              refine ⟨5732692160517656946937459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30574358189427503716999781 5732692160517656946937459)
              ·
                refine ⟨8599038240776485420406189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5732692160517656946937459 8599038240776485420406189)
                ·
                  refine ⟨3224639340291182032652321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8599038240776485420406189 3224639340291182032652321)
                  ·
                    refine ⟨2418479505218386524489241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3224639340291182032652321 2418479505218386524489241)
                    ·
                      refine ⟨1813859628913789893366931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2418479505218386524489241 1813859628913789893366931)
                      ·
                        rfl

theorem cell23_3532479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 2, 2].length) (baseStart_3532479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532479 prefixEnd_3532479 := by exact prefixLift 3532479
  have htrace : WordTrace (prefixWord ++ tailWord_3532479) baseStart_3532479 baseEnd_3532479 := by
    simpa [prefixWord, tailWord_3532479, baseEnd_3532479] using wordTrace_append hprefix tailTrace_3532479
  have hstable : (prefixWord ++ tailWord_3532479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532479).length < 2 ^ (prefixWord ++ tailWord_3532479).sum := by decide
  have hdescent : baseEnd_3532479 < baseStart_3532479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532492 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 1, 1, 6]
def baseStart_3532492 : Nat := 118140960795 + 3532492 * 2 ^ 59
def prefixEnd_3532492 : Nat := 4983230072969 + 3 ^ 40 * 3532492 * 2
def baseEnd_3532492 : Nat := 1813866304162298342504371

theorem tailTrace_3532492 : CollatzResearch.WordTrace tailWord_3532492 prefixEnd_3532492 1813866304162298342504371 := by
  unfold tailWord_3532492
  simp only [CollatzResearch.WordTrace]
  refine ⟨64420283959196130223707865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85893711945594840298277153 64420283959196130223707865)
  ·
    refine ⟨48315212969397097667780899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64420283959196130223707865 48315212969397097667780899)
    ·
      refine ⟨72472819454095646501671349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48315212969397097667780899 72472819454095646501671349)
      ·
        refine ⟨6794326823821466859531689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72472819454095646501671349 6794326823821466859531689)
        ·
          refine ⟨5095745117866100144648767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6794326823821466859531689 5095745117866100144648767)
          ·
            refine ⟨7643617676799150216973151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5095745117866100144648767 7643617676799150216973151)
            ·
              refine ⟨11465426515198725325459727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7643617676799150216973151 11465426515198725325459727)
              ·
                refine ⟨17198139772798087988189591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11465426515198725325459727 17198139772798087988189591)
                ·
                  refine ⟨25797209659197131982284387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17198139772798087988189591 25797209659197131982284387)
                  ·
                    refine ⟨38695814488795697973426581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25797209659197131982284387 38695814488795697973426581)
                    ·
                      refine ⟨1813866304162298342504371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38695814488795697973426581 1813866304162298342504371)
                      ·
                        rfl

theorem cell23_3532492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_3532492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532492 prefixEnd_3532492 := by exact prefixLift 3532492
  have htrace : WordTrace (prefixWord ++ tailWord_3532492) baseStart_3532492 baseEnd_3532492 := by
    simpa [prefixWord, tailWord_3532492, baseEnd_3532492] using wordTrace_append hprefix tailTrace_3532492
  have hstable : (prefixWord ++ tailWord_3532492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532492).length < 2 ^ (prefixWord ++ tailWord_3532492).sum := by decide
  have hdescent : baseEnd_3532492 < baseStart_3532492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532512 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 4, 1, 3]
def baseStart_3532512 : Nat := 118140960795 + 3532512 * 2 ^ 59
def prefixEnd_3532512 : Nat := 4983230072969 + 3 ^ 40 * 3532512 * 2
def baseEnd_3532512 : Nat := 1813876573775388264254279

theorem tailTrace_3532512 : CollatzResearch.WordTrace tailWord_3532512 prefixEnd_3532512 1813876573775388264254279 := by
  unfold tailWord_3532512
  simp only [CollatzResearch.WordTrace]
  refine ⟨64420648689159901931571895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85894198252213202575429193 64420648689159901931571895)
  ·
    refine ⟨96630973033739852897357843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64420648689159901931571895 96630973033739852897357843)
    ·
      refine ⟨144946459550609779346036765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96630973033739852897357843 144946459550609779346036765)
      ·
        refine ⟨54354922331478667254763787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144946459550609779346036765 54354922331478667254763787)
        ·
          refine ⟨81532383497218000882145681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54354922331478667254763787 81532383497218000882145681)
          ·
            refine ⟨61149287622913500661609261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81532383497218000882145681 61149287622913500661609261)
            ·
              refine ⟨22930982858592562748103473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61149287622913500661609261 22930982858592562748103473)
              ·
                refine ⟨17198237143944422061077605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22930982858592562748103473 17198237143944422061077605)
                ·
                  refine ⟨3224669464489579136452051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17198237143944422061077605 3224669464489579136452051)
                  ·
                    refine ⟨4837004196734368704678077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3224669464489579136452051 4837004196734368704678077)
                    ·
                      refine ⟨1813876573775388264254279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4837004196734368704678077 1813876573775388264254279)
                      ·
                        rfl

theorem cell23_3532512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_3532512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532512 prefixEnd_3532512 := by exact prefixLift 3532512
  have htrace : WordTrace (prefixWord ++ tailWord_3532512) baseStart_3532512 baseEnd_3532512 := by
    simpa [prefixWord, tailWord_3532512, baseEnd_3532512] using wordTrace_append hprefix tailTrace_3532512
  have hstable : (prefixWord ++ tailWord_3532512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532512).length < 2 ^ (prefixWord ++ tailWord_3532512).sum := by decide
  have hdescent : baseEnd_3532512 < baseStart_3532512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532519 : List Nat := [1, 1, 5, 4, 2, 1, 9]
def baseStart_3532519 : Nat := 118140960795 + 3532519 * 2 ^ 59
def prefixEnd_3532519 : Nat := 4983230072969 + 3 ^ 40 * 3532519 * 2
def baseEnd_3532519 : Nat := 22393582322715675763787

theorem tailTrace_3532519 : CollatzResearch.WordTrace tailWord_3532519 prefixEnd_3532519 22393582322715675763787 := by
  unfold tailWord_3532519
  simp only [CollatzResearch.WordTrace]
  refine ⟨128841552689294444058648611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85894368459529629372432407 128841552689294444058648611)
  ·
    refine ⟨193262329033941666087972917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128841552689294444058648611 193262329033941666087972917)
    ·
      refine ⟨18118343346932031195747461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193262329033941666087972917 18118343346932031195747461)
      ·
        refine ⟨3397189377549755849202649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18118343346932031195747461 3397189377549755849202649)
        ·
          refine ⟨2547892033162316886901987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3397189377549755849202649 2547892033162316886901987)
          ·
            refine ⟨3821838049743475330352981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2547892033162316886901987 3821838049743475330352981)
            ·
              refine ⟨22393582322715675763787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3821838049743475330352981 22393582322715675763787)
              ·
                rfl

theorem cell23_3532519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 9].length) (baseStart_3532519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532519 prefixEnd_3532519 := by exact prefixLift 3532519
  have htrace : WordTrace (prefixWord ++ tailWord_3532519) baseStart_3532519 baseEnd_3532519 := by
    simpa [prefixWord, tailWord_3532519, baseEnd_3532519] using wordTrace_append hprefix tailTrace_3532519
  have hstable : (prefixWord ++ tailWord_3532519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532519).length < 2 ^ (prefixWord ++ tailWord_3532519).sum := by decide
  have hdescent : baseEnd_3532519 < baseStart_3532519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532545 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 2, 6]
def baseStart_3532545 : Nat := 118140960795 + 3532545 * 2 ^ 59
def prefixEnd_3532545 : Nat := 4983230072969 + 3 ^ 40 * 3532545 * 2
def baseEnd_3532545 : Nat := 604631172878995545047209

theorem tailTrace_3532545 : CollatzResearch.WordTrace tailWord_3532545 prefixEnd_3532545 604631172878995545047209 := by
  unfold tailWord_3532545
  simp only [CollatzResearch.WordTrace]
  refine ⟨128842500987200250499095089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85895000658133500332730059 128842500987200250499095089)
  ·
    refine ⟨96631875740400187874321317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128842500987200250499095089 96631875740400187874321317)
    ·
      refine ⟨18118476701325035226435247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96631875740400187874321317 18118476701325035226435247)
      ·
        refine ⟨27177715051987552839652871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18118476701325035226435247 27177715051987552839652871)
        ·
          refine ⟨40766572577981329259479307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27177715051987552839652871 40766572577981329259479307)
          ·
            refine ⟨61149858866971993889218961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40766572577981329259479307 61149858866971993889218961)
            ·
              refine ⟨45862394150228995416914221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61149858866971993889218961 45862394150228995416914221)
              ·
                refine ⟨17198397806335873281342833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45862394150228995416914221 17198397806335873281342833)
                ·
                  refine ⟨12898798354751904961007125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17198397806335873281342833 12898798354751904961007125)
                  ·
                    refine ⟨604631172878995545047209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12898798354751904961007125 604631172878995545047209)
                    ·
                      rfl

theorem cell23_3532545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_3532545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532545 prefixEnd_3532545 := by exact prefixLift 3532545
  have htrace : WordTrace (prefixWord ++ tailWord_3532545) baseStart_3532545 baseEnd_3532545 := by
    simpa [prefixWord, tailWord_3532545, baseEnd_3532545] using wordTrace_append hprefix tailTrace_3532545
  have hstable : (prefixWord ++ tailWord_3532545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532545).length < 2 ^ (prefixWord ++ tailWord_3532545).sum := by decide
  have hdescent : baseEnd_3532545 < baseStart_3532545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532546 : List Nat := [3, 4, 1, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_3532546 : Nat := 118140960795 + 3532546 * 2 ^ 59
def prefixEnd_3532546 : Nat := 4983230072969 + 3 ^ 40 * 3532546 * 2
def baseEnd_3532546 : Nat := 1813894032117641131229123

theorem tailTrace_3532546 : CollatzResearch.WordTrace tailWord_3532546 prefixEnd_3532546 1813894032117641131229123 := by
  unfold tailWord_3532546
  simp only [CollatzResearch.WordTrace]
  refine ⟨32210634365049156917470373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85895024973464418446587661 32210634365049156917470373)
  ·
    refine ⟨6039493943446716922025695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32210634365049156917470373 6039493943446716922025695)
    ·
      refine ⟨9059240915170075383038543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6039493943446716922025695 9059240915170075383038543)
      ·
        refine ⟨13588861372755113074557815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9059240915170075383038543 13588861372755113074557815)
        ·
          refine ⟨20383292059132669611836723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13588861372755113074557815 20383292059132669611836723)
          ·
            refine ⟨30574938088699004417755085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20383292059132669611836723 30574938088699004417755085)
            ·
              refine ⟨11465601783262126656658157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30574938088699004417755085 11465601783262126656658157)
              ·
                refine ⟨4299600668723297496246809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11465601783262126656658157 4299600668723297496246809)
                ·
                  refine ⟨3224700501542473122185107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4299600668723297496246809 3224700501542473122185107)
                  ·
                    refine ⟨4837050752313709683277661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3224700501542473122185107 4837050752313709683277661)
                    ·
                      refine ⟨1813894032117641131229123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4837050752313709683277661 1813894032117641131229123)
                      ·
                        rfl

theorem cell23_3532546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_3532546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532546 prefixEnd_3532546 := by exact prefixLift 3532546
  have htrace : WordTrace (prefixWord ++ tailWord_3532546) baseStart_3532546 baseEnd_3532546 := by
    simpa [prefixWord, tailWord_3532546, baseEnd_3532546] using wordTrace_append hprefix tailTrace_3532546
  have hstable : (prefixWord ++ tailWord_3532546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532546).length < 2 ^ (prefixWord ++ tailWord_3532546).sum := by decide
  have hdescent : baseEnd_3532546 < baseStart_3532546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532555 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 5]
def baseStart_3532555 : Nat := 118140960795 + 3532555 * 2 ^ 59
def prefixEnd_3532555 : Nat := 4983230072969 + 3 ^ 40 * 3532555 * 2
def baseEnd_3532555 : Nat := 1813898653443531596016581

theorem tailTrace_3532555 : CollatzResearch.WordTrace tailWord_3532555 prefixEnd_3532555 1813898653443531596016581 := by
  unfold tailWord_3532555
  simp only [CollatzResearch.WordTrace]
  refine ⟨128842865717164022206959119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85895243811442681471306079 128842865717164022206959119)
  ·
    refine ⟨193264298575746033310438679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128842865717164022206959119 193264298575746033310438679)
    ·
      refine ⟨289896447863619049965658019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193264298575746033310438679 289896447863619049965658019)
      ·
        refine ⟨434844671795428574948487029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289896447863619049965658019 434844671795428574948487029)
        ·
          refine ⟨40766687980821428901420659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 434844671795428574948487029 40766687980821428901420659)
          ·
            refine ⟨61150031971232143352130989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40766687980821428901420659 61150031971232143352130989)
            ·
              refine ⟨22931261989212053757049121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61150031971232143352130989 22931261989212053757049121)
              ·
                refine ⟨17198446491909040317786841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22931261989212053757049121 17198446491909040317786841)
                ·
                  refine ⟨12898834868931780238340131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17198446491909040317786841 12898834868931780238340131)
                  ·
                    refine ⟨19348252303397670357510197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12898834868931780238340131 19348252303397670357510197)
                    ·
                      refine ⟨1813898653443531596016581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19348252303397670357510197 1813898653443531596016581)
                      ·
                        rfl

theorem cell23_3532555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 5].length) (baseStart_3532555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532555 prefixEnd_3532555 := by exact prefixLift 3532555
  have htrace : WordTrace (prefixWord ++ tailWord_3532555) baseStart_3532555 baseEnd_3532555 := by
    simpa [prefixWord, tailWord_3532555, baseEnd_3532555] using wordTrace_append hprefix tailTrace_3532555
  have hstable : (prefixWord ++ tailWord_3532555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532555).length < 2 ^ (prefixWord ++ tailWord_3532555).sum := by decide
  have hdescent : baseEnd_3532555 < baseStart_3532555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532602 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3]
def baseStart_3532602 : Nat := 118140960795 + 3532602 * 2 ^ 59
def prefixEnd_3532602 : Nat := 4983230072969 + 3 ^ 40 * 3532602 * 2
def baseEnd_3532602 : Nat := 1813922787034292912128865

theorem tailTrace_3532602 : CollatzResearch.WordTrace tailWord_3532602 prefixEnd_3532602 1813922787034292912128865 := by
  unfold tailWord_3532602
  simp only [CollatzResearch.WordTrace]
  refine ⟨32211144986998437308480015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85896386631995832822613373 32211144986998437308480015)
  ·
    refine ⟨48316717480497655962720023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32211144986998437308480015 48316717480497655962720023)
    ·
      refine ⟨72475076220746483944080035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48316717480497655962720023 72475076220746483944080035)
      ·
        refine ⟨108712614331119725916120053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72475076220746483944080035 108712614331119725916120053)
        ·
          refine ⟨10191807593542474304636255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108712614331119725916120053 10191807593542474304636255)
          ·
            refine ⟨15287711390313711456954383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10191807593542474304636255 15287711390313711456954383)
            ·
              refine ⟨22931567085470567185431575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15287711390313711456954383 22931567085470567185431575)
              ·
                refine ⟨34397350628205850778147363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22931567085470567185431575 34397350628205850778147363)
                ·
                  refine ⟨51596025942308776167221045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34397350628205850778147363 51596025942308776167221045)
                  ·
                    refine ⟨4837127432091447765676973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51596025942308776167221045 4837127432091447765676973)
                    ·
                      refine ⟨1813922787034292912128865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4837127432091447765676973 1813922787034292912128865)
                      ·
                        rfl

theorem cell23_3532602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_3532602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532602 prefixEnd_3532602 := by exact prefixLift 3532602
  have htrace : WordTrace (prefixWord ++ tailWord_3532602) baseStart_3532602 baseEnd_3532602 := by
    simpa [prefixWord, tailWord_3532602, baseEnd_3532602] using wordTrace_append hprefix tailTrace_3532602
  have hstable : (prefixWord ++ tailWord_3532602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532602).length < 2 ^ (prefixWord ++ tailWord_3532602).sum := by decide
  have hdescent : baseEnd_3532602 < baseStart_3532602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532615 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_3532615 : Nat := 118140960795 + 3532615 * 2 ^ 59
def prefixEnd_3532615 : Nat := 4983230072969 + 3 ^ 40 * 3532615 * 2
def baseEnd_3532615 : Nat := 1813929462282801361266305

theorem tailTrace_3532615 : CollatzResearch.WordTrace tailWord_3532615 prefixEnd_3532615 1813929462282801361266305 := by
  unfold tailWord_3532615
  simp only [CollatzResearch.WordTrace]
  refine ⟨128845054096946652454143299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85896702731297768302762199 128845054096946652454143299)
  ·
    refine ⟨193267581145419978681214949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128845054096946652454143299 193267581145419978681214949)
    ·
      refine ⟨36237671464766246002727803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193267581145419978681214949 36237671464766246002727803)
      ·
        refine ⟨54356507197149369004091705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36237671464766246002727803 54356507197149369004091705)
        ·
          refine ⟨40767380397862026753068779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54356507197149369004091705 40767380397862026753068779)
          ·
            refine ⟨61151070596793040129603169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40767380397862026753068779 61151070596793040129603169)
            ·
              refine ⟨45863302947594780097202377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61151070596793040129603169 45863302947594780097202377)
              ·
                refine ⟨34397477210696085072901783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45863302947594780097202377 34397477210696085072901783)
                ·
                  refine ⟨51596215816044127609352675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34397477210696085072901783 51596215816044127609352675)
                  ·
                    refine ⟨77394323724066191414029013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51596215816044127609352675 77394323724066191414029013)
                    ·
                      refine ⟨1813929462282801361266305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77394323724066191414029013 1813929462282801361266305)
                      ·
                        rfl

theorem cell23_3532615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_3532615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532615 prefixEnd_3532615 := by exact prefixLift 3532615
  have htrace : WordTrace (prefixWord ++ tailWord_3532615) baseStart_3532615 baseEnd_3532615 := by
    simpa [prefixWord, tailWord_3532615, baseEnd_3532615] using wordTrace_append hprefix tailTrace_3532615
  have hstable : (prefixWord ++ tailWord_3532615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532615).length < 2 ^ (prefixWord ++ tailWord_3532615).sum := by decide
  have hdescent : baseEnd_3532615 < baseStart_3532615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532703 : List Nat := [1, 1, 2, 5, 4, 1, 1, 1, 3, 4]
def baseStart_3532703 : Nat := 118140960795 + 3532703 * 2 ^ 59
def prefixEnd_3532703 : Nat := 4983230072969 + 3 ^ 40 * 3532703 * 2
def baseEnd_3532703 : Nat := 604658216193465672321967

theorem tailTrace_3532703 : CollatzResearch.WordTrace tailWord_3532703 prefixEnd_3532703 604658216193465672321967 := by
  unfold tailWord_3532703
  simp only [CollatzResearch.WordTrace]
  refine ⟨128848263720627843483346763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85898842480418562322231175 128848263720627843483346763)
  ·
    refine ⟨193272395580941765225020145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128848263720627843483346763 193272395580941765225020145)
    ·
      refine ⟨144954296685706323918765109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193272395580941765225020145 144954296685706323918765109)
      ·
        refine ⟨13589465314284967867384229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 144954296685706323918765109 13589465314284967867384229)
        ·
          refine ⟨2548024746428431475134543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13589465314284967867384229 2548024746428431475134543)
          ·
            refine ⟨3822037119642647212701815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2548024746428431475134543 3822037119642647212701815)
            ·
              refine ⟨5733055679463970819052723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3822037119642647212701815 5733055679463970819052723)
              ·
                refine ⟨8599583519195956228579085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5733055679463970819052723 8599583519195956228579085)
                ·
                  refine ⟨3224843819698483585717157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8599583519195956228579085 3224843819698483585717157)
                  ·
                    refine ⟨604658216193465672321967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3224843819698483585717157 604658216193465672321967)
                    ·
                      rfl

theorem cell23_3532703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 1, 1, 3, 4].length) (baseStart_3532703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532703 prefixEnd_3532703 := by exact prefixLift 3532703
  have htrace : WordTrace (prefixWord ++ tailWord_3532703) baseStart_3532703 baseEnd_3532703 := by
    simpa [prefixWord, tailWord_3532703, baseEnd_3532703] using wordTrace_append hprefix tailTrace_3532703
  have hstable : (prefixWord ++ tailWord_3532703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532703).length < 2 ^ (prefixWord ++ tailWord_3532703).sum := by decide
  have hdescent : baseEnd_3532703 < baseStart_3532703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532719 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 4, 3, 2]
def baseStart_3532719 : Nat := 118140960795 + 3532719 * 2 ^ 59
def prefixEnd_3532719 : Nat := 4983230072969 + 3 ^ 40 * 3532719 * 2
def baseEnd_3532719 : Nat := 1813982864270868954365827

theorem tailTrace_3532719 : CollatzResearch.WordTrace tailWord_3532719 prefixEnd_3532719 1813982864270868954365827 := by
  unfold tailWord_3532719
  simp only [CollatzResearch.WordTrace]
  refine ⟨128848847288569878215929211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85899231525713252143952807 128848847288569878215929211)
  ·
    refine ⟨193273270932854817323893817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128848847288569878215929211 193273270932854817323893817)
    ·
      refine ⟨144954953199641112992920363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193273270932854817323893817 144954953199641112992920363)
      ·
        refine ⟨217432429799461669489380545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144954953199641112992920363 217432429799461669489380545)
        ·
          refine ⟨163074322349596252117035409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217432429799461669489380545 163074322349596252117035409)
          ·
            refine ⟨122305741762197189087776557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163074322349596252117035409 122305741762197189087776557)
            ·
              refine ⟨45864653160823945907916209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122305741762197189087776557 45864653160823945907916209)
              ·
                refine ⟨34398489870617959430937157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45864653160823945907916209 34398489870617959430937157)
                ·
                  refine ⟨6449716850740867393300717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34398489870617959430937157 6449716850740867393300717)
                  ·
                    refine ⟨2418643819027825272487769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6449716850740867393300717 2418643819027825272487769)
                    ·
                      refine ⟨1813982864270868954365827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2418643819027825272487769 1813982864270868954365827)
                      ·
                        rfl

theorem cell23_3532719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 3, 2].length) (baseStart_3532719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532719 prefixEnd_3532719 := by exact prefixLift 3532719
  have htrace : WordTrace (prefixWord ++ tailWord_3532719) baseStart_3532719 baseEnd_3532719 := by
    simpa [prefixWord, tailWord_3532719, baseEnd_3532719] using wordTrace_append hprefix tailTrace_3532719
  have hstable : (prefixWord ++ tailWord_3532719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532719).length < 2 ^ (prefixWord ++ tailWord_3532719).sum := by decide
  have hdescent : baseEnd_3532719 < baseStart_3532719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532736 : List Nat := [2, 1, 1, 2, 3, 2, 4, 1, 2, 3, 2]
def baseStart_3532736 : Nat := 118140960795 + 3532736 * 2 ^ 59
def prefixEnd_3532736 : Nat := 4983230072969 + 3 ^ 40 * 3532736 * 2
def baseEnd_3532736 : Nat := 1813991593441995387853249

theorem tailTrace_3532736 : CollatzResearch.WordTrace tailWord_3532736 prefixEnd_3532736 1813991593441995387853249 := by
  unfold tailWord_3532736
  simp only [CollatzResearch.WordTrace]
  refine ⟨64424733664754145059649031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85899644886338860079532041 64424733664754145059649031)
  ·
    refine ⟨96637100497131217589473547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64424733664754145059649031 96637100497131217589473547)
    ·
      refine ⟨144955650745696826384210321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96637100497131217589473547 144955650745696826384210321)
      ·
        refine ⟨108716738059272619788157741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144955650745696826384210321 108716738059272619788157741)
        ·
          refine ⟨40768776772227232420559153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108716738059272619788157741 40768776772227232420559153)
          ·
            refine ⟨30576582579170424315419365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40768776772227232420559153 30576582579170424315419365)
            ·
              refine ⟨5733109233594454559141131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30576582579170424315419365 5733109233594454559141131)
              ·
                refine ⟨8599663850391681838711697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5733109233594454559141131 8599663850391681838711697)
                ·
                  refine ⟨6449747887793761379033773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8599663850391681838711697 6449747887793761379033773)
                  ·
                    refine ⟨2418655457922660517137665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6449747887793761379033773 2418655457922660517137665)
                    ·
                      refine ⟨1813991593441995387853249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2418655457922660517137665 1813991593441995387853249)
                      ·
                        rfl

theorem cell23_3532736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 2, 3, 2].length) (baseStart_3532736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532736 prefixEnd_3532736 := by exact prefixLift 3532736
  have htrace : WordTrace (prefixWord ++ tailWord_3532736) baseStart_3532736 baseEnd_3532736 := by
    simpa [prefixWord, tailWord_3532736, baseEnd_3532736] using wordTrace_append hprefix tailTrace_3532736
  have hstable : (prefixWord ++ tailWord_3532736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532736).length < 2 ^ (prefixWord ++ tailWord_3532736).sum := by decide
  have hdescent : baseEnd_3532736 < baseStart_3532736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532769 : List Nat := [1, 2, 3, 1, 2, 1, 3, 2, 3, 2, 3]
def baseStart_3532769 : Nat := 118140960795 + 3532769 * 2 ^ 59
def prefixEnd_3532769 : Nat := 4983230072969 + 3 ^ 40 * 3532769 * 2
def baseEnd_3532769 : Nat := 1814008538303593758740597

theorem tailTrace_3532769 : CollatzResearch.WordTrace tailWord_3532769 prefixEnd_3532769 1814008538303593758740597 := by
  unfold tailWord_3532769
  simp only [CollatzResearch.WordTrace]
  refine ⟨128850670938388736755249361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85900447292259157836832907 128850670938388736755249361)
  ·
    refine ⟨96638003203791552566437021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128850670938388736755249361 96638003203791552566437021)
    ·
      refine ⟨36239251201421832212413883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96638003203791552566437021 36239251201421832212413883)
      ·
        refine ⟨54358876802132748318620825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36239251201421832212413883 54358876802132748318620825)
        ·
          refine ⟨40769157601599561238965619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54358876802132748318620825 40769157601599561238965619)
          ·
            refine ⟨61153736402399341858448429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40769157601599561238965619 61153736402399341858448429)
            ·
              refine ⟨22932651150899753196918161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61153736402399341858448429 22932651150899753196918161)
              ·
                refine ⟨17199488363174814897688621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22932651150899753196918161 17199488363174814897688621)
                ·
                  refine ⟨6449808136190555586633233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17199488363174814897688621 6449808136190555586633233)
                  ·
                    refine ⟨4837356102142916689974925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6449808136190555586633233 4837356102142916689974925)
                    ·
                      refine ⟨1814008538303593758740597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4837356102142916689974925 1814008538303593758740597)
                      ·
                        rfl

theorem cell23_3532769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_3532769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532769 prefixEnd_3532769 := by exact prefixLift 3532769
  have htrace : WordTrace (prefixWord ++ tailWord_3532769) baseStart_3532769 baseEnd_3532769 := by
    simpa [prefixWord, tailWord_3532769, baseEnd_3532769] using wordTrace_append hprefix tailTrace_3532769
  have hstable : (prefixWord ++ tailWord_3532769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532769).length < 2 ^ (prefixWord ++ tailWord_3532769).sum := by decide
  have hdescent : baseEnd_3532769 < baseStart_3532769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532810 : List Nat := [3, 1, 2, 2, 5, 1, 1, 2, 2, 4]
def baseStart_3532810 : Nat := 118140960795 + 3532810 * 2 ^ 59
def prefixEnd_3532810 : Nat := 4983230072969 + 3 ^ 40 * 3532810 * 2
def baseEnd_3532810 : Nat := 604676530336809366109303

theorem tailTrace_3532810 : CollatzResearch.WordTrace tailWord_3532810 prefixEnd_3532810 604676530336809366109303 := by
  unfold tailWord_3532810
  simp only [CollatzResearch.WordTrace]
  refine ⟨32213041582810050189372971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85901444220826800504994589 32213041582810050189372971)
  ·
    refine ⟨48319562374215075284059457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32213041582810050189372971 48319562374215075284059457)
    ·
      refine ⟨36239671780661306463044593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48319562374215075284059457 36239671780661306463044593)
      ·
        refine ⟨27179753835495979847283445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36239671780661306463044593 27179753835495979847283445)
        ·
          refine ⟨2548101922077748110682823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27179753835495979847283445 2548101922077748110682823)
          ·
            refine ⟨3822152883116622166024235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2548101922077748110682823 3822152883116622166024235)
            ·
              refine ⟨5733229324674933249036353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3822152883116622166024235 5733229324674933249036353)
              ·
                refine ⟨4299921993506199936777265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5733229324674933249036353 4299921993506199936777265)
                ·
                  refine ⟨3224941495129649952582949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4299921993506199936777265 3224941495129649952582949)
                  ·
                    refine ⟨604676530336809366109303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3224941495129649952582949 604676530336809366109303)
                    ·
                      rfl

theorem cell23_3532810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_3532810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532810 prefixEnd_3532810 := by exact prefixLift 3532810
  have htrace : WordTrace (prefixWord ++ tailWord_3532810) baseStart_3532810 baseEnd_3532810 := by
    simpa [prefixWord, tailWord_3532810, baseEnd_3532810] using wordTrace_append hprefix tailTrace_3532810
  have hstable : (prefixWord ++ tailWord_3532810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532810).length < 2 ^ (prefixWord ++ tailWord_3532810).sum := by decide
  have hdescent : baseEnd_3532810 < baseStart_3532810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532833 : List Nat := [1, 2, 3, 2, 4, 2, 1, 1, 1, 3, 3]
def baseStart_3532833 : Nat := 118140960795 + 3532833 * 2 ^ 59
def prefixEnd_3532833 : Nat := 4983230072969 + 3 ^ 40 * 3532833 * 2
def baseEnd_3532833 : Nat := 1814041401065481508340303

theorem tailTrace_3532833 : CollatzResearch.WordTrace tailWord_3532833 prefixEnd_3532833 1814041401065481508340303 := by
  unfold tailWord_3532833
  simp only [CollatzResearch.WordTrace]
  refine ⟨128853005210156875685579153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85902003473437917123719435 128853005210156875685579153)
  ·
    refine ⟨96639753907617656764184365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128853005210156875685579153 96639753907617656764184365)
    ·
      refine ⟨36239907715356621286569137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96639753907617656764184365 36239907715356621286569137)
      ·
        refine ⟨27179930786517465964926853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36239907715356621286569137 27179930786517465964926853)
        ·
          refine ⟨5096237022472024868423785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27179930786517465964926853 5096237022472024868423785)
          ·
            refine ⟨3822177766854018651317839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5096237022472024868423785 3822177766854018651317839)
            ·
              refine ⟨5733266650281027976976759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3822177766854018651317839 5733266650281027976976759)
              ·
                refine ⟨8599899975421541965465139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5733266650281027976976759 8599899975421541965465139)
                ·
                  refine ⟨12899849963132312948197709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8599899975421541965465139 12899849963132312948197709)
                  ·
                    refine ⟨4837443736174617355574141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12899849963132312948197709 4837443736174617355574141)
                    ·
                      refine ⟨1814041401065481508340303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4837443736174617355574141 1814041401065481508340303)
                      ·
                        rfl

theorem cell23_3532833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_3532833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532833 prefixEnd_3532833 := by exact prefixLift 3532833
  have htrace : WordTrace (prefixWord ++ tailWord_3532833) baseStart_3532833 baseEnd_3532833 := by
    simpa [prefixWord, tailWord_3532833, baseEnd_3532833] using wordTrace_append hprefix tailTrace_3532833
  have hstable : (prefixWord ++ tailWord_3532833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532833).length < 2 ^ (prefixWord ++ tailWord_3532833).sum := by decide
  have hdescent : baseEnd_3532833 < baseStart_3532833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532840 : List Nat := [2, 1, 5, 3, 2, 1, 2, 7]
def baseStart_3532840 : Nat := 118140960795 + 3532840 * 2 ^ 59
def prefixEnd_3532840 : Nat := 4983230072969 + 3 ^ 40 * 3532840 * 2
def baseEnd_3532840 : Nat := 67186851682594925220473

theorem tailTrace_3532840 : CollatzResearch.WordTrace tailWord_3532840 prefixEnd_3532840 67186851682594925220473 := by
  unfold tailWord_3532840
  simp only [CollatzResearch.WordTrace]
  refine ⟨64426630260565757940541987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85902173680754343920722649 64426630260565757940541987)
  ·
    refine ⟨96639945390848636910812981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64426630260565757940541987 96639945390848636910812981)
    ·
      refine ⟨9059994880392059710388717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96639945390848636910812981 9059994880392059710388717)
      ·
        refine ⟨3397498080147022391395769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9059994880392059710388717 3397498080147022391395769)
        ·
          refine ⟨2548123560110266793546827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3397498080147022391395769 2548123560110266793546827)
          ·
            refine ⟨3822185340165400190320241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2548123560110266793546827 3822185340165400190320241)
            ·
              refine ⟨2866639005124050142740181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3822185340165400190320241 2866639005124050142740181)
              ·
                refine ⟨67186851682594925220473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2866639005124050142740181 67186851682594925220473)
                ·
                  rfl

theorem cell23_3532840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 7].length) (baseStart_3532840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532840 prefixEnd_3532840 := by exact prefixLift 3532840
  have htrace : WordTrace (prefixWord ++ tailWord_3532840) baseStart_3532840 baseEnd_3532840 := by
    simpa [prefixWord, tailWord_3532840, baseEnd_3532840] using wordTrace_append hprefix tailTrace_3532840
  have hstable : (prefixWord ++ tailWord_3532840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532840).length < 2 ^ (prefixWord ++ tailWord_3532840).sum := by decide
  have hdescent : baseEnd_3532840 < baseStart_3532840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532873 : List Nat := [1, 2, 1, 1, 2, 2, 4, 4, 2, 2, 2]
def baseStart_3532873 : Nat := 118140960795 + 3532873 * 2 ^ 59
def prefixEnd_3532873 : Nat := 4983230072969 + 3 ^ 40 * 3532873 * 2
def baseEnd_3532873 : Nat := 1814061940291661351840119

theorem tailTrace_3532873 : CollatzResearch.WordTrace tailWord_3532873 prefixEnd_3532873 1814061940291661351840119 := by
  unfold tailWord_3532873
  simp only [CollatzResearch.WordTrace]
  refine ⟨128854464130011962517035273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85902976086674641678023515 128854464130011962517035273)
  ·
    refine ⟨96640848097508971887776455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128854464130011962517035273 96640848097508971887776455)
    ·
      refine ⟨144961272146263457831664683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96640848097508971887776455 144961272146263457831664683)
      ·
        refine ⟨217441908219395186747497025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144961272146263457831664683 217441908219395186747497025)
        ·
          refine ⟨163081431164546390060622769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217441908219395186747497025 163081431164546390060622769)
          ·
            refine ⟨122311073373409792545467077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163081431164546390060622769 122311073373409792545467077)
            ·
              refine ⟨22933326257514336102275077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122311073373409792545467077 22933326257514336102275077)
              ·
                refine ⟨4299998673283938019176577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22933326257514336102275077 4299998673283938019176577)
                ·
                  refine ⟨3224999004962953514382433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4299998673283938019176577 3224999004962953514382433)
                  ·
                    refine ⟨2418749253722215135786825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3224999004962953514382433 2418749253722215135786825)
                    ·
                      refine ⟨1814061940291661351840119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2418749253722215135786825 1814061940291661351840119)
                      ·
                        rfl

theorem cell23_3532873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 2, 2].length) (baseStart_3532873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532873 prefixEnd_3532873 := by exact prefixLift 3532873
  have htrace : WordTrace (prefixWord ++ tailWord_3532873) baseStart_3532873 baseEnd_3532873 := by
    simpa [prefixWord, tailWord_3532873, baseEnd_3532873] using wordTrace_append hprefix tailTrace_3532873
  have hstable : (prefixWord ++ tailWord_3532873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532873).length < 2 ^ (prefixWord ++ tailWord_3532873).sum := by decide
  have hdescent : baseEnd_3532873 < baseStart_3532873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532889 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 1, 5, 3]
def baseStart_3532889 : Nat := 118140960795 + 3532889 * 2 ^ 59
def prefixEnd_3532889 : Nat := 4983230072969 + 3 ^ 40 * 3532889 * 2
def baseEnd_3532889 : Nat := 1814070155982133289240045

theorem tailTrace_3532889 : CollatzResearch.WordTrace tailWord_3532889 prefixEnd_3532889 1814070155982133289240045 := by
  unfold tailWord_3532889
  simp only [CollatzResearch.WordTrace]
  refine ⟨128855047697953997249617721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85903365131969331499745147 128855047697953997249617721)
  ·
    refine ⟨96641285773465497937213291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128855047697953997249617721 96641285773465497937213291)
    ·
      refine ⟨144961928660198246905819937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96641285773465497937213291 144961928660198246905819937)
      ·
        refine ⟨108721446495148685179364953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144961928660198246905819937 108721446495148685179364953)
        ·
          refine ⟨81541084871361513884523715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108721446495148685179364953 81541084871361513884523715)
          ·
            refine ⟨122311627307042270826785573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81541084871361513884523715 122311627307042270826785573)
            ·
              refine ⟨22933430120070425780022295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122311627307042270826785573 22933430120070425780022295)
              ·
                refine ⟨34400145180105638670033443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22933430120070425780022295 34400145180105638670033443)
                ·
                  refine ⟨51600217770158458005050165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34400145180105638670033443 51600217770158458005050165)
                  ·
                    refine ⟨4837520415952355437973453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 51600217770158458005050165 4837520415952355437973453)
                    ·
                      refine ⟨1814070155982133289240045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4837520415952355437973453 1814070155982133289240045)
                      ·
                        rfl

theorem cell23_3532889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_3532889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532889 prefixEnd_3532889 := by exact prefixLift 3532889
  have htrace : WordTrace (prefixWord ++ tailWord_3532889) baseStart_3532889 baseEnd_3532889 := by
    simpa [prefixWord, tailWord_3532889, baseEnd_3532889] using wordTrace_append hprefix tailTrace_3532889
  have hstable : (prefixWord ++ tailWord_3532889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532889).length < 2 ^ (prefixWord ++ tailWord_3532889).sum := by decide
  have hdescent : baseEnd_3532889 < baseStart_3532889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532919 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 5]
def baseStart_3532919 : Nat := 118140960795 + 3532919 * 2 ^ 59
def prefixEnd_3532919 : Nat := 4983230072969 + 3 ^ 40 * 3532919 * 2
def baseEnd_3532919 : Nat := 1814085560401768171864907

theorem tailTrace_3532919 : CollatzResearch.WordTrace tailWord_3532919 prefixEnd_3532919 1814085560401768171864907 := by
  unfold tailWord_3532919
  simp only [CollatzResearch.WordTrace]
  refine ⟨128856141887845312373209811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85904094591896874915473207 128856141887845312373209811)
  ·
    refine ⟨193284212831767968559814717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128856141887845312373209811 193284212831767968559814717)
    ·
      refine ⟨72481579811912988209930519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193284212831767968559814717 72481579811912988209930519)
      ·
        refine ⟨108722369717869482314895779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72481579811912988209930519 108722369717869482314895779)
        ·
          refine ⟨163083554576804223472343669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108722369717869482314895779 163083554576804223472343669)
          ·
            refine ⟨15289083241575395950532219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163083554576804223472343669 15289083241575395950532219)
            ·
              refine ⟨22933624862363093925798329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15289083241575395950532219 22933624862363093925798329)
              ·
                refine ⟨17200218646772320444348747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22933624862363093925798329 17200218646772320444348747)
                ·
                  refine ⟨25800327970158480666523121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17200218646772320444348747 25800327970158480666523121)
                  ·
                    refine ⟨19350245977618860499892341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25800327970158480666523121 19350245977618860499892341)
                    ·
                      refine ⟨1814085560401768171864907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19350245977618860499892341 1814085560401768171864907)
                      ·
                        rfl

theorem cell23_3532919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_3532919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532919 prefixEnd_3532919 := by exact prefixLift 3532919
  have htrace : WordTrace (prefixWord ++ tailWord_3532919) baseStart_3532919 baseEnd_3532919 := by
    simpa [prefixWord, tailWord_3532919, baseEnd_3532919] using wordTrace_append hprefix tailTrace_3532919
  have hstable : (prefixWord ++ tailWord_3532919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532919).length < 2 ^ (prefixWord ++ tailWord_3532919).sum := by decide
  have hdescent : baseEnd_3532919 < baseStart_3532919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532936 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3532936 : Nat := 118140960795 + 3532936 * 2 ^ 59
def prefixEnd_3532936 : Nat := 4983230072969 + 3 ^ 40 * 3532936 * 2
def baseEnd_3532936 : Nat := 1814094289572894605352329

theorem tailTrace_3532936 : CollatzResearch.WordTrace tailWord_3532936 prefixEnd_3532936 1814094289572894605352329 := by
  unfold tailWord_3532936
  simp only [CollatzResearch.WordTrace]
  refine ⟨64428380964391862138289331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85904507952522482851052441 64428380964391862138289331)
  ·
    refine ⟨96642571446587793207433997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64428380964391862138289331 96642571446587793207433997)
    ·
      refine ⟨36240964292470422452787749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96642571446587793207433997 36240964292470422452787749)
      ·
        refine ⟨6795180804838204209897703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36240964292470422452787749 6795180804838204209897703)
        ·
          refine ⟨10192771207257306314846555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6795180804838204209897703 10192771207257306314846555)
          ·
            refine ⟨15289156810885959472269833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10192771207257306314846555 15289156810885959472269833)
            ·
              refine ⟨11466867608164469604202375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15289156810885959472269833 11466867608164469604202375)
              ·
                refine ⟨17200301412246704406303563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11466867608164469604202375 17200301412246704406303563)
                ·
                  refine ⟨25800452118370056609455345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17200301412246704406303563 25800452118370056609455345)
                  ·
                    refine ⟨19350339088777542457091509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25800452118370056609455345 19350339088777542457091509)
                    ·
                      refine ⟨1814094289572894605352329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19350339088777542457091509 1814094289572894605352329)
                      ·
                        rfl

theorem cell23_3532936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3532936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532936 prefixEnd_3532936 := by exact prefixLift 3532936
  have htrace : WordTrace (prefixWord ++ tailWord_3532936) baseStart_3532936 baseEnd_3532936 := by
    simpa [prefixWord, tailWord_3532936, baseEnd_3532936] using wordTrace_append hprefix tailTrace_3532936
  have hstable : (prefixWord ++ tailWord_3532936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532936).length < 2 ^ (prefixWord ++ tailWord_3532936).sum := by decide
  have hdescent : baseEnd_3532936 < baseStart_3532936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532946 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_3532946 : Nat := 118140960795 + 3532946 * 2 ^ 59
def prefixEnd_3532946 : Nat := 4983230072969 + 3 ^ 40 * 3532946 * 2
def baseEnd_3532946 : Nat := 1814099424379439566227283

theorem tailTrace_3532946 : CollatzResearch.WordTrace tailWord_3532946 prefixEnd_3532946 1814099424379439566227283 := by
  unfold tailWord_3532946
  simp only [CollatzResearch.WordTrace]
  refine ⟨32214281664686873996110673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85904751105831663989628461 32214281664686873996110673)
  ·
    refine ⟨24160711248515155497083005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32214281664686873996110673 24160711248515155497083005)
    ·
      refine ⟨9060266718193183311406127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24160711248515155497083005 9060266718193183311406127)
      ·
        refine ⟨13590400077289774967109191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9060266718193183311406127 13590400077289774967109191)
        ·
          refine ⟨20385600115934662450663787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13590400077289774967109191 20385600115934662450663787)
          ·
            refine ⟨30578400173901993675995681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20385600115934662450663787 30578400173901993675995681)
            ·
              refine ⟨22933800130426495256996761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30578400173901993675995681 22933800130426495256996761)
              ·
                refine ⟨17200350097819871442747571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22933800130426495256996761 17200350097819871442747571)
                ·
                  refine ⟨25800525146729807164121357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17200350097819871442747571 25800525146729807164121357)
                  ·
                    refine ⟨9675196930023677686545509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25800525146729807164121357 9675196930023677686545509)
                    ·
                      refine ⟨1814099424379439566227283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9675196930023677686545509 1814099424379439566227283)
                      ·
                        rfl

theorem cell23_3532946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_3532946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532946 prefixEnd_3532946 := by exact prefixLift 3532946
  have htrace : WordTrace (prefixWord ++ tailWord_3532946) baseStart_3532946 baseEnd_3532946 := by
    simpa [prefixWord, tailWord_3532946, baseEnd_3532946] using wordTrace_append hprefix tailTrace_3532946
  have hstable : (prefixWord ++ tailWord_3532946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532946).length < 2 ^ (prefixWord ++ tailWord_3532946).sum := by decide
  have hdescent : baseEnd_3532946 < baseStart_3532946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532986 : List Nat := [3, 1, 1, 1, 2, 2, 5, 2, 6]
def baseStart_3532986 : Nat := 118140960795 + 3532986 * 2 ^ 59
def prefixEnd_3532986 : Nat := 4983230072969 + 3 ^ 40 * 3532986 * 2
def baseEnd_3532986 : Nat := 201568884845068823303011

theorem tailTrace_3532986 : CollatzResearch.WordTrace tailWord_3532986 prefixEnd_3532986 201568884845068823303011 := by
  unfold tailWord_3532986
  simp only [CollatzResearch.WordTrace]
  refine ⟨32214646394650645703974703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85905723719068388543932541 32214646394650645703974703)
  ·
    refine ⟨48321969591975968555962055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32214646394650645703974703 48321969591975968555962055)
    ·
      refine ⟨72482954387963952833943083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48321969591975968555962055 72482954387963952833943083)
      ·
        refine ⟨108724431581945929250914625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72482954387963952833943083 108724431581945929250914625)
        ·
          refine ⟨81543323686459446938185969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108724431581945929250914625 81543323686459446938185969)
          ·
            refine ⟨61157492764844585203639477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81543323686459446938185969 61157492764844585203639477)
            ·
              refine ⟨5733514946704179862841201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61157492764844585203639477 5733514946704179862841201)
              ·
                refine ⟨4300136210028134897130901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5733514946704179862841201 4300136210028134897130901)
                ·
                  refine ⟨201568884845068823303011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4300136210028134897130901 201568884845068823303011)
                  ·
                    rfl

theorem cell23_3532986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 6].length) (baseStart_3532986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532986 prefixEnd_3532986 := by exact prefixLift 3532986
  have htrace : WordTrace (prefixWord ++ tailWord_3532986) baseStart_3532986 baseEnd_3532986 := by
    simpa [prefixWord, tailWord_3532986, baseEnd_3532986] using wordTrace_append hprefix tailTrace_3532986
  have hstable : (prefixWord ++ tailWord_3532986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532986).length < 2 ^ (prefixWord ++ tailWord_3532986).sum := by decide
  have hdescent : baseEnd_3532986 < baseStart_3532986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3532990 : List Nat := [4, 2, 1, 1, 4, 1, 2, 1, 3, 4]
def baseStart_3532990 : Nat := 118140960795 + 3532990 * 2 ^ 59
def prefixEnd_3532990 : Nat := 4983230072969 + 3 ^ 40 * 3532990 * 2
def baseEnd_3532990 : Nat := 604707339176079131359027

theorem tailTrace_3532990 : CollatzResearch.WordTrace tailWord_3532990 prefixEnd_3532990 604707339176079131359027 := by
  unfold tailWord_3532990
  simp only [CollatzResearch.WordTrace]
  refine ⟨16107341433823511437380553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85905820980392060999362949 16107341433823511437380553)
  ·
    refine ⟨12080506075367633578035415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16107341433823511437380553 12080506075367633578035415)
    ·
      refine ⟨18120759113051450367053123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12080506075367633578035415 18120759113051450367053123)
      ·
        refine ⟨27181138669577175550579685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18120759113051450367053123 27181138669577175550579685)
        ·
          refine ⟨5096463500545720415733691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27181138669577175550579685 5096463500545720415733691)
          ·
            refine ⟨7644695250818580623600537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5096463500545720415733691 7644695250818580623600537)
            ·
              refine ⟨5733521438113935467700403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7644695250818580623600537 5733521438113935467700403)
              ·
                refine ⟨8600282157170903201550605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5733521438113935467700403 8600282157170903201550605)
                ·
                  refine ⟨3225105808939088700581477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8600282157170903201550605 3225105808939088700581477)
                  ·
                    refine ⟨604707339176079131359027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3225105808939088700581477 604707339176079131359027)
                    ·
                      rfl

theorem cell23_3532990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_3532990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3532990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3532990 prefixEnd_3532990 := by exact prefixLift 3532990
  have htrace : WordTrace (prefixWord ++ tailWord_3532990) baseStart_3532990 baseEnd_3532990 := by
    simpa [prefixWord, tailWord_3532990, baseEnd_3532990] using wordTrace_append hprefix tailTrace_3532990
  have hstable : (prefixWord ++ tailWord_3532990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3532990).length < 2 ^ (prefixWord ++ tailWord_3532990).sum := by decide
  have hdescent : baseEnd_3532990 < baseStart_3532990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3532990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533009 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 7]
def baseStart_3533009 : Nat := 118140960795 + 3533009 * 2 ^ 59
def prefixEnd_3533009 : Nat := 4983230072969 + 3 ^ 40 * 3533009 * 2
def baseEnd_3533009 : Nat := 1814131773660672819739493

theorem tailTrace_3533009 : CollatzResearch.WordTrace tailWord_3533009 prefixEnd_3533009 1814131773660672819739493 := by
  unfold tailWord_3533009
  simp only [CollatzResearch.WordTrace]
  refine ⟨128859424457519257743986081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85906282971679505162657387 128859424457519257743986081)
  ·
    refine ⟨96644568343139443307989561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128859424457519257743986081 96644568343139443307989561)
    ·
      refine ⟨72483426257354582480992171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96644568343139443307989561 72483426257354582480992171)
      ·
        refine ⟨108725139386031873721488257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72483426257354582480992171 108725139386031873721488257)
        ·
          refine ⟨81543854539523905291116193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108725139386031873721488257 81543854539523905291116193)
          ·
            refine ⟨61157890904642928968337145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81543854539523905291116193 61157890904642928968337145)
            ·
              refine ⟨45868418178482196726252859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61157890904642928968337145 45868418178482196726252859)
              ·
                refine ⟨68802627267723295089379289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45868418178482196726252859 68802627267723295089379289)
                ·
                  refine ⟨51601970450792471317034467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68802627267723295089379289 51601970450792471317034467)
                  ·
                    refine ⟨77402955676188706975551701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51601970450792471317034467 77402955676188706975551701)
                    ·
                      refine ⟨1814131773660672819739493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77402955676188706975551701 1814131773660672819739493)
                      ·
                        rfl

theorem cell23_3533009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 7].length) (baseStart_3533009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533009 prefixEnd_3533009 := by exact prefixLift 3533009
  have htrace : WordTrace (prefixWord ++ tailWord_3533009) baseStart_3533009 baseEnd_3533009 := by
    simpa [prefixWord, tailWord_3533009, baseEnd_3533009] using wordTrace_append hprefix tailTrace_3533009
  have hstable : (prefixWord ++ tailWord_3533009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533009).length < 2 ^ (prefixWord ++ tailWord_3533009).sum := by decide
  have hdescent : baseEnd_3533009 < baseStart_3533009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533023 : List Nat := [1, 1, 2, 3, 2, 1, 1, 5, 2, 3, 2]
def baseStart_3533023 : Nat := 118140960795 + 3533023 * 2 ^ 59
def prefixEnd_3533023 : Nat := 4983230072969 + 3 ^ 40 * 3533023 * 2
def baseEnd_3533023 : Nat := 1814138962389835764964429

theorem tailTrace_3533023 : CollatzResearch.WordTrace tailWord_3533023 prefixEnd_3533023 1814138962389835764964429 := by
  unfold tailWord_3533023
  simp only [CollatzResearch.WordTrace]
  refine ⟨128859935079468538134995723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85906623386312358756663815 128859935079468538134995723)
  ·
    refine ⟨193289902619202807202493585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128859935079468538134995723 193289902619202807202493585)
    ·
      refine ⟨144967426964402105401870189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193289902619202807202493585 144967426964402105401870189)
      ·
        refine ⟨54362785111650789525701321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 144967426964402105401870189 54362785111650789525701321)
        ·
          refine ⟨40772088833738092144275991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54362785111650789525701321 40772088833738092144275991)
          ·
            refine ⟨61158133250607138216413987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40772088833738092144275991 61158133250607138216413987)
            ·
              refine ⟨91737199875910707324620981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61158133250607138216413987 91737199875910707324620981)
              ·
                refine ⟨8600362488366628811683217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 91737199875910707324620981 8600362488366628811683217)
                ·
                  refine ⟨6450271866274971608762413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8600362488366628811683217 6450271866274971608762413)
                  ·
                    refine ⟨2418851949853114353285905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6450271866274971608762413 2418851949853114353285905)
                    ·
                      refine ⟨1814138962389835764964429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2418851949853114353285905 1814138962389835764964429)
                      ·
                        rfl

theorem cell23_3533023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_3533023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533023 prefixEnd_3533023 := by exact prefixLift 3533023
  have htrace : WordTrace (prefixWord ++ tailWord_3533023) baseStart_3533023 baseEnd_3533023 := by
    simpa [prefixWord, tailWord_3533023, baseEnd_3533023] using wordTrace_append hprefix tailTrace_3533023
  have hstable : (prefixWord ++ tailWord_3533023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533023).length < 2 ^ (prefixWord ++ tailWord_3533023).sum := by decide
  have hdescent : baseEnd_3533023 < baseStart_3533023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533056 : List Nat := [2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 5]
def baseStart_3533056 : Nat := 118140960795 + 3533056 * 2 ^ 59
def prefixEnd_3533056 : Nat := 4983230072969 + 3 ^ 40 * 3533056 * 2
def baseEnd_3533056 : Nat := 1814155907251434135851777

theorem tailTrace_3533056 : CollatzResearch.WordTrace tailWord_3533056 prefixEnd_3533056 1814155907251434135851777 := by
  unfold tailWord_3533056
  simp only [CollatzResearch.WordTrace]
  refine ⟨64430569344174492385473511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85907425792232656513964681 64430569344174492385473511)
  ·
    refine ⟨96645854016261738578210267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64430569344174492385473511 96645854016261738578210267)
    ·
      refine ⟨144968781024392607867315401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96645854016261738578210267 144968781024392607867315401)
      ·
        refine ⟨108726585768294455900486551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144968781024392607867315401 108726585768294455900486551)
        ·
          refine ⟨163089878652441683850729827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108726585768294455900486551 163089878652441683850729827)
          ·
            refine ⟨244634817978662525776094741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163089878652441683850729827 244634817978662525776094741)
            ·
              refine ⟨11467257092749805895754441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 244634817978662525776094741 11467257092749805895754441)
              ·
                refine ⟨8600442819562354421815831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11467257092749805895754441 8600442819562354421815831)
                ·
                  refine ⟨12900664229343531632723747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8600442819562354421815831 12900664229343531632723747)
                  ·
                    refine ⟨19350996344015297449085621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12900664229343531632723747 19350996344015297449085621)
                    ·
                      refine ⟨1814155907251434135851777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19350996344015297449085621 1814155907251434135851777)
                      ·
                        rfl

theorem cell23_3533056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_3533056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533056 prefixEnd_3533056 := by exact prefixLift 3533056
  have htrace : WordTrace (prefixWord ++ tailWord_3533056) baseStart_3533056 baseEnd_3533056 := by
    simpa [prefixWord, tailWord_3533056, baseEnd_3533056] using wordTrace_append hprefix tailTrace_3533056
  have hstable : (prefixWord ++ tailWord_3533056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533056).length < 2 ^ (prefixWord ++ tailWord_3533056).sum := by decide
  have hdescent : baseEnd_3533056 < baseStart_3533056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533066 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_3533066 : Nat := 118140960795 + 3533066 * 2 ^ 59
def prefixEnd_3533066 : Nat := 4983230072969 + 3 ^ 40 * 3533066 * 2
def baseEnd_3533066 : Nat := 1814161042057979096726731

theorem tailTrace_3533066 : CollatzResearch.WordTrace tailWord_3533066 prefixEnd_3533066 1814161042057979096726731 := by
  unfold tailWord_3533066
  simp only [CollatzResearch.WordTrace]
  refine ⟨32215375854578189119702763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85907668945541837652540701 32215375854578189119702763)
  ·
    refine ⟨48323063781867283679554145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32215375854578189119702763 48323063781867283679554145)
    ·
      refine ⟨36242297836400462759665609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48323063781867283679554145 36242297836400462759665609)
      ·
        refine ⟨27181723377300347069749207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36242297836400462759665609 27181723377300347069749207)
        ·
          refine ⟨40772585065950520604623811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27181723377300347069749207 40772585065950520604623811)
          ·
            refine ⟨61158877598925780906935717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40772585065950520604623811 61158877598925780906935717)
            ·
              refine ⟨11467289549798583920050447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61158877598925780906935717 11467289549798583920050447)
              ·
                refine ⟨17200934324697875880075671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11467289549798583920050447 17200934324697875880075671)
                ·
                  refine ⟨25801401487046813820113507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17200934324697875880075671 25801401487046813820113507)
                  ·
                    refine ⟨38702102230570220730170261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25801401487046813820113507 38702102230570220730170261)
                    ·
                      refine ⟨1814161042057979096726731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38702102230570220730170261 1814161042057979096726731)
                      ·
                        rfl

theorem cell23_3533066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_3533066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533066 prefixEnd_3533066 := by exact prefixLift 3533066
  have htrace : WordTrace (prefixWord ++ tailWord_3533066) baseStart_3533066 baseEnd_3533066 := by
    simpa [prefixWord, tailWord_3533066, baseEnd_3533066] using wordTrace_append hprefix tailTrace_3533066
  have hstable : (prefixWord ++ tailWord_3533066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533066).length < 2 ^ (prefixWord ++ tailWord_3533066).sum := by decide
  have hdescent : baseEnd_3533066 < baseStart_3533066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533070 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2]
def baseStart_3533070 : Nat := 118140960795 + 3533070 * 2 ^ 59
def prefixEnd_3533070 : Nat := 4983230072969 + 3 ^ 40 * 3533070 * 2
def baseEnd_3533070 : Nat := 1814163095980597081076713

theorem tailTrace_3533070 : CollatzResearch.WordTrace tailWord_3533070 prefixEnd_3533070 1814163095980597081076713 := by
  unfold tailWord_3533070
  simp only [CollatzResearch.WordTrace]
  refine ⟨16107706163787283145244583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85907766206865510107971109 16107706163787283145244583)
  ·
    refine ⟨24161559245680924717866875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16107706163787283145244583 24161559245680924717866875)
    ·
      refine ⟨36242338868521387076800313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24161559245680924717866875 36242338868521387076800313)
      ·
        refine ⟨27181754151391040307600235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36242338868521387076800313 27181754151391040307600235)
        ·
          refine ⟨40772631227086560461400353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27181754151391040307600235 40772631227086560461400353)
          ·
            refine ⟨30579473420314920346050265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40772631227086560461400353 30579473420314920346050265)
            ·
              refine ⟨22934605065236190259537699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30579473420314920346050265 22934605065236190259537699)
              ·
                refine ⟨34401907597854285389306549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22934605065236190259537699 34401907597854285389306549)
                ·
                  refine ⟨3225178837298839255247489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34401907597854285389306549 3225178837298839255247489)
                  ·
                    refine ⟨2418884127974129441435617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3225178837298839255247489 2418884127974129441435617)
                    ·
                      refine ⟨1814163095980597081076713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2418884127974129441435617 1814163095980597081076713)
                      ·
                        rfl

theorem cell23_3533070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_3533070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533070 prefixEnd_3533070 := by exact prefixLift 3533070
  have htrace : WordTrace (prefixWord ++ tailWord_3533070) baseStart_3533070 baseEnd_3533070 := by
    simpa [prefixWord, tailWord_3533070, baseEnd_3533070] using wordTrace_append hprefix tailTrace_3533070
  have hstable : (prefixWord ++ tailWord_3533070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533070).length < 2 ^ (prefixWord ++ tailWord_3533070).sum := by decide
  have hdescent : baseEnd_3533070 < baseStart_3533070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533073 : List Nat := [1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 3]
def baseStart_3533073 : Nat := 118140960795 + 3533073 * 2 ^ 59
def prefixEnd_3533073 : Nat := 4983230072969 + 3 ^ 40 * 3533073 * 2
def baseEnd_3533073 : Nat := 1814164636422560569339199

theorem tailTrace_3533073 : CollatzResearch.WordTrace tailWord_3533073 prefixEnd_3533073 1814164636422560569339199 := by
  unfold tailWord_3533073
  simp only [CollatzResearch.WordTrace]
  refine ⟨128861758729287396674315873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85907839152858264449543915 128861758729287396674315873)
  ·
    refine ⟨96646319046965547505736905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128861758729287396674315873 96646319046965547505736905)
    ·
      refine ⟨72484739285224160629302679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96646319046965547505736905 72484739285224160629302679)
      ·
        refine ⟨108727108927836240943954019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72484739285224160629302679 108727108927836240943954019)
        ·
          refine ⟨163090663391754361415931029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108727108927836240943954019 163090663391754361415931029)
          ·
            refine ⟨7644874846488485691371767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163090663391754361415931029 7644874846488485691371767)
            ·
              refine ⟨11467312269732728537057651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7644874846488485691371767 11467312269732728537057651)
              ·
                refine ⟨17200968404599092805586477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11467312269732728537057651 17200968404599092805586477)
                ·
                  refine ⟨6450363151724659802094929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17200968404599092805586477 6450363151724659802094929)
                  ·
                    refine ⟨4837772363793494851571197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6450363151724659802094929 4837772363793494851571197)
                    ·
                      refine ⟨1814164636422560569339199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4837772363793494851571197 1814164636422560569339199)
                      ·
                        rfl

theorem cell23_3533073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 3].length) (baseStart_3533073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533073 prefixEnd_3533073 := by exact prefixLift 3533073
  have htrace : WordTrace (prefixWord ++ tailWord_3533073) baseStart_3533073 baseEnd_3533073 := by
    simpa [prefixWord, tailWord_3533073, baseEnd_3533073] using wordTrace_append hprefix tailTrace_3533073
  have hstable : (prefixWord ++ tailWord_3533073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533073).length < 2 ^ (prefixWord ++ tailWord_3533073).sum := by decide
  have hdescent : baseEnd_3533073 < baseStart_3533073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533090 : List Nat := [3, 3, 1, 1, 3, 3, 1, 1, 1, 1, 5]
def baseStart_3533090 : Nat := 118140960795 + 3533090 * 2 ^ 59
def prefixEnd_3533090 : Nat := 4983230072969 + 3 ^ 40 * 3533090 * 2
def baseEnd_3533090 : Nat := 1814173365593687002826621

theorem tailTrace_3533090 : CollatzResearch.WordTrace tailWord_3533090 prefixEnd_3533090 1814173365593687002826621 := by
  unfold tailWord_3533090
  simp only [CollatzResearch.WordTrace]
  refine ⟨32215594692556452144421181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85908252513483872385123149 32215594692556452144421181)
  ·
    refine ⟨12080848009708669554157943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32215594692556452144421181 12080848009708669554157943)
    ·
      refine ⟨18121272014563004331236915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12080848009708669554157943 18121272014563004331236915)
      ·
        refine ⟨27181908021844506496855373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18121272014563004331236915 27181908021844506496855373)
        ·
          refine ⟨10193215508191689936320765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27181908021844506496855373 10193215508191689936320765)
          ·
            refine ⟨3822455815571883726120287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10193215508191689936320765 3822455815571883726120287)
            ·
              refine ⟨5733683723357825589180431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3822455815571883726120287 5733683723357825589180431)
              ·
                refine ⟨8600525585036738383770647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5733683723357825589180431 8600525585036738383770647)
                ·
                  refine ⟨12900788377555107575655971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8600525585036738383770647 12900788377555107575655971)
                  ·
                    refine ⟨19351182566332661363483957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12900788377555107575655971 19351182566332661363483957)
                    ·
                      refine ⟨1814173365593687002826621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19351182566332661363483957 1814173365593687002826621)
                      ·
                        rfl

theorem cell23_3533090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_3533090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533090 prefixEnd_3533090 := by exact prefixLift 3533090
  have htrace : WordTrace (prefixWord ++ tailWord_3533090) baseStart_3533090 baseEnd_3533090 := by
    simpa [prefixWord, tailWord_3533090, baseEnd_3533090] using wordTrace_append hprefix tailTrace_3533090
  have hstable : (prefixWord ++ tailWord_3533090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533090).length < 2 ^ (prefixWord ++ tailWord_3533090).sum := by decide
  have hdescent : baseEnd_3533090 < baseStart_3533090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533098 : List Nat := [3, 1, 4, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_3533098 : Nat := 118140960795 + 3533098 * 2 ^ 59
def prefixEnd_3533098 : Nat := 4983230072969 + 3 ^ 40 * 3533098 * 2
def baseEnd_3533098 : Nat := 1814177473438922971526585

theorem tailTrace_3533098 : CollatzResearch.WordTrace tailWord_3533098 prefixEnd_3533098 1814177473438922971526585 := by
  unfold tailWord_3533098
  simp only [CollatzResearch.WordTrace]
  refine ⟨32215667638549206485993987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85908447036131217295983965 32215667638549206485993987)
  ·
    refine ⟨48323501457823809728990981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32215667638549206485993987 48323501457823809728990981)
    ·
      refine ⟨9060656523341964324185809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48323501457823809728990981 9060656523341964324185809)
      ·
        refine ⟨6795492392506473243139357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9060656523341964324185809 6795492392506473243139357)
        ·
          refine ⟨2548309647189927466177259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6795492392506473243139357 2548309647189927466177259)
          ·
            refine ⟨3822464470784891199265889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2548309647189927466177259 3822464470784891199265889)
            ·
              refine ⟨2866848353088668399449417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3822464470784891199265889 2866848353088668399449417)
              ·
                refine ⟨2150136264816501299587063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2866848353088668399449417 2150136264816501299587063)
                ·
                  refine ⟨3225204397224751949380595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150136264816501299587063 3225204397224751949380595)
                  ·
                    refine ⟨4837806595837127924070893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3225204397224751949380595 4837806595837127924070893)
                    ·
                      refine ⟨1814177473438922971526585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4837806595837127924070893 1814177473438922971526585)
                      ·
                        rfl

theorem cell23_3533098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_3533098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533098 prefixEnd_3533098 := by exact prefixLift 3533098
  have htrace : WordTrace (prefixWord ++ tailWord_3533098) baseStart_3533098 baseEnd_3533098 := by
    simpa [prefixWord, tailWord_3533098, baseEnd_3533098] using wordTrace_append hprefix tailTrace_3533098
  have hstable : (prefixWord ++ tailWord_3533098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533098).length < 2 ^ (prefixWord ++ tailWord_3533098).sum := by decide
  have hdescent : baseEnd_3533098 < baseStart_3533098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533103 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 4, 1, 3]
def baseStart_3533103 : Nat := 118140960795 + 3533103 * 2 ^ 59
def prefixEnd_3533103 : Nat := 4983230072969 + 3 ^ 40 * 3533103 * 2
def baseEnd_3533103 : Nat := 1814180040842195451964061

theorem tailTrace_3533103 : CollatzResearch.WordTrace tailWord_3533103 prefixEnd_3533103 1814180040842195451964061 := by
  unfold tailWord_3533103
  simp only [CollatzResearch.WordTrace]
  refine ⟨128862852919178711797907963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85908568612785807865271975 128862852919178711797907963)
  ·
    refine ⟨193294279378768067696861945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128862852919178711797907963 193294279378768067696861945)
    ·
      refine ⟨144970709534076050772646459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193294279378768067696861945 144970709534076050772646459)
      ·
        refine ⟨217456064301114076158969689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144970709534076050772646459 217456064301114076158969689)
        ·
          refine ⟨163092048225835557119227267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217456064301114076158969689 163092048225835557119227267)
          ·
            refine ⟨244638072338753335678840901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163092048225835557119227267 244638072338753335678840901)
            ·
              refine ⟨45869638563516250439782669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 244638072338753335678840901 45869638563516250439782669)
              ·
                refine ⟨17201114461318593914918501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45869638563516250439782669 17201114461318593914918501)
                ·
                  refine ⟨3225208961497236359047219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17201114461318593914918501 3225208961497236359047219)
                  ·
                    refine ⟨4837813442245854538570829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3225208961497236359047219 4837813442245854538570829)
                    ·
                      refine ⟨1814180040842195451964061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4837813442245854538570829 1814180040842195451964061)
                      ·
                        rfl

theorem cell23_3533103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 4, 1, 3].length) (baseStart_3533103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533103 prefixEnd_3533103 := by exact prefixLift 3533103
  have htrace : WordTrace (prefixWord ++ tailWord_3533103) baseStart_3533103 baseEnd_3533103 := by
    simpa [prefixWord, tailWord_3533103, baseEnd_3533103] using wordTrace_append hprefix tailTrace_3533103
  have hstable : (prefixWord ++ tailWord_3533103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533103).length < 2 ^ (prefixWord ++ tailWord_3533103).sum := by decide
  have hdescent : baseEnd_3533103 < baseStart_3533103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533146 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5]
def baseStart_3533146 : Nat := 118140960795 + 3533146 * 2 ^ 59
def prefixEnd_3533146 : Nat := 4983230072969 + 3 ^ 40 * 3533146 * 2
def baseEnd_3533146 : Nat := 1814202120510338783726363

theorem tailTrace_3533146 : CollatzResearch.WordTrace tailWord_3533146 prefixEnd_3533146 1814202120510338783726363 := by
  unfold tailWord_3533146
  simp only [CollatzResearch.WordTrace]
  refine ⟨32216105314505732535430823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85909614172015286761148861 32216105314505732535430823)
  ·
    refine ⟨48324157971758598803146235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32216105314505732535430823 48324157971758598803146235)
    ·
      refine ⟨72486236957637898204719353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48324157971758598803146235 72486236957637898204719353)
      ·
        refine ⟨54364677718228423653539515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72486236957637898204719353 54364677718228423653539515)
        ·
          refine ⟨81547016577342635480309273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54364677718228423653539515 81547016577342635480309273)
          ·
            refine ⟨61160262433006976610231955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81547016577342635480309273 61160262433006976610231955)
            ·
              refine ⟨91740393649510464915347933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61160262433006976610231955 91740393649510464915347933)
              ·
                refine ⟨34402647618566424343255475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91740393649510464915347933 34402647618566424343255475)
                ·
                  refine ⟨51603971427849636514883213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34402647618566424343255475 51603971427849636514883213)
                  ·
                    refine ⟨19351489285443613693081205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51603971427849636514883213 19351489285443613693081205)
                    ·
                      refine ⟨1814202120510338783726363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19351489285443613693081205 1814202120510338783726363)
                      ·
                        rfl

theorem cell23_3533146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_3533146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533146 prefixEnd_3533146 := by exact prefixLift 3533146
  have htrace : WordTrace (prefixWord ++ tailWord_3533146) baseStart_3533146 baseEnd_3533146 := by
    simpa [prefixWord, tailWord_3533146, baseEnd_3533146] using wordTrace_append hprefix tailTrace_3533146
  have hstable : (prefixWord ++ tailWord_3533146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533146).length < 2 ^ (prefixWord ++ tailWord_3533146).sum := by decide
  have hdescent : baseEnd_3533146 < baseStart_3533146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533154 : List Nat := [3, 3, 2, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_3533154 : Nat := 118140960795 + 3533154 * 2 ^ 59
def prefixEnd_3533154 : Nat := 4983230072969 + 3 ^ 40 * 3533154 * 2
def baseEnd_3533154 : Nat := 1814206228355574752426327

theorem tailTrace_3533154 : CollatzResearch.WordTrace tailWord_3533154 prefixEnd_3533154 1814206228355574752426327 := by
  unfold tailWord_3533154
  simp only [CollatzResearch.WordTrace]
  refine ⟨32216178260498486877003629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85909808694662631672009677 32216178260498486877003629)
  ·
    refine ⟨12081066847686932578876361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32216178260498486877003629 12081066847686932578876361)
    ·
      refine ⟨9060800135765199434157271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12081066847686932578876361 9060800135765199434157271)
      ·
        refine ⟨13591200203647799151235907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9060800135765199434157271 13591200203647799151235907)
        ·
          refine ⟨20386800305471698726853861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13591200203647799151235907 20386800305471698726853861)
          ·
            refine ⟨3822525057275943511285099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20386800305471698726853861 3822525057275943511285099)
            ·
              refine ⟨5733787585913915266927649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3822525057275943511285099 5733787585913915266927649)
              ·
                refine ⟨4300340689435436450195737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5733787585913915266927649 4300340689435436450195737)
                ·
                  refine ⟨3225255517076577337646803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4300340689435436450195737 3225255517076577337646803)
                  ·
                    refine ⟨4837883275614866006470205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3225255517076577337646803 4837883275614866006470205)
                    ·
                      refine ⟨1814206228355574752426327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4837883275614866006470205 1814206228355574752426327)
                      ·
                        rfl

theorem cell23_3533154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_3533154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533154 prefixEnd_3533154 := by exact prefixLift 3533154
  have htrace : WordTrace (prefixWord ++ tailWord_3533154) baseStart_3533154 baseEnd_3533154 := by
    simpa [prefixWord, tailWord_3533154, baseEnd_3533154] using wordTrace_append hprefix tailTrace_3533154
  have hstable : (prefixWord ++ tailWord_3533154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533154).length < 2 ^ (prefixWord ++ tailWord_3533154).sum := by decide
  have hdescent : baseEnd_3533154 < baseStart_3533154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533217 : List Nat := [1, 2, 3, 5, 1, 2, 1, 1, 7]
def baseStart_3533217 : Nat := 118140960795 + 3533217 * 2 ^ 59
def prefixEnd_3533217 : Nat := 4983230072969 + 3 ^ 40 * 3533217 * 2
def baseEnd_3533217 : Nat := 201582064181867556215393

theorem tailTrace_3533217 : CollatzResearch.WordTrace tailWord_3533217 prefixEnd_3533217 201582064181867556215393 := by
  unfold tailWord_3533217
  simp only [CollatzResearch.WordTrace]
  refine ⟨128867010840765709267557905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85911340560510472845038603 128867010840765709267557905)
  ·
    refine ⟨96650258130574281950668429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128867010840765709267557905 96650258130574281950668429)
    ·
      refine ⟨36243846798965355731500661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96650258130574281950668429 36243846798965355731500661)
      ·
        refine ⟨3397860637403002099828187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36243846798965355731500661 3397860637403002099828187)
        ·
          refine ⟨5096790956104503149742281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3397860637403002099828187 5096790956104503149742281)
          ·
            refine ⟨3822593217078377362306711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5096790956104503149742281 3822593217078377362306711)
            ·
              refine ⟨5733889825617566043460067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3822593217078377362306711 5733889825617566043460067)
              ·
                refine ⟨8600834738426349065190101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5733889825617566043460067 8600834738426349065190101)
                ·
                  refine ⟨201582064181867556215393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8600834738426349065190101 201582064181867556215393)
                  ·
                    rfl

theorem cell23_3533217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 7].length) (baseStart_3533217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533217 prefixEnd_3533217 := by exact prefixLift 3533217
  have htrace : WordTrace (prefixWord ++ tailWord_3533217) baseStart_3533217 baseEnd_3533217 := by
    simpa [prefixWord, tailWord_3533217, baseEnd_3533217] using wordTrace_append hprefix tailTrace_3533217
  have hstable : (prefixWord ++ tailWord_3533217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533217).length < 2 ^ (prefixWord ++ tailWord_3533217).sum := by decide
  have hdescent : baseEnd_3533217 < baseStart_3533217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533223 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_3533223 : Nat := 118140960795 + 3533223 * 2 ^ 59
def prefixEnd_3533223 : Nat := 4983230072969 + 3 ^ 40 * 3533223 * 2
def baseEnd_3533223 : Nat := 1814241658520734982463509

theorem tailTrace_3533223 : CollatzResearch.WordTrace tailWord_3533223 prefixEnd_3533223 1814241658520734982463509 := by
  unfold tailWord_3533223
  simp only [CollatzResearch.WordTrace]
  refine ⟨128867229678743972292276323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85911486452495981528184215 128867229678743972292276323)
  ·
    refine ⟨193300844518115958438414485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128867229678743972292276323 193300844518115958438414485)
    ·
      refine ⟨9060977086786685551800679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 193300844518115958438414485 9060977086786685551800679)
      ·
        refine ⟨13591465630180028327701019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9060977086786685551800679 13591465630180028327701019)
        ·
          refine ⟨20387198445270042491551529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13591465630180028327701019 20387198445270042491551529)
          ·
            refine ⟨15290398833952531868663647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20387198445270042491551529 15290398833952531868663647)
            ·
              refine ⟨22935598250928797802995471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15290398833952531868663647 22935598250928797802995471)
              ·
                refine ⟨34403397376393196704493207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22935598250928797802995471 34403397376393196704493207)
                ·
                  refine ⟨51605096064589795056739811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34403397376393196704493207 51605096064589795056739811)
                  ·
                    refine ⟨77407644096884692585109717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51605096064589795056739811 77407644096884692585109717)
                    ·
                      refine ⟨1814241658520734982463509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77407644096884692585109717 1814241658520734982463509)
                      ·
                        rfl

theorem cell23_3533223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_3533223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533223 prefixEnd_3533223 := by exact prefixLift 3533223
  have htrace : WordTrace (prefixWord ++ tailWord_3533223) baseStart_3533223 baseEnd_3533223 := by
    simpa [prefixWord, tailWord_3533223, baseEnd_3533223] using wordTrace_append hprefix tailTrace_3533223
  have hstable : (prefixWord ++ tailWord_3533223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533223).length < 2 ^ (prefixWord ++ tailWord_3533223).sum := by decide
  have hdescent : baseEnd_3533223 < baseStart_3533223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533270 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_3533270 : Nat := 118140960795 + 3533270 * 2 ^ 59
def prefixEnd_3533270 : Nat := 4983230072969 + 3 ^ 40 * 3533270 * 2
def baseEnd_3533270 : Nat := 1814265792111496298575793

theorem tailTrace_3533270 : CollatzResearch.WordTrace tailWord_3533270 prefixEnd_3533270 1814265792111496298575793 := by
  unfold tailWord_3533270
  simp only [CollatzResearch.WordTrace]
  refine ⟨8054308994348356207452329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85912629273049132879491509 8054308994348356207452329)
  ·
    refine ⟨6040731745761267155589247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8054308994348356207452329 6040731745761267155589247)
    ·
      refine ⟨9061097618641900733383871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6040731745761267155589247 9061097618641900733383871)
      ·
        refine ⟨13591646427962851100075807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9061097618641900733383871 13591646427962851100075807)
        ·
          refine ⟨20387469641944276650113711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13591646427962851100075807 20387469641944276650113711)
          ·
            refine ⟨30581204462916414975170567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20387469641944276650113711 30581204462916414975170567)
            ·
              refine ⟨45871806694374622462755851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30581204462916414975170567 45871806694374622462755851)
              ·
                refine ⟨68807710041561933694133777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45871806694374622462755851 68807710041561933694133777)
                ·
                  refine ⟨51605782531171450270600333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68807710041561933694133777 51605782531171450270600333)
                  ·
                    refine ⟨19352168449189293851475125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51605782531171450270600333 19352168449189293851475125)
                    ·
                      refine ⟨1814265792111496298575793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19352168449189293851475125 1814265792111496298575793)
                      ·
                        rfl

theorem cell23_3533270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_3533270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533270 prefixEnd_3533270 := by exact prefixLift 3533270
  have htrace : WordTrace (prefixWord ++ tailWord_3533270) baseStart_3533270 baseEnd_3533270 := by
    simpa [prefixWord, tailWord_3533270, baseEnd_3533270] using wordTrace_append hprefix tailTrace_3533270
  have hstable : (prefixWord ++ tailWord_3533270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533270).length < 2 ^ (prefixWord ++ tailWord_3533270).sum := by decide
  have hdescent : baseEnd_3533270 < baseStart_3533270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533290 : List Nat := [3, 1, 3, 1, 3, 1, 2, 3, 6]
def baseStart_3533290 : Nat := 118140960795 + 3533290 * 2 ^ 59
def prefixEnd_3533290 : Nat := 4983230072969 + 3 ^ 40 * 3533290 * 2
def baseEnd_3533290 : Nat := 201586229080509580036189

theorem tailTrace_3533290 : CollatzResearch.WordTrace tailWord_3533290 prefixEnd_3533290 201586229080509580036189 := by
  unfold tailWord_3533290
  simp only [CollatzResearch.WordTrace]
  refine ⟨32217418342375310683741331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85913115579667495156643549 32217418342375310683741331)
  ·
    refine ⟨48326127513562966025611997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32217418342375310683741331 48326127513562966025611997)
    ·
      refine ⟨18122297817586112259604499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48326127513562966025611997 18122297817586112259604499)
      ·
        refine ⟨27183446726379168389406749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18122297817586112259604499 27183446726379168389406749)
        ·
          refine ⟨10193792522392188146027531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27183446726379168389406749 10193792522392188146027531)
          ·
            refine ⟨15290688783588282219041297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10193792522392188146027531 15290688783588282219041297)
            ·
              refine ⟨11468016587691211664280973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15290688783588282219041297 11468016587691211664280973)
              ·
                refine ⟨4300506220384204374105365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11468016587691211664280973 4300506220384204374105365)
                ·
                  refine ⟨201586229080509580036189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4300506220384204374105365 201586229080509580036189)
                  ·
                    rfl

theorem cell23_3533290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 6].length) (baseStart_3533290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533290 prefixEnd_3533290 := by exact prefixLift 3533290
  have htrace : WordTrace (prefixWord ++ tailWord_3533290) baseStart_3533290 baseEnd_3533290 := by
    simpa [prefixWord, tailWord_3533290, baseEnd_3533290] using wordTrace_append hprefix tailTrace_3533290
  have hstable : (prefixWord ++ tailWord_3533290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533290).length < 2 ^ (prefixWord ++ tailWord_3533290).sum := by decide
  have hdescent : baseEnd_3533290 < baseStart_3533290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533301 : List Nat := [1, 3, 5, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_3533301 : Nat := 118140960795 + 3533301 * 2 ^ 59
def prefixEnd_3533301 : Nat := 4983230072969 + 3 ^ 40 * 3533301 * 2
def baseEnd_3533301 : Nat := 1814281710011785677288151

theorem tailTrace_3533301 : CollatzResearch.WordTrace tailWord_3533301 prefixEnd_3533301 1814281710011785677288151 := by
  unfold tailWord_3533301
  simp only [CollatzResearch.WordTrace]
  refine ⟨128870074572461391613615757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85913383048307594409077171 128870074572461391613615757)
  ·
    refine ⟨48326277964673021855105909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128870074572461391613615757 48326277964673021855105909)
    ·
      refine ⟨4530588559188095798916179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48326277964673021855105909 4530588559188095798916179)
      ·
        refine ⟨6795882838782143698374269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4530588559188095798916179 6795882838782143698374269)
        ·
          refine ⟨2548456064543303886890351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6795882838782143698374269 2548456064543303886890351)
          ·
            refine ⟨3822684096814955830335527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2548456064543303886890351 3822684096814955830335527)
            ·
              refine ⟨5734026145222433745503291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3822684096814955830335527 5734026145222433745503291)
              ·
                refine ⟨8601039217833650618254937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5734026145222433745503291 8601039217833650618254937)
                ·
                  refine ⟨6450779413375237963691203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8601039217833650618254937 6450779413375237963691203)
                  ·
                    refine ⟨9676169120062856945536805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6450779413375237963691203 9676169120062856945536805)
                    ·
                      refine ⟨1814281710011785677288151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9676169120062856945536805 1814281710011785677288151)
                      ·
                        rfl

theorem cell23_3533301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_3533301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533301 prefixEnd_3533301 := by exact prefixLift 3533301
  have htrace : WordTrace (prefixWord ++ tailWord_3533301) baseStart_3533301 baseEnd_3533301 := by
    simpa [prefixWord, tailWord_3533301, baseEnd_3533301] using wordTrace_append hprefix tailTrace_3533301
  have hstable : (prefixWord ++ tailWord_3533301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533301).length < 2 ^ (prefixWord ++ tailWord_3533301).sum := by decide
  have hdescent : baseEnd_3533301 < baseStart_3533301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533360 : List Nat := [2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 3]
def baseStart_3533360 : Nat := 118140960795 + 3533360 * 2 ^ 59
def prefixEnd_3533360 : Nat := 4983230072969 + 3 ^ 40 * 3533360 * 2
def baseEnd_3533360 : Nat := 1814312005370400946450379

theorem tailTrace_3533360 : CollatzResearch.WordTrace tailWord_3533360 prefixEnd_3533360 1814312005370400946450379 := by
  unfold tailWord_3533360
  simp only [CollatzResearch.WordTrace]
  refine ⟨64436113239623822345006767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85914817652831763126675689 64436113239623822345006767)
  ·
    refine ⟨96654169859435733517510151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64436113239623822345006767 96654169859435733517510151)
    ·
      refine ⟨144981254789153600276265227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96654169859435733517510151 144981254789153600276265227)
      ·
        refine ⟨217471882183730400414397841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144981254789153600276265227 217471882183730400414397841)
        ·
          refine ⟨163103911637797800310798381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217471882183730400414397841 163103911637797800310798381)
          ·
            refine ⟨61163966864174175116549393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163103911637797800310798381 61163966864174175116549393)
            ·
              refine ⟨45872975148130631337412045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61163966864174175116549393 45872975148130631337412045)
              ·
                refine ⟨17202365680548986751529517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45872975148130631337412045 17202365680548986751529517)
                ·
                  refine ⟨6450887130205870031823569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17202365680548986751529517 6450887130205870031823569)
                  ·
                    refine ⟨4838165347654402523867677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6450887130205870031823569 4838165347654402523867677)
                    ·
                      refine ⟨1814312005370400946450379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4838165347654402523867677 1814312005370400946450379)
                      ·
                        rfl

theorem cell23_3533360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 3].length) (baseStart_3533360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533360 prefixEnd_3533360 := by exact prefixLift 3533360
  have htrace : WordTrace (prefixWord ++ tailWord_3533360) baseStart_3533360 baseEnd_3533360 := by
    simpa [prefixWord, tailWord_3533360, baseEnd_3533360] using wordTrace_append hprefix tailTrace_3533360
  have hstable : (prefixWord ++ tailWord_3533360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533360).length < 2 ^ (prefixWord ++ tailWord_3533360).sum := by decide
  have hdescent : baseEnd_3533360 < baseStart_3533360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533363 : List Nat := [1, 1, 1, 2, 4, 2, 3, 9]
def baseStart_3533363 : Nat := 118140960795 + 3533363 * 2 ^ 59
def prefixEnd_3533363 : Nat := 4983230072969 + 3 ^ 40 * 3533363 * 2
def baseEnd_3533363 : Nat := 67196797993050534618995

theorem tailTrace_3533363 : CollatzResearch.WordTrace tailWord_3533363 prefixEnd_3533363 67196797993050534618995 := by
  unfold tailWord_3533363
  simp only [CollatzResearch.WordTrace]
  refine ⟨128872335898236776202372743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85914890598824517468248495 128872335898236776202372743)
  ·
    refine ⟨193308503847355164303559115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128872335898236776202372743 193308503847355164303559115)
    ·
      refine ⟨289962755771032746455338673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193308503847355164303559115 289962755771032746455338673)
      ·
        refine ⟨217472066828274559841504005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 289962755771032746455338673 217472066828274559841504005)
        ·
          refine ⟨40776012530301479970282001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 217472066828274559841504005 40776012530301479970282001)
          ·
            refine ⟨30582009397726109977711501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40776012530301479970282001 30582009397726109977711501)
            ·
              refine ⟨11468253524147291241641813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30582009397726109977711501 11468253524147291241641813)
              ·
                refine ⟨67196797993050534618995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11468253524147291241641813 67196797993050534618995)
                ·
                  rfl

theorem cell23_3533363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 9].length) (baseStart_3533363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533363 prefixEnd_3533363 := by exact prefixLift 3533363
  have htrace : WordTrace (prefixWord ++ tailWord_3533363) baseStart_3533363 baseEnd_3533363 := by
    simpa [prefixWord, tailWord_3533363, baseEnd_3533363] using wordTrace_append hprefix tailTrace_3533363
  have hstable : (prefixWord ++ tailWord_3533363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533363).length < 2 ^ (prefixWord ++ tailWord_3533363).sum := by decide
  have hdescent : baseEnd_3533363 < baseStart_3533363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533377 : List Nat := [1, 2, 5, 1, 1, 3, 2, 1, 1, 1, 5]
def baseStart_3533377 : Nat := 118140960795 + 3533377 * 2 ^ 59
def prefixEnd_3533377 : Nat := 4983230072969 + 3 ^ 40 * 3533377 * 2
def baseEnd_3533377 : Nat := 1814320734541527379937801

theorem tailTrace_3533377 : CollatzResearch.WordTrace tailWord_3533377 prefixEnd_3533377 1814320734541527379937801 := by
  unfold tailWord_3533377
  simp only [CollatzResearch.WordTrace]
  refine ⟨128872846520186056593382385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85915231013457371062254923 128872846520186056593382385)
  ·
    refine ⟨96654634890139542445036789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128872846520186056593382385 96654634890139542445036789)
    ·
      refine ⟨9061372020950582104222199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 96654634890139542445036789 9061372020950582104222199)
      ·
        refine ⟨13592058031425873156333299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9061372020950582104222199 13592058031425873156333299)
        ·
          refine ⟨20388087047138809734499949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13592058031425873156333299 20388087047138809734499949)
          ·
            refine ⟨7645532642677053650437481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20388087047138809734499949 7645532642677053650437481)
            ·
              refine ⟨5734149482007790237828111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7645532642677053650437481 5734149482007790237828111)
              ·
                refine ⟨8601224223011685356742167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5734149482007790237828111 8601224223011685356742167)
                ·
                  refine ⟨12901836334517528035113251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8601224223011685356742167 12901836334517528035113251)
                  ·
                    refine ⟨19352754501776292052669877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12901836334517528035113251 19352754501776292052669877)
                    ·
                      refine ⟨1814320734541527379937801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19352754501776292052669877 1814320734541527379937801)
                      ·
                        rfl

theorem cell23_3533377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_3533377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533377 prefixEnd_3533377 := by exact prefixLift 3533377
  have htrace : WordTrace (prefixWord ++ tailWord_3533377) baseStart_3533377 baseEnd_3533377 := by
    simpa [prefixWord, tailWord_3533377, baseEnd_3533377] using wordTrace_append hprefix tailTrace_3533377
  have hstable : (prefixWord ++ tailWord_3533377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533377).length < 2 ^ (prefixWord ++ tailWord_3533377).sum := by decide
  have hdescent : baseEnd_3533377 < baseStart_3533377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533447 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 3, 4, 2]
def baseStart_3533447 : Nat := 118140960795 + 3533447 * 2 ^ 59
def prefixEnd_3533447 : Nat := 4983230072969 + 3 ^ 40 * 3533447 * 2
def baseEnd_3533447 : Nat := 1814356678187342106062479

theorem tailTrace_3533447 : CollatzResearch.WordTrace tailWord_3533447 prefixEnd_3533447 1814356678187342106062479 := by
  unfold tailWord_3533447
  simp only [CollatzResearch.WordTrace]
  refine ⟨128875399629932458548430595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85916933086621639032287063 128875399629932458548430595)
  ·
    refine ⟨193313099444898687822645893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128875399629932458548430595 193313099444898687822645893)
    ·
      refine ⟨36246206145918503966746105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193313099444898687822645893 36246206145918503966746105)
      ·
        refine ⟨27184654609438877975059579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36246206145918503966746105 27184654609438877975059579)
        ·
          refine ⟨40776981914158316962589369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27184654609438877975059579 40776981914158316962589369)
          ·
            refine ⟨30582736435618737721942027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40776981914158316962589369 30582736435618737721942027)
            ·
              refine ⟨45874104653428106582913041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30582736435618737721942027 45874104653428106582913041)
              ·
                refine ⟨34405578490071079937184781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45874104653428106582913041 34405578490071079937184781)
                ·
                  refine ⟨12902091933776654976444293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34405578490071079937184781 12902091933776654976444293)
                  ·
                    refine ⟨2419142237583122808083305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12902091933776654976444293 2419142237583122808083305)
                    ·
                      refine ⟨1814356678187342106062479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2419142237583122808083305 1814356678187342106062479)
                      ·
                        rfl

theorem cell23_3533447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_3533447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533447 prefixEnd_3533447 := by exact prefixLift 3533447
  have htrace : WordTrace (prefixWord ++ tailWord_3533447) baseStart_3533447 baseEnd_3533447 := by
    simpa [prefixWord, tailWord_3533447, baseEnd_3533447] using wordTrace_append hprefix tailTrace_3533447
  have hstable : (prefixWord ++ tailWord_3533447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533447).length < 2 ^ (prefixWord ++ tailWord_3533447).sum := by decide
  have hdescent : baseEnd_3533447 < baseStart_3533447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533464 : List Nat := [2, 1, 2, 4, 1, 1, 4, 1, 1, 4, 2]
def baseStart_3533464 : Nat := 118140960795 + 3533464 * 2 ^ 59
def prefixEnd_3533464 : Nat := 4983230072969 + 3 ^ 40 * 3533464 * 2
def baseEnd_3533464 : Nat := 1814365407358468539549901

theorem tailTrace_3533464 : CollatzResearch.WordTrace tailWord_3533464 prefixEnd_3533464 1814365407358468539549901 := by
  unfold tailWord_3533464
  simp only [CollatzResearch.WordTrace]
  refine ⟨64438009835435435225899723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85917346447247246967866297 64438009835435435225899723)
  ·
    refine ⟨96657014753153152838849585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64438009835435435225899723 96657014753153152838849585)
    ·
      refine ⟨72492761064864864629137189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96657014753153152838849585 72492761064864864629137189)
      ·
        refine ⟨13592392699662162117963223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72492761064864864629137189 13592392699662162117963223)
        ·
          refine ⟨20388589049493243176944835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13592392699662162117963223 20388589049493243176944835)
          ·
            refine ⟨30582883574239864765417253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20388589049493243176944835 30582883574239864765417253)
            ·
              refine ⟨5734290670169974643515735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30582883574239864765417253 5734290670169974643515735)
              ·
                refine ⟨8601436005254961965273603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5734290670169974643515735 8601436005254961965273603)
                ·
                  refine ⟨12902154007882442947910405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8601436005254961965273603 12902154007882442947910405)
                  ·
                    refine ⟨2419153876477958052733201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12902154007882442947910405 2419153876477958052733201)
                    ·
                      refine ⟨1814365407358468539549901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2419153876477958052733201 1814365407358468539549901)
                      ·
                        rfl

theorem cell23_3533464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_3533464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533464 prefixEnd_3533464 := by exact prefixLift 3533464
  have htrace : WordTrace (prefixWord ++ tailWord_3533464) baseStart_3533464 baseEnd_3533464 := by
    simpa [prefixWord, tailWord_3533464, baseEnd_3533464] using wordTrace_append hprefix tailTrace_3533464
  have hstable : (prefixWord ++ tailWord_3533464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533464).length < 2 ^ (prefixWord ++ tailWord_3533464).sum := by decide
  have hdescent : baseEnd_3533464 < baseStart_3533464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533487 : List Nat := [1, 1, 2, 1, 2, 5, 1, 5, 5]
def baseStart_3533487 : Nat := 118140960795 + 3533487 * 2 ^ 59
def prefixEnd_3533487 : Nat := 4983230072969 + 3 ^ 40 * 3533487 * 2
def baseEnd_3533487 : Nat := 201597468601502438840255

theorem tailTrace_3533487 : CollatzResearch.WordTrace tailWord_3533487 prefixEnd_3533487 201597468601502438840255 := by
  unfold tailWord_3533487
  simp only [CollatzResearch.WordTrace]
  refine ⟨128876858549787545379886715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85917905699858363586591143 128876858549787545379886715)
  ·
    refine ⟨193315287824681318069830073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128876858549787545379886715 193315287824681318069830073)
    ·
      refine ⟨144986465868510988552372555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193315287824681318069830073 144986465868510988552372555)
      ·
        refine ⟨217479698802766482828558833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144986465868510988552372555 217479698802766482828558833)
        ·
          refine ⟨163109774102074862121419125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217479698802766482828558833 163109774102074862121419125)
          ·
            refine ⟨15291541322069518323883043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 163109774102074862121419125 15291541322069518323883043)
            ·
              refine ⟨22937311983104277485824565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15291541322069518323883043 22937311983104277485824565)
              ·
                refine ⟨2150372998416026014296053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22937311983104277485824565 2150372998416026014296053)
                ·
                  refine ⟨201597468601502438840255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2150372998416026014296053 201597468601502438840255)
                  ·
                    rfl

theorem cell23_3533487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 5].length) (baseStart_3533487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533487 prefixEnd_3533487 := by exact prefixLift 3533487
  have htrace : WordTrace (prefixWord ++ tailWord_3533487) baseStart_3533487 baseEnd_3533487 := by
    simpa [prefixWord, tailWord_3533487, baseEnd_3533487] using wordTrace_append hprefix tailTrace_3533487
  have hstable : (prefixWord ++ tailWord_3533487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533487).length < 2 ^ (prefixWord ++ tailWord_3533487).sum := by decide
  have hdescent : baseEnd_3533487 < baseStart_3533487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533530 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 2, 8]
def baseStart_3533530 : Nat := 118140960795 + 3533530 * 2 ^ 59
def prefixEnd_3533530 : Nat := 4983230072969 + 3 ^ 40 * 3533530 * 2
def baseEnd_3533530 : Nat := 604799765693888427108199

theorem tailTrace_3533530 : CollatzResearch.WordTrace tailWord_3533530 prefixEnd_3533530 604799765693888427108199 := by
  unfold tailWord_3533530
  simp only [CollatzResearch.WordTrace]
  refine ⟨32219606722157940930925511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85918951259087842482468029 32219606722157940930925511)
  ·
    refine ⟨48329410083236911396388267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32219606722157940930925511 48329410083236911396388267)
    ·
      refine ⟨72494115124855367094582401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48329410083236911396388267 72494115124855367094582401)
      ·
        refine ⟨54370586343641525320936801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72494115124855367094582401 54370586343641525320936801)
        ·
          refine ⟨40777939757731143990702601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54370586343641525320936801 40777939757731143990702601)
          ·
            refine ⟨30583454818298357993026951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40777939757731143990702601 30583454818298357993026951)
            ·
              refine ⟨45875182227447536989540427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30583454818298357993026951 45875182227447536989540427)
              ·
                refine ⟨68812773341171305484310641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45875182227447536989540427 68812773341171305484310641)
                ·
                  refine ⟨51609580005878479113232981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 68812773341171305484310641 51609580005878479113232981)
                  ·
                    refine ⟨604799765693888427108199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 51609580005878479113232981 604799765693888427108199)
                    ·
                      rfl

theorem cell23_3533530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_3533530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533530 prefixEnd_3533530 := by exact prefixLift 3533530
  have htrace : WordTrace (prefixWord ++ tailWord_3533530) baseStart_3533530 baseEnd_3533530 := by
    simpa [prefixWord, tailWord_3533530, baseEnd_3533530] using wordTrace_append hprefix tailTrace_3533530
  have hstable : (prefixWord ++ tailWord_3533530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533530).length < 2 ^ (prefixWord ++ tailWord_3533530).sum := by decide
  have hdescent : baseEnd_3533530 < baseStart_3533530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533537 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_3533537 : Nat := 118140960795 + 3533537 * 2 ^ 59
def prefixEnd_3533537 : Nat := 4983230072969 + 3 ^ 40 * 3533537 * 2
def baseEnd_3533537 : Nat := 1814402891446246753937065

theorem tailTrace_3533537 : CollatzResearch.WordTrace tailWord_3533537 prefixEnd_3533537 1814402891446246753937065 := by
  unfold tailWord_3533537
  simp only [CollatzResearch.WordTrace]
  refine ⟨128878682199606403919206865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85919121466404269279471243 128878682199606403919206865)
  ·
    refine ⟨96659011649704802939405149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128878682199606403919206865 96659011649704802939405149)
    ·
      refine ⟨36247129368639301102276931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96659011649704802939405149 36247129368639301102276931)
      ·
        refine ⟨54370694052958951653415397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36247129368639301102276931 54370694052958951653415397)
        ·
          refine ⟨10194505134929803435015387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54370694052958951653415397 10194505134929803435015387)
          ·
            refine ⟨15291757702394705152523081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10194505134929803435015387 15291757702394705152523081)
            ·
              refine ⟨11468818276796028864392311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15291757702394705152523081 11468818276796028864392311)
              ·
                refine ⟨17203227415194043296588467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11468818276796028864392311 17203227415194043296588467)
                ·
                  refine ⟨25804841122791064944882701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17203227415194043296588467 25804841122791064944882701)
                  ·
                    refine ⟨9676815421046649354331013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25804841122791064944882701 9676815421046649354331013)
                    ·
                      refine ⟨1814402891446246753937065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9676815421046649354331013 1814402891446246753937065)
                      ·
                        rfl

theorem cell23_3533537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_3533537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533537 prefixEnd_3533537 := by exact prefixLift 3533537
  have htrace : WordTrace (prefixWord ++ tailWord_3533537) baseStart_3533537 baseEnd_3533537 := by
    simpa [prefixWord, tailWord_3533537, baseEnd_3533537] using wordTrace_append hprefix tailTrace_3533537
  have hstable : (prefixWord ++ tailWord_3533537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533537).length < 2 ^ (prefixWord ++ tailWord_3533537).sum := by decide
  have hdescent : baseEnd_3533537 < baseStart_3533537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533554 : List Nat := [3, 2, 1, 3, 1, 3, 1, 2, 2, 1, 4]
def baseStart_3533554 : Nat := 118140960795 + 3533554 * 2 ^ 59
def prefixEnd_3533554 : Nat := 4983230072969 + 3 ^ 40 * 3533554 * 2
def baseEnd_3533554 : Nat := 1814411620617373187424487

theorem tailTrace_3533554 : CollatzResearch.WordTrace tailWord_3533554 prefixEnd_3533554 1814411620617373187424487 := by
  unfold tailWord_3533554
  simp only [CollatzResearch.WordTrace]
  refine ⟨32219825560136203955643929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85919534827029877215050477 32219825560136203955643929)
  ·
    refine ⟨24164869170102152966732947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32219825560136203955643929 24164869170102152966732947)
    ·
      refine ⟨36247303755153229450099421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24164869170102152966732947 36247303755153229450099421)
      ·
        refine ⟨13592738908182461043787283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36247303755153229450099421 13592738908182461043787283)
        ·
          refine ⟨20389108362273691565680925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13592738908182461043787283 20389108362273691565680925)
          ·
            refine ⟨7645915635852634337130347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20389108362273691565680925 7645915635852634337130347)
            ·
              refine ⟨11468873453778951505695521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7645915635852634337130347 11468873453778951505695521)
              ·
                refine ⟨8601655090334213629271641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11468873453778951505695521 8601655090334213629271641)
                ·
                  refine ⟨6451241317750660221953731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8601655090334213629271641 6451241317750660221953731)
                  ·
                    refine ⟨9676861976625990332930597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6451241317750660221953731 9676861976625990332930597)
                    ·
                      refine ⟨1814411620617373187424487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9676861976625990332930597 1814411620617373187424487)
                      ·
                        rfl

theorem cell23_3533554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_3533554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533554 prefixEnd_3533554 := by exact prefixLift 3533554
  have htrace : WordTrace (prefixWord ++ tailWord_3533554) baseStart_3533554 baseEnd_3533554 := by
    simpa [prefixWord, tailWord_3533554, baseEnd_3533554] using wordTrace_append hprefix tailTrace_3533554
  have hstable : (prefixWord ++ tailWord_3533554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533554).length < 2 ^ (prefixWord ++ tailWord_3533554).sum := by decide
  have hdescent : baseEnd_3533554 < baseStart_3533554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533560 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 8]
def baseStart_3533560 : Nat := 118140960795 + 3533560 * 2 ^ 59
def prefixEnd_3533560 : Nat := 4983230072969 + 3 ^ 40 * 3533560 * 2
def baseEnd_3533560 : Nat := 201601633500144462661051

theorem tailTrace_3533560 : CollatzResearch.WordTrace tailWord_3533560 prefixEnd_3533560 201601633500144462661051 := by
  unfold tailWord_3533560
  simp only [CollatzResearch.WordTrace]
  refine ⟨64439760539261539423647067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85919680719015385898196089 64439760539261539423647067)
  ·
    refine ⟨96659640808892309135470601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64439760539261539423647067 96659640808892309135470601)
    ·
      refine ⟨72494730606669231851602951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96659640808892309135470601 72494730606669231851602951)
      ·
        refine ⟨108742095910003847777404427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72494730606669231851602951 108742095910003847777404427)
        ·
          refine ⟨163113143865005771666106641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108742095910003847777404427 163113143865005771666106641)
          ·
            refine ⟨122334857898754328749579981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163113143865005771666106641 122334857898754328749579981)
            ·
              refine ⟨45875571712032873281092493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122334857898754328749579981 45875571712032873281092493)
              ·
                refine ⟨17203339392012327480409685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45875571712032873281092493 17203339392012327480409685)
                ·
                  refine ⟨201601633500144462661051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17203339392012327480409685 201601633500144462661051)
                  ·
                    rfl

theorem cell23_3533560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 8].length) (baseStart_3533560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533560 prefixEnd_3533560 := by exact prefixLift 3533560
  have htrace : WordTrace (prefixWord ++ tailWord_3533560) baseStart_3533560 baseEnd_3533560 := by
    simpa [prefixWord, tailWord_3533560, baseEnd_3533560] using wordTrace_append hprefix tailTrace_3533560
  have hstable : (prefixWord ++ tailWord_3533560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533560).length < 2 ^ (prefixWord ++ tailWord_3533560).sum := by decide
  have hdescent : baseEnd_3533560 < baseStart_3533560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533564 : List Nat := [2, 2, 2, 1, 3, 2, 3, 1, 3, 4]
def baseStart_3533564 : Nat := 118140960795 + 3533564 * 2 ^ 59
def prefixEnd_3533564 : Nat := 4983230072969 + 3 ^ 40 * 3533564 * 2
def baseEnd_3533564 : Nat := 604805585141306049433147

theorem tailTrace_3533564 : CollatzResearch.WordTrace tailWord_3533564 prefixEnd_3533564 604805585141306049433147 := by
  unfold tailWord_3533564
  simp only [CollatzResearch.WordTrace]
  refine ⟨64439833485254293765219873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85919777980339058353626497 64439833485254293765219873)
  ·
    refine ⟨48329875113940720323914905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64439833485254293765219873 48329875113940720323914905)
    ·
      refine ⟨36247406335455540242936179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48329875113940720323914905 36247406335455540242936179)
      ·
        refine ⟨54371109503183310364404269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36247406335455540242936179 54371109503183310364404269)
        ·
          refine ⟨20389166063693741386651601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54371109503183310364404269 20389166063693741386651601)
          ·
            refine ⟨15291874547770306039988701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20389166063693741386651601 15291874547770306039988701)
            ·
              refine ⟨5734452955413864764995763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15291874547770306039988701 5734452955413864764995763)
              ·
                refine ⟨8601679433120797147493645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5734452955413864764995763 8601679433120797147493645)
                ·
                  refine ⟨3225629787420298930310117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8601679433120797147493645 3225629787420298930310117)
                  ·
                    refine ⟨604805585141306049433147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3225629787420298930310117 604805585141306049433147)
                    ·
                      rfl

theorem cell23_3533564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_3533564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533564 prefixEnd_3533564 := by exact prefixLift 3533564
  have htrace : WordTrace (prefixWord ++ tailWord_3533564) baseStart_3533564 baseEnd_3533564 := by
    simpa [prefixWord, tailWord_3533564, baseEnd_3533564] using wordTrace_append hprefix tailTrace_3533564
  have hstable : (prefixWord ++ tailWord_3533564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533564).length < 2 ^ (prefixWord ++ tailWord_3533564).sum := by decide
  have hdescent : baseEnd_3533564 < baseStart_3533564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533591 : List Nat := [1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 3]
def baseStart_3533591 : Nat := 118140960795 + 3533591 * 2 ^ 59
def prefixEnd_3533591 : Nat := 4983230072969 + 3 ^ 40 * 3533591 * 2
def baseEnd_3533591 : Nat := 1814430619401589542661817

theorem tailTrace_3533591 : CollatzResearch.WordTrace tailWord_3533591 prefixEnd_3533591 1814430619401589542661817 := by
  unfold tailWord_3533591
  simp only [CollatzResearch.WordTrace]
  refine ⟨128880651741410771141672627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85920434494273847427781751 128880651741410771141672627)
  ·
    refine ⟨193320977612116156712508941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128880651741410771141672627 193320977612116156712508941)
    ·
      refine ⟨72495366604543558767190853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193320977612116156712508941 72495366604543558767190853)
      ·
        refine ⟨13592881238351917268848285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72495366604543558767190853 13592881238351917268848285)
        ·
          refine ⟨5097330464381968975818107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13592881238351917268848285 5097330464381968975818107)
          ·
            refine ⟨7645995696572953463727161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5097330464381968975818107 7645995696572953463727161)
            ·
              refine ⟨5734496772429715097795371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7645995696572953463727161 5734496772429715097795371)
              ·
                refine ⟨8601745158644572646693057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5734496772429715097795371 8601745158644572646693057)
                ·
                  refine ⟨6451308868983429485019793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8601745158644572646693057 6451308868983429485019793)
                  ·
                    refine ⟨4838481651737572113764845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6451308868983429485019793 4838481651737572113764845)
                    ·
                      refine ⟨1814430619401589542661817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4838481651737572113764845 1814430619401589542661817)
                      ·
                        rfl

theorem cell23_3533591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_3533591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533591 prefixEnd_3533591 := by exact prefixLift 3533591
  have htrace : WordTrace (prefixWord ++ tailWord_3533591) baseStart_3533591 baseEnd_3533591 := by
    simpa [prefixWord, tailWord_3533591, baseEnd_3533591] using wordTrace_append hprefix tailTrace_3533591
  have hstable : (prefixWord ++ tailWord_3533591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533591).length < 2 ^ (prefixWord ++ tailWord_3533591).sum := by decide
  have hdescent : baseEnd_3533591 < baseStart_3533591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533644 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 3, 1, 4]
def baseStart_3533644 : Nat := 118140960795 + 3533644 * 2 ^ 59
def prefixEnd_3533644 : Nat := 4983230072969 + 3 ^ 40 * 3533644 * 2
def baseEnd_3533644 : Nat := 1814457833876277835299073

theorem tailTrace_3533644 : CollatzResearch.WordTrace tailWord_3533644 prefixEnd_3533644 1814457833876277835299073 := by
  unfold tailWord_3533644
  simp only [CollatzResearch.WordTrace]
  refine ⟨64441292405109380596675993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85921723206812507462234657 64441292405109380596675993)
  ·
    refine ⟨48330969303832035447506995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64441292405109380596675993 48330969303832035447506995)
    ·
      refine ⟨72496453955748053171260493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48330969303832035447506995 72496453955748053171260493)
      ·
        refine ⟨27186170233405519939222685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72496453955748053171260493 27186170233405519939222685)
        ·
          refine ⟨10194813837527069977208507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27186170233405519939222685 10194813837527069977208507)
          ·
            refine ⟨15292220756290604965812761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10194813837527069977208507 15292220756290604965812761)
            ·
              refine ⟨11469165567217953724359571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15292220756290604965812761 11469165567217953724359571)
              ·
                refine ⟨17203748350826930586539357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11469165567217953724359571 17203748350826930586539357)
                ·
                  refine ⟨6451405631560098969952259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17203748350826930586539357 6451405631560098969952259)
                  ·
                    refine ⟨9677108447340148454928389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6451405631560098969952259 9677108447340148454928389)
                    ·
                      refine ⟨1814457833876277835299073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9677108447340148454928389 1814457833876277835299073)
                      ·
                        rfl

theorem cell23_3533644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_3533644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533644 prefixEnd_3533644 := by exact prefixLift 3533644
  have htrace : WordTrace (prefixWord ++ tailWord_3533644) baseStart_3533644 baseEnd_3533644 := by
    simpa [prefixWord, tailWord_3533644, baseEnd_3533644] using wordTrace_append hprefix tailTrace_3533644
  have hstable : (prefixWord ++ tailWord_3533644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533644).length < 2 ^ (prefixWord ++ tailWord_3533644).sum := by decide
  have hdescent : baseEnd_3533644 < baseStart_3533644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533667 : List Nat := [1, 1, 1, 5, 3, 2, 10]
def baseStart_3533667 : Nat := 118140960795 + 3533667 * 2 ^ 59
def prefixEnd_3533667 : Nat := 4983230072969 + 3 ^ 40 * 3533667 * 2
def baseEnd_3533667 : Nat := 22400859801621373398907

theorem tailTrace_3533667 : CollatzResearch.WordTrace tailWord_3533667 prefixEnd_3533667 22400859801621373398907 := by
  unfold tailWord_3533667
  simp only [CollatzResearch.WordTrace]
  refine ⟨128883423689135436121439255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85922282459423624080959503 128883423689135436121439255)
  ·
    refine ⟨193325135533703154182158883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128883423689135436121439255 193325135533703154182158883)
    ·
      refine ⟨289987703300554731273238325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193325135533703154182158883 289987703300554731273238325)
      ·
        refine ⟨27186347184427006056866093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 289987703300554731273238325 27186347184427006056866093)
        ·
          refine ⟨10194880194160127271324785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27186347184427006056866093 10194880194160127271324785)
          ·
            refine ⟨7646160145620095453493589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10194880194160127271324785 7646160145620095453493589)
            ·
              refine ⟨22400859801621373398907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7646160145620095453493589 22400859801621373398907)
              ·
                rfl

theorem cell23_3533667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 10].length) (baseStart_3533667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533667 prefixEnd_3533667 := by exact prefixLift 3533667
  have htrace : WordTrace (prefixWord ++ tailWord_3533667) baseStart_3533667 baseEnd_3533667 := by
    simpa [prefixWord, tailWord_3533667, baseEnd_3533667] using wordTrace_append hprefix tailTrace_3533667
  have hstable : (prefixWord ++ tailWord_3533667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533667).length < 2 ^ (prefixWord ++ tailWord_3533667).sum := by decide
  have hdescent : baseEnd_3533667 < baseStart_3533667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533671 : List Nat := [1, 1, 5, 1, 2, 2, 3, 2, 2, 4]
def baseStart_3533671 : Nat := 118140960795 + 3533671 * 2 ^ 59
def prefixEnd_3533671 : Nat := 4983230072969 + 3 ^ 40 * 3533671 * 2
def baseEnd_3533671 : Nat := 604823899284649743220483

theorem tailTrace_3533671 : CollatzResearch.WordTrace tailWord_3533671 prefixEnd_3533671 604823899284649743220483 := by
  unfold tailWord_3533671
  simp only [CollatzResearch.WordTrace]
  refine ⟨128883569581120944804584867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85922379720747296536389911 128883569581120944804584867)
  ·
    refine ⟨193325354371681417206877301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128883569581120944804584867 193325354371681417206877301)
    ·
      refine ⟨18124251972345132863144747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193325354371681417206877301 18124251972345132863144747)
      ·
        refine ⟨27186377958517699294717121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18124251972345132863144747 27186377958517699294717121)
        ·
          refine ⟨20389783468888274471037841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27186377958517699294717121 20389783468888274471037841)
          ·
            refine ⟨15292337601666205853278381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20389783468888274471037841 15292337601666205853278381)
            ·
              refine ⟨5734626600624827194979393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15292337601666205853278381 5734626600624827194979393)
              ·
                refine ⟨4300969950468620396234545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5734626600624827194979393 4300969950468620396234545)
                ·
                  refine ⟨3225727462851465297175909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4300969950468620396234545 3225727462851465297175909)
                  ·
                    refine ⟨604823899284649743220483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3225727462851465297175909 604823899284649743220483)
                    ·
                      rfl

theorem cell23_3533671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_3533671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533671 prefixEnd_3533671 := by exact prefixLift 3533671
  have htrace : WordTrace (prefixWord ++ tailWord_3533671) baseStart_3533671 baseEnd_3533671 := by
    simpa [prefixWord, tailWord_3533671, baseEnd_3533671] using wordTrace_append hprefix tailTrace_3533671
  have hstable : (prefixWord ++ tailWord_3533671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533671).length < 2 ^ (prefixWord ++ tailWord_3533671).sum := by decide
  have hdescent : baseEnd_3533671 < baseStart_3533671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533677 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_3533677 : Nat := 118140960795 + 3533677 * 2 ^ 59
def prefixEnd_3533677 : Nat := 4983230072969 + 3 ^ 40 * 3533677 * 2
def baseEnd_3533677 : Nat := 1814474778737876206186421

theorem tailTrace_3533677 : CollatzResearch.WordTrace tailWord_3533677 prefixEnd_3533677 1814474778737876206186421 := by
  unfold tailWord_3533677
  simp only [CollatzResearch.WordTrace]
  refine ⟨128883788419099207829303285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85922525612732805219535523 128883788419099207829303285)
  ·
    refine ⟨12082855164290550733997183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 128883788419099207829303285 12082855164290550733997183)
    ·
      refine ⟨18124282746435826100995775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12082855164290550733997183 18124282746435826100995775)
      ·
        refine ⟨27186424119653739151493663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18124282746435826100995775 27186424119653739151493663)
        ·
          refine ⟨40779636179480608727240495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27186424119653739151493663 40779636179480608727240495)
          ·
            refine ⟨61169454269220913090860743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40779636179480608727240495 61169454269220913090860743)
            ·
              refine ⟨91754181403831369636291115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61169454269220913090860743 91754181403831369636291115)
              ·
                refine ⟨137631272105747054454436673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91754181403831369636291115 137631272105747054454436673)
                ·
                  refine ⟨103223454079310290840827505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137631272105747054454436673 103223454079310290840827505)
                  ·
                    refine ⟨77417590559482718130620629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 103223454079310290840827505 77417590559482718130620629)
                    ·
                      refine ⟨1814474778737876206186421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77417590559482718130620629 1814474778737876206186421)
                      ·
                        rfl

theorem cell23_3533677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_3533677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533677 prefixEnd_3533677 := by exact prefixLift 3533677
  have htrace : WordTrace (prefixWord ++ tailWord_3533677) baseStart_3533677 baseEnd_3533677 := by
    simpa [prefixWord, tailWord_3533677, baseEnd_3533677] using wordTrace_append hprefix tailTrace_3533677
  have hstable : (prefixWord ++ tailWord_3533677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533677).length < 2 ^ (prefixWord ++ tailWord_3533677).sum := by decide
  have hdescent : baseEnd_3533677 < baseStart_3533677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533707 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 5]
def baseStart_3533707 : Nat := 118140960795 + 3533707 * 2 ^ 59
def prefixEnd_3533707 : Nat := 4983230072969 + 3 ^ 40 * 3533707 * 2
def baseEnd_3533707 : Nat := 1814490183157511088811283

theorem tailTrace_3533707 : CollatzResearch.WordTrace tailWord_3533707 prefixEnd_3533707 1814490183157511088811283 := by
  unfold tailWord_3533707
  simp only [CollatzResearch.WordTrace]
  refine ⟨128884882608990522952895375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85923255072660348635263583 128884882608990522952895375)
  ·
    refine ⟨193327323913485784429343063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128884882608990522952895375 193327323913485784429343063)
    ·
      refine ⟨289990985870228676644014595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193327323913485784429343063 289990985870228676644014595)
      ·
        refine ⟨434986478805343014966021893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289990985870228676644014595 434986478805343014966021893)
        ·
          refine ⟨81559964776001815306129105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 434986478805343014966021893 81559964776001815306129105)
          ·
            refine ⟨61169973582001361479596829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81559964776001815306129105 61169973582001361479596829)
            ·
              refine ⟨22938740093250510554848811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61169973582001361479596829 22938740093250510554848811)
              ·
                refine ⟨34408110139875765832273217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22938740093250510554848811 34408110139875765832273217)
                ·
                  refine ⟨25806082604906824374204913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34408110139875765832273217 25806082604906824374204913)
                  ·
                    refine ⟨19354561953680118280653685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25806082604906824374204913 19354561953680118280653685)
                    ·
                      refine ⟨1814490183157511088811283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19354561953680118280653685 1814490183157511088811283)
                      ·
                        rfl

theorem cell23_3533707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 5].length) (baseStart_3533707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533707 prefixEnd_3533707 := by exact prefixLift 3533707
  have htrace : WordTrace (prefixWord ++ tailWord_3533707) baseStart_3533707 baseEnd_3533707 := by
    simpa [prefixWord, tailWord_3533707, baseEnd_3533707] using wordTrace_append hprefix tailTrace_3533707
  have hstable : (prefixWord ++ tailWord_3533707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533707).length < 2 ^ (prefixWord ++ tailWord_3533707).sum := by decide
  have hdescent : baseEnd_3533707 < baseStart_3533707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533718 : List Nat := [5, 3, 1, 1, 1, 3, 9]
def baseStart_3533718 : Nat := 118140960795 + 3533718 * 2 ^ 59
def prefixEnd_3533718 : Nat := 4983230072969 + 3 ^ 40 * 3533718 * 2
def baseEnd_3533718 : Nat := 22401183104255685750293

theorem tailTrace_3533718 : CollatzResearch.WordTrace tailWord_3533718 prefixEnd_3533718 22401183104255685750293 := by
  unfold tailWord_3533718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8055330238246916989471613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85923522541300447887697205 8055330238246916989471613)
  ·
    refine ⟨3020748839342593871051855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8055330238246916989471613 3020748839342593871051855)
    ·
      refine ⟨4531123259013890806577783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3020748839342593871051855 4531123259013890806577783)
      ·
        refine ⟨6796684888520836209866675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4531123259013890806577783 6796684888520836209866675)
        ·
          refine ⟨10195027332781254314800013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6796684888520836209866675 10195027332781254314800013)
          ·
            refine ⟨3823135249792970368050005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10195027332781254314800013 3823135249792970368050005)
            ·
              refine ⟨22401183104255685750293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3823135249792970368050005 22401183104255685750293)
              ·
                rfl

theorem cell23_3533718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 9].length) (baseStart_3533718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533718 prefixEnd_3533718 := by exact prefixLift 3533718
  have htrace : WordTrace (prefixWord ++ tailWord_3533718) baseStart_3533718 baseEnd_3533718 := by
    simpa [prefixWord, tailWord_3533718, baseEnd_3533718] using wordTrace_append hprefix tailTrace_3533718
  have hstable : (prefixWord ++ tailWord_3533718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533718).length < 2 ^ (prefixWord ++ tailWord_3533718).sum := by decide
  have hdescent : baseEnd_3533718 < baseStart_3533718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533737 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 1, 3, 5]
def baseStart_3533737 : Nat := 118140960795 + 3533737 * 2 ^ 59
def prefixEnd_3533737 : Nat := 4983230072969 + 3 ^ 40 * 3533737 * 2
def baseEnd_3533737 : Nat := 1814505587577145971436145

theorem tailTrace_3533737 : CollatzResearch.WordTrace tailWord_3533737 prefixEnd_3533737 1814505587577145971436145 := by
  unfold tailWord_3533737
  simp only [CollatzResearch.WordTrace]
  refine ⟨128885976798881838076487465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85923984532587892050991643 128885976798881838076487465)
  ·
    refine ⟨96664482599161378557365599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128885976798881838076487465 96664482599161378557365599)
    ·
      refine ⟨144996723898742067836048399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96664482599161378557365599 144996723898742067836048399)
      ·
        refine ⟨217495085848113101754072599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 144996723898742067836048399 217495085848113101754072599)
        ·
          refine ⟨326242628772169652631108899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217495085848113101754072599 326242628772169652631108899)
          ·
            refine ⟨489363943158254478946663349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 326242628772169652631108899 489363943158254478946663349)
            ·
              refine ⟨45877869671086357401249689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 489363943158254478946663349 45877869671086357401249689)
              ·
                refine ⟨34408402253314768050937267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45877869671086357401249689 34408402253314768050937267)
                ·
                  refine ⟨51612603379972152076405901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34408402253314768050937267 51612603379972152076405901)
                  ·
                    refine ⟨19354726267489557028652213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 51612603379972152076405901 19354726267489557028652213)
                    ·
                      refine ⟨1814505587577145971436145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19354726267489557028652213 1814505587577145971436145)
                      ·
                        rfl

theorem cell23_3533737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_3533737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533737 prefixEnd_3533737 := by exact prefixLift 3533737
  have htrace : WordTrace (prefixWord ++ tailWord_3533737) baseStart_3533737 baseEnd_3533737 := by
    simpa [prefixWord, tailWord_3533737, baseEnd_3533737] using wordTrace_append hprefix tailTrace_3533737
  have hstable : (prefixWord ++ tailWord_3533737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533737).length < 2 ^ (prefixWord ++ tailWord_3533737).sum := by decide
  have hdescent : baseEnd_3533737 < baseStart_3533737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533766 : List Nat := [6, 1, 3, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_3533766 : Nat := 118140960795 + 3533766 * 2 ^ 59
def prefixEnd_3533766 : Nat := 4983230072969 + 3 ^ 40 * 3533766 * 2
def baseEnd_3533766 : Nat := 1814520478516126357973513

theorem tailTrace_3533766 : CollatzResearch.WordTrace tailWord_3533766 prefixEnd_3533766 1814520478516126357973513 := by
  unfold tailWord_3533766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4027719828618024250915411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 85924689677184517352862101 4027719828618024250915411)
  ·
    refine ⟨6041579742927036376373117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4027719828618024250915411 6041579742927036376373117)
    ·
      refine ⟨2265592403597638641139919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6041579742927036376373117 2265592403597638641139919)
      ·
        refine ⟨3398388605396457961709879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2265592403597638641139919 3398388605396457961709879)
        ·
          refine ⟨5097582908094686942564819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3398388605396457961709879 5097582908094686942564819)
          ·
            refine ⟨7646374362142030413847229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5097582908094686942564819 7646374362142030413847229)
            ·
              refine ⟨2867390385803261405192711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7646374362142030413847229 2867390385803261405192711)
              ·
                refine ⟨4301085578704892107789067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2867390385803261405192711 4301085578704892107789067)
                ·
                  refine ⟨6451628368057338161683601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4301085578704892107789067 6451628368057338161683601)
                  ·
                    refine ⟨4838721276043003621262701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6451628368057338161683601 4838721276043003621262701)
                    ·
                      refine ⟨1814520478516126357973513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4838721276043003621262701 1814520478516126357973513)
                      ·
                        rfl

theorem cell23_3533766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_3533766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533766 prefixEnd_3533766 := by exact prefixLift 3533766
  have htrace : WordTrace (prefixWord ++ tailWord_3533766) baseStart_3533766 baseEnd_3533766 := by
    simpa [prefixWord, tailWord_3533766, baseEnd_3533766] using wordTrace_append hprefix tailTrace_3533766
  have hstable : (prefixWord ++ tailWord_3533766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533766).length < 2 ^ (prefixWord ++ tailWord_3533766).sum := by decide
  have hdescent : baseEnd_3533766 < baseStart_3533766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533768 : List Nat := [2, 1, 3, 1, 5, 1, 1, 2, 1, 4, 2]
def baseStart_3533768 : Nat := 118140960795 + 3533768 * 2 ^ 59
def prefixEnd_3533768 : Nat := 4983230072969 + 3 ^ 40 * 3533768 * 2
def baseEnd_3533768 : Nat := 1814521505477435350148503

theorem tailTrace_3533768 : CollatzResearch.WordTrace tailWord_3533768 prefixEnd_3533768 1814521505477435350148503 := by
  unfold tailWord_3533768
  simp only [CollatzResearch.WordTrace]
  refine ⟨64443553730884765185432979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85924738307846353580577305 64443553730884765185432979)
  ·
    refine ⟨96665330596327147778149469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64443553730884765185432979 96665330596327147778149469)
    ·
      refine ⟨36249498973622680416806051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96665330596327147778149469 36249498973622680416806051)
      ·
        refine ⟨54374248460434020625209077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36249498973622680416806051 54374248460434020625209077)
        ·
          refine ⟨5097585793165689433613351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54374248460434020625209077 5097585793165689433613351)
          ·
            refine ⟨7646378689748534150420027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5097585793165689433613351 7646378689748534150420027)
            ·
              refine ⟨11469568034622801225630041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7646378689748534150420027 11469568034622801225630041)
              ·
                refine ⟨8602176025967100919222531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11469568034622801225630041 8602176025967100919222531)
                ·
                  refine ⟨12903264038950651378833797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8602176025967100919222531 12903264038950651378833797)
                  ·
                    refine ⟨2419362007303247133531337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12903264038950651378833797 2419362007303247133531337)
                    ·
                      refine ⟨1814521505477435350148503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2419362007303247133531337 1814521505477435350148503)
                      ·
                        rfl

theorem cell23_3533768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 1, 4, 2].length) (baseStart_3533768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533768 prefixEnd_3533768 := by exact prefixLift 3533768
  have htrace : WordTrace (prefixWord ++ tailWord_3533768) baseStart_3533768 baseEnd_3533768 := by
    simpa [prefixWord, tailWord_3533768, baseEnd_3533768] using wordTrace_append hprefix tailTrace_3533768
  have hstable : (prefixWord ++ tailWord_3533768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533768).length < 2 ^ (prefixWord ++ tailWord_3533768).sum := by decide
  have hdescent : baseEnd_3533768 < baseStart_3533768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533785 : List Nat := [1, 2, 1, 2, 5, 2, 2, 2, 2, 2, 2]
def baseStart_3533785 : Nat := 118140960795 + 3533785 * 2 ^ 59
def prefixEnd_3533785 : Nat := 4983230072969 + 3 ^ 40 * 3533785 * 2
def baseEnd_3533785 : Nat := 1814530234648561783635925

theorem tailTrace_3533785 : CollatzResearch.WordTrace tailWord_3533785 prefixEnd_3533785 1814530234648561783635925 := by
  unfold tailWord_3533785
  simp only [CollatzResearch.WordTrace]
  refine ⟨128887727502707942274234809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85925151668471961516156539 128887727502707942274234809)
  ·
    refine ⟨96665795627030956705676107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128887727502707942274234809 96665795627030956705676107)
    ·
      refine ⟨144998693440546435058514161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96665795627030956705676107 144998693440546435058514161)
      ·
        refine ⟨108749020080409826293885621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144998693440546435058514161 108749020080409826293885621)
        ·
          refine ⟨10195220632538421215051777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108749020080409826293885621 10195220632538421215051777)
          ·
            refine ⟨7646415474403815911288833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10195220632538421215051777 7646415474403815911288833)
            ·
              refine ⟨5734811605802861933466625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7646415474403815911288833 5734811605802861933466625)
              ·
                refine ⟨4301108704352146450099969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5734811605802861933466625 4301108704352146450099969)
                ·
                  refine ⟨3225831528264109837574977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4301108704352146450099969 3225831528264109837574977)
                  ·
                    refine ⟨2419373646198082378181233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3225831528264109837574977 2419373646198082378181233)
                    ·
                      refine ⟨1814530234648561783635925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2419373646198082378181233 1814530234648561783635925)
                      ·
                        rfl

theorem cell23_3533785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 2, 2].length) (baseStart_3533785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533785 prefixEnd_3533785 := by exact prefixLift 3533785
  have htrace : WordTrace (prefixWord ++ tailWord_3533785) baseStart_3533785 baseEnd_3533785 := by
    simpa [prefixWord, tailWord_3533785, baseEnd_3533785] using wordTrace_append hprefix tailTrace_3533785
  have hstable : (prefixWord ++ tailWord_3533785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533785).length < 2 ^ (prefixWord ++ tailWord_3533785).sum := by decide
  have hdescent : baseEnd_3533785 < baseStart_3533785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533858 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 2, 4, 2]
def baseStart_3533858 : Nat := 118140960795 + 3533858 * 2 ^ 59
def prefixEnd_3533858 : Nat := 4983230072969 + 3 ^ 40 * 3533858 * 2
def baseEnd_3533858 : Nat := 1814567718736339998023089

theorem tailTrace_3533858 : CollatzResearch.WordTrace tailWord_3533858 prefixEnd_3533858 1814567718736339998023089 := by
  unfold tailWord_3533858
  simp only [CollatzResearch.WordTrace]
  refine ⟨32222597507860868935410557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85926926687628983827761485 32222597507860868935410557)
  ·
    refine ⟨12083474065447825850778959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32222597507860868935410557 12083474065447825850778959)
    ·
      refine ⟨18125211098171738776168439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12083474065447825850778959 18125211098171738776168439)
      ·
        refine ⟨27187816647257608164252659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18125211098171738776168439 27187816647257608164252659)
        ·
          refine ⟨40781724970886412246378989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27187816647257608164252659 40781724970886412246378989)
          ·
            refine ⟨15293146864082404592392121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40781724970886412246378989 15293146864082404592392121)
            ·
              refine ⟨11469860148061803444294091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15293146864082404592392121 11469860148061803444294091)
              ·
                refine ⟨17204790222092705166441137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11469860148061803444294091 17204790222092705166441137)
                ·
                  refine ⟨12903592666569528874830853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17204790222092705166441137 12903592666569528874830853)
                  ·
                    refine ⟨2419423624981786664030785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12903592666569528874830853 2419423624981786664030785)
                    ·
                      refine ⟨1814567718736339998023089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2419423624981786664030785 1814567718736339998023089)
                      ·
                        rfl

theorem cell23_3533858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 2, 4, 2].length) (baseStart_3533858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533858 prefixEnd_3533858 := by exact prefixLift 3533858
  have htrace : WordTrace (prefixWord ++ tailWord_3533858) baseStart_3533858 baseEnd_3533858 := by
    simpa [prefixWord, tailWord_3533858, baseEnd_3533858] using wordTrace_append hprefix tailTrace_3533858
  have hstable : (prefixWord ++ tailWord_3533858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533858).length < 2 ^ (prefixWord ++ tailWord_3533858).sum := by decide
  have hdescent : baseEnd_3533858 < baseStart_3533858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533878 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_3533878 : Nat := 118140960795 + 3533878 * 2 ^ 59
def prefixEnd_3533878 : Nat := 4983230072969 + 3 ^ 40 * 3533878 * 2
def baseEnd_3533878 : Nat := 1814577988349429919772997

theorem tailTrace_3533878 : CollatzResearch.WordTrace tailWord_3533878 prefixEnd_3533878 1814577988349429919772997 := by
  unfold tailWord_3533878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8055694968210688697335643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85927412994247346104913525 8055694968210688697335643)
  ·
    refine ⟨12083542452316033046003465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8055694968210688697335643 12083542452316033046003465)
    ·
      refine ⟨9062656839237024784502599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12083542452316033046003465 9062656839237024784502599)
      ·
        refine ⟨13593985258855537176753899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9062656839237024784502599 13593985258855537176753899)
        ·
          refine ⟨20390977888283305765130849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13593985258855537176753899 20390977888283305765130849)
          ·
            refine ⟨15293233416212479323848137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20390977888283305765130849 15293233416212479323848137)
            ·
              refine ⟨11469925062159359492886103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15293233416212479323848137 11469925062159359492886103)
              ·
                refine ⟨17204887593239039239329155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11469925062159359492886103 17204887593239039239329155)
                ·
                  refine ⟨25807331389858558858993733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17204887593239039239329155 25807331389858558858993733)
                  ·
                    refine ⟨4838874635598479786061325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25807331389858558858993733 4838874635598479786061325)
                    ·
                      refine ⟨1814577988349429919772997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4838874635598479786061325 1814577988349429919772997)
                      ·
                        rfl

theorem cell23_3533878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_3533878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533878 prefixEnd_3533878 := by exact prefixLift 3533878
  have htrace : WordTrace (prefixWord ++ tailWord_3533878) baseStart_3533878 baseEnd_3533878 := by
    simpa [prefixWord, tailWord_3533878, baseEnd_3533878] using wordTrace_append hprefix tailTrace_3533878
  have hstable : (prefixWord ++ tailWord_3533878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533878).length < 2 ^ (prefixWord ++ tailWord_3533878).sum := by decide
  have hdescent : baseEnd_3533878 < baseStart_3533878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533885 : List Nat := [1, 4, 1, 3, 1, 2, 3, 3, 1, 4]
def baseStart_3533885 : Nat := 118140960795 + 3533885 * 2 ^ 59
def prefixEnd_3533885 : Nat := 4983230072969 + 3 ^ 40 * 3533885 * 2
def baseEnd_3533885 : Nat := 604860527571337130795155

theorem tailTrace_3533885 : CollatzResearch.WordTrace tailWord_3533885 prefixEnd_3533885 604860527571337130795155 := by
  unfold tailWord_3533885
  simp only [CollatzResearch.WordTrace]
  refine ⟨128891374802345659352875109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85927583201563772901916739 128891374802345659352875109)
  ·
    refine ⟨24167132775439811128664083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128891374802345659352875109 24167132775439811128664083)
    ·
      refine ⟨36250699163159716692996125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24167132775439811128664083 36250699163159716692996125)
      ·
        refine ⟨13594012186184893759873547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36250699163159716692996125 13594012186184893759873547)
        ·
          refine ⟨20391018279277340639810321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13594012186184893759873547 20391018279277340639810321)
          ·
            refine ⟨15293263709458005479857741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20391018279277340639810321 15293263709458005479857741)
            ·
              refine ⟨5734973891046752054946653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15293263709458005479857741 5734973891046752054946653)
              ·
                refine ⟨2150615209142532020604995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5734973891046752054946653 2150615209142532020604995)
                ·
                  refine ⟨3225922813713798030907493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150615209142532020604995 3225922813713798030907493)
                  ·
                    refine ⟨604860527571337130795155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3225922813713798030907493 604860527571337130795155)
                    ·
                      rfl

theorem cell23_3533885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 1, 4].length) (baseStart_3533885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533885 prefixEnd_3533885 := by exact prefixLift 3533885
  have htrace : WordTrace (prefixWord ++ tailWord_3533885) baseStart_3533885 baseEnd_3533885 := by
    simpa [prefixWord, tailWord_3533885, baseEnd_3533885] using wordTrace_append hprefix tailTrace_3533885
  have hstable : (prefixWord ++ tailWord_3533885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533885).length < 2 ^ (prefixWord ++ tailWord_3533885).sum := by decide
  have hdescent : baseEnd_3533885 < baseStart_3533885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533942 : List Nat := [5, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3]
def baseStart_3533942 : Nat := 118140960795 + 3533942 * 2 ^ 59
def prefixEnd_3533942 : Nat := 4983230072969 + 3 ^ 40 * 3533942 * 2
def baseEnd_3533942 : Nat := 1814610851111317669372703

theorem tailTrace_3533942 : CollatzResearch.WordTrace tailWord_3533942 prefixEnd_3533942 1814610851111317669372703 := by
  unfold tailWord_3533942
  simp only [CollatzResearch.WordTrace]
  refine ⟨8055840860196197380481255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85928969175426105391800053 8055840860196197380481255)
  ·
    refine ⟨12083761290294296070721883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8055840860196197380481255 12083761290294296070721883)
    ·
      refine ⟨18125641935441444106082825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12083761290294296070721883 18125641935441444106082825)
      ·
        refine ⟨13594231451581083079562119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18125641935441444106082825 13594231451581083079562119)
        ·
          refine ⟨20391347177371624619343179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13594231451581083079562119 20391347177371624619343179)
          ·
            refine ⟨30587020766057436929014769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20391347177371624619343179 30587020766057436929014769)
            ·
              refine ⟨22940265574543077696761077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30587020766057436929014769 22940265574543077696761077)
              ·
                refine ⟨2150649897613413534071351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22940265574543077696761077 2150649897613413534071351)
                ·
                  refine ⟨3225974846420120301107027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150649897613413534071351 3225974846420120301107027)
                  ·
                    refine ⟨4838962269630180451660541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3225974846420120301107027 4838962269630180451660541)
                    ·
                      refine ⟨1814610851111317669372703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4838962269630180451660541 1814610851111317669372703)
                      ·
                        rfl

theorem cell23_3533942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_3533942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533942 prefixEnd_3533942 := by exact prefixLift 3533942
  have htrace : WordTrace (prefixWord ++ tailWord_3533942) baseStart_3533942 baseEnd_3533942 := by
    simpa [prefixWord, tailWord_3533942, baseEnd_3533942] using wordTrace_append hprefix tailTrace_3533942
  have hstable : (prefixWord ++ tailWord_3533942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533942).length < 2 ^ (prefixWord ++ tailWord_3533942).sum := by decide
  have hdescent : baseEnd_3533942 < baseStart_3533942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533945 : List Nat := [1, 2, 1, 3, 5, 1, 3, 1, 1, 5]
def baseStart_3533945 : Nat := 118140960795 + 3533945 * 2 ^ 59
def prefixEnd_3533945 : Nat := 4983230072969 + 3 ^ 40 * 3533945 * 2
def baseEnd_3533945 : Nat := 604870797184427052545063

theorem tailTrace_3533945 : CollatzResearch.WordTrace tailWord_3533945 prefixEnd_3533945 604870797184427052545063 := by
  unfold tailWord_3533945
  simp only [CollatzResearch.WordTrace]
  refine ⟨128893563182128289600059289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85929042121418859733372859 128893563182128289600059289)
  ·
    refine ⟨96670172386596217200044467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128893563182128289600059289 96670172386596217200044467)
    ·
      refine ⟨145005258579894325800066701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96670172386596217200044467 145005258579894325800066701)
      ·
        refine ⟨54376971967460372175025013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145005258579894325800066701 54376971967460372175025013)
        ·
          refine ⟨5097841121949409891408595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54376971967460372175025013 5097841121949409891408595)
          ·
            refine ⟨7646761682924114837112893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5097841121949409891408595 7646761682924114837112893)
            ·
              refine ⟨2867535631096543063917335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7646761682924114837112893 2867535631096543063917335)
              ·
                refine ⟨4301303446644814595876003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2867535631096543063917335 4301303446644814595876003)
                ·
                  refine ⟨6451955169967221893814005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4301303446644814595876003 6451955169967221893814005)
                  ·
                    refine ⟨604870797184427052545063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6451955169967221893814005 604870797184427052545063)
                    ·
                      rfl

theorem cell23_3533945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 1, 5].length) (baseStart_3533945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533945 prefixEnd_3533945 := by exact prefixLift 3533945
  have htrace : WordTrace (prefixWord ++ tailWord_3533945) baseStart_3533945 baseEnd_3533945 := by
    simpa [prefixWord, tailWord_3533945, baseEnd_3533945] using wordTrace_append hprefix tailTrace_3533945
  have hstable : (prefixWord ++ tailWord_3533945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533945).length < 2 ^ (prefixWord ++ tailWord_3533945).sum := by decide
  have hdescent : baseEnd_3533945 < baseStart_3533945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533978 : List Nat := [3, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3533978 : Nat := 118140960795 + 3533978 * 2 ^ 59
def prefixEnd_3533978 : Nat := 4983230072969 + 3 ^ 40 * 3533978 * 2
def baseEnd_3533978 : Nat := 1814629336414879528522537

theorem tailTrace_3533978 : CollatzResearch.WordTrace tailWord_3533978 prefixEnd_3533978 1814629336414879528522537 := by
  unfold tailWord_3533978
  simp only [CollatzResearch.WordTrace]
  refine ⟨32223691697752184059002647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85929844527339157490673725 32223691697752184059002647)
  ·
    refine ⟨48335537546628276088503971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32223691697752184059002647 48335537546628276088503971)
    ·
      refine ⟨72503306319942414132755957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48335537546628276088503971 72503306319942414132755957)
      ·
        refine ⟨6797184967494601324945871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72503306319942414132755957 6797184967494601324945871)
        ·
          refine ⟨10195777451241901987418807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6797184967494601324945871 10195777451241901987418807)
          ·
            refine ⟨15293666176862852981128211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10195777451241901987418807 15293666176862852981128211)
            ·
              refine ⟨22940499265294279471692317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15293666176862852981128211 22940499265294279471692317)
              ·
                refine ⟨8602687224485354801884619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22940499265294279471692317 8602687224485354801884619)
                ·
                  refine ⟨12904030836728032202826929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8602687224485354801884619 12904030836728032202826929)
                  ·
                    refine ⟨9678023127546024152120197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12904030836728032202826929 9678023127546024152120197)
                    ·
                      refine ⟨1814629336414879528522537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9678023127546024152120197 1814629336414879528522537)
                      ·
                        rfl

theorem cell23_3533978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3533978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533978 prefixEnd_3533978 := by exact prefixLift 3533978
  have htrace : WordTrace (prefixWord ++ tailWord_3533978) baseStart_3533978 baseEnd_3533978 := by
    simpa [prefixWord, tailWord_3533978, baseEnd_3533978] using wordTrace_append hprefix tailTrace_3533978
  have hstable : (prefixWord ++ tailWord_3533978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533978).length < 2 ^ (prefixWord ++ tailWord_3533978).sum := by decide
  have hdescent : baseEnd_3533978 < baseStart_3533978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533982 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_3533982 : Nat := 118140960795 + 3533982 * 2 ^ 59
def prefixEnd_3533982 : Nat := 4983230072969 + 3 ^ 40 * 3533982 * 2
def baseEnd_3533982 : Nat := 1814631390337497512872519

theorem tailTrace_3533982 : CollatzResearch.WordTrace tailWord_3533982 prefixEnd_3533982 1814631390337497512872519 := by
  unfold tailWord_3533982
  simp only [CollatzResearch.WordTrace]
  refine ⟨16111864085374280614894525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85929941788662829946104133 16111864085374280614894525)
  ·
    refine ⟨6041949032015355230585447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16111864085374280614894525 6041949032015355230585447)
    ·
      refine ⟨9062923548023032845878171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6041949032015355230585447 9062923548023032845878171)
      ·
        refine ⟨13594385322034549268817257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9062923548023032845878171 13594385322034549268817257)
        ·
          refine ⟨10195788991525911951612943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13594385322034549268817257 10195788991525911951612943)
          ·
            refine ⟨15293683487288867927419415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10195788991525911951612943 15293683487288867927419415)
            ·
              refine ⟨22940525230933301891129123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15293683487288867927419415 22940525230933301891129123)
              ·
                refine ⟨34410787846399952836693685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22940525230933301891129123 34410787846399952836693685)
                ·
                  refine ⟨3226011360599995578440033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34410787846399952836693685 3226011360599995578440033)
                  ·
                    refine ⟨2419508520449996683830025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3226011360599995578440033 2419508520449996683830025)
                    ·
                      refine ⟨1814631390337497512872519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2419508520449996683830025 1814631390337497512872519)
                      ·
                        rfl

theorem cell23_3533982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_3533982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533982 prefixEnd_3533982 := by exact prefixLift 3533982
  have htrace : WordTrace (prefixWord ++ tailWord_3533982) baseStart_3533982 baseEnd_3533982 := by
    simpa [prefixWord, tailWord_3533982, baseEnd_3533982] using wordTrace_append hprefix tailTrace_3533982
  have hstable : (prefixWord ++ tailWord_3533982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533982).length < 2 ^ (prefixWord ++ tailWord_3533982).sum := by decide
  have hdescent : baseEnd_3533982 < baseStart_3533982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3533988 : List Nat := [2, 3, 1, 2, 3, 2, 3, 7]
def baseStart_3533988 : Nat := 118140960795 + 3533988 * 2 ^ 59
def prefixEnd_3533988 : Nat := 4983230072969 + 3 ^ 40 * 3533988 * 2
def baseEnd_3533988 : Nat := 67208684119312018125833

theorem tailTrace_3533988 : CollatzResearch.WordTrace tailWord_3533988 prefixEnd_3533988 67208684119312018125833 := by
  unfold tailWord_3533988
  simp only [CollatzResearch.WordTrace]
  refine ⟨64447565760486253971937309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85930087680648338629249745 64447565760486253971937309)
  ·
    refine ⟨24167837160182345239476491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64447565760486253971937309 24167837160182345239476491)
    ·
      refine ⟨36251755740273517859214737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24167837160182345239476491 36251755740273517859214737)
      ·
        refine ⟨27188816805205138394411053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36251755740273517859214737 27188816805205138394411053)
        ·
          refine ⟨10195806301951926897904145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27188816805205138394411053 10195806301951926897904145)
          ·
            refine ⟨7646854726463945173428109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10195806301951926897904145 7646854726463945173428109)
            ·
              refine ⟨2867570522423979440035541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7646854726463945173428109 2867570522423979440035541)
              ·
                refine ⟨67208684119312018125833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2867570522423979440035541 67208684119312018125833)
                ·
                  rfl

theorem cell23_3533988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 7].length) (baseStart_3533988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3533988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3533988 prefixEnd_3533988 := by exact prefixLift 3533988
  have htrace : WordTrace (prefixWord ++ tailWord_3533988) baseStart_3533988 baseEnd_3533988 := by
    simpa [prefixWord, tailWord_3533988, baseEnd_3533988] using wordTrace_append hprefix tailTrace_3533988
  have hstable : (prefixWord ++ tailWord_3533988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3533988).length < 2 ^ (prefixWord ++ tailWord_3533988).sum := by decide
  have hdescent : baseEnd_3533988 < baseStart_3533988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3533988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534002 : List Nat := [3, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3]
def baseStart_3534002 : Nat := 118140960795 + 3534002 * 2 ^ 59
def prefixEnd_3534002 : Nat := 4983230072969 + 3 ^ 40 * 3534002 * 2
def baseEnd_3534002 : Nat := 1814641659950587434622427

theorem tailTrace_3534002 : CollatzResearch.WordTrace tailWord_3534002 prefixEnd_3534002 1814641659950587434622427 := by
  unfold tailWord_3534002
  simp only [CollatzResearch.WordTrace]
  refine ⟨32223910535730447083721065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85930428095281192223256173 32223910535730447083721065)
  ·
    refine ⟨24167932901797835312790799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32223910535730447083721065 24167932901797835312790799)
    ·
      refine ⟨36251899352696752969186199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24167932901797835312790799 36251899352696752969186199)
      ·
        refine ⟨54377849029045129453779299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36251899352696752969186199 54377849029045129453779299)
        ·
          refine ⟨81566773543567694180668949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54377849029045129453779299 81566773543567694180668949)
          ·
            refine ⟨3823442509854735664718857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81566773543567694180668949 3823442509854735664718857)
            ·
              refine ⟨2867581882391051748539143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3823442509854735664718857 2867581882391051748539143)
              ·
                refine ⟨4301372823586577622808715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2867581882391051748539143 4301372823586577622808715)
                ·
                  refine ⟨6452059235379866434213073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4301372823586577622808715 6452059235379866434213073)
                  ·
                    refine ⟨4839044426534899825659805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6452059235379866434213073 4839044426534899825659805)
                    ·
                      refine ⟨1814641659950587434622427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4839044426534899825659805 1814641659950587434622427)
                      ·
                        rfl

theorem cell23_3534002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3].length) (baseStart_3534002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534002 prefixEnd_3534002 := by exact prefixLift 3534002
  have htrace : WordTrace (prefixWord ++ tailWord_3534002) baseStart_3534002 baseEnd_3534002 := by
    simpa [prefixWord, tailWord_3534002, baseEnd_3534002] using wordTrace_append hprefix tailTrace_3534002
  have hstable : (prefixWord ++ tailWord_3534002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534002).length < 2 ^ (prefixWord ++ tailWord_3534002).sum := by decide
  have hdescent : baseEnd_3534002 < baseStart_3534002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534008 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 5, 3, 2]
def baseStart_3534008 : Nat := 118140960795 + 3534008 * 2 ^ 59
def prefixEnd_3534008 : Nat := 4983230072969 + 3 ^ 40 * 3534008 * 2
def baseEnd_3534008 : Nat := 1814644740834514411147399

theorem tailTrace_3534008 : CollatzResearch.WordTrace tailWord_3534008 prefixEnd_3534008 1814644740834514411147399 := by
  unfold tailWord_3534008
  simp only [CollatzResearch.WordTrace]
  refine ⟨64447930490450025679801339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85930573987266700906401785 64447930490450025679801339)
  ·
    refine ⟨96671895735675038519702009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64447930490450025679801339 96671895735675038519702009)
    ·
      refine ⟨72503921801756278889776507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96671895735675038519702009 72503921801756278889776507)
      ·
        refine ⟨108755882702634418334664761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72503921801756278889776507 108755882702634418334664761)
        ·
          refine ⟨81566912026975813750998571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108755882702634418334664761 81566912026975813750998571)
          ·
            refine ⟨122350368040463720626497857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81566912026975813750998571 122350368040463720626497857)
            ·
              refine ⟨91762776030347790469873393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122350368040463720626497857 91762776030347790469873393)
              ·
                refine ⟨68822082022760842852405045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 91762776030347790469873393 68822082022760842852405045)
                ·
                  refine ⟨6452070189633829017412973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68822082022760842852405045 6452070189633829017412973)
                  ·
                    refine ⟨2419526321112685881529865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6452070189633829017412973 2419526321112685881529865)
                    ·
                      refine ⟨1814644740834514411147399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2419526321112685881529865 1814644740834514411147399)
                      ·
                        rfl

theorem cell23_3534008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 5, 3, 2].length) (baseStart_3534008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534008 prefixEnd_3534008 := by exact prefixLift 3534008
  have htrace : WordTrace (prefixWord ++ tailWord_3534008) baseStart_3534008 baseEnd_3534008 := by
    simpa [prefixWord, tailWord_3534008, baseEnd_3534008] using wordTrace_append hprefix tailTrace_3534008
  have hstable : (prefixWord ++ tailWord_3534008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534008).length < 2 ^ (prefixWord ++ tailWord_3534008).sum := by decide
  have hdescent : baseEnd_3534008 < baseStart_3534008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534015 : List Nat := [1, 1, 2, 2, 2, 2, 5, 2, 2, 1, 3]
def baseStart_3534015 : Nat := 118140960795 + 3534015 * 2 ^ 59
def prefixEnd_3534015 : Nat := 4983230072969 + 3 ^ 40 * 3534015 * 2
def baseEnd_3534015 : Nat := 1814648335199095883759867

theorem tailTrace_3534015 : CollatzResearch.WordTrace tailWord_3534015 prefixEnd_3534015 1814648335199095883759867 := by
  unfold tailWord_3534015
  simp only [CollatzResearch.WordTrace]
  refine ⟨128896116291874691555107499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85930744194583127703404999 128896116291874691555107499)
  ·
    refine ⟨193344174437812037332661249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128896116291874691555107499 193344174437812037332661249)
    ·
      refine ⟨145008130828359027999495937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193344174437812037332661249 145008130828359027999495937)
      ·
        refine ⟨108756098121269270999621953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145008130828359027999495937 108756098121269270999621953)
        ·
          refine ⟨81567073590951953249716465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108756098121269270999621953 81567073590951953249716465)
          ·
            refine ⟨61175305193213964937287349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81567073590951953249716465 61175305193213964937287349)
            ·
              refine ⟨5735184861863809212870689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61175305193213964937287349 5735184861863809212870689)
              ·
                refine ⟨4301388646397856909653017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5735184861863809212870689 4301388646397856909653017)
                ·
                  refine ⟨3226041484798392682239763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4301388646397856909653017 3226041484798392682239763)
                  ·
                    refine ⟨4839062227197589023359645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3226041484798392682239763 4839062227197589023359645)
                    ·
                      refine ⟨1814648335199095883759867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4839062227197589023359645 1814648335199095883759867)
                      ·
                        rfl

theorem cell23_3534015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 1, 3].length) (baseStart_3534015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534015 prefixEnd_3534015 := by exact prefixLift 3534015
  have htrace : WordTrace (prefixWord ++ tailWord_3534015) baseStart_3534015 baseEnd_3534015 := by
    simpa [prefixWord, tailWord_3534015, baseEnd_3534015] using wordTrace_append hprefix tailTrace_3534015
  have hstable : (prefixWord ++ tailWord_3534015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534015).length < 2 ^ (prefixWord ++ tailWord_3534015).sum := by decide
  have hdescent : baseEnd_3534015 < baseStart_3534015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534029 : List Nat := [1, 6, 2, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_3534029 : Nat := 118140960795 + 3534029 * 2 ^ 59
def prefixEnd_3534029 : Nat := 4983230072969 + 3 ^ 40 * 3534029 * 2
def baseEnd_3534029 : Nat := 1814655523928258828984803

theorem tailTrace_3534029 : CollatzResearch.WordTrace tailWord_3534029 prefixEnd_3534029 1814655523928258828984803 := by
  unfold tailWord_3534029
  simp only [CollatzResearch.WordTrace]
  refine ⟨128896626913823971946117141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85931084609215981297411427 128896626913823971946117141)
  ·
    refine ⟨6042029386585498684974241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 128896626913823971946117141 6042029386585498684974241)
    ·
      refine ⟨4531522039939124013730681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6042029386585498684974241 4531522039939124013730681)
      ·
        refine ⟨3398641529954343010298011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4531522039939124013730681 3398641529954343010298011)
        ·
          refine ⟨5097962294931514515447017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3398641529954343010298011 5097962294931514515447017)
          ·
            refine ⟨3823471721198635886585263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5097962294931514515447017 3823471721198635886585263)
            ·
              refine ⟨5735207581797953829877895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3823471721198635886585263 5735207581797953829877895)
              ·
                refine ⟨8602811372696930744816843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5735207581797953829877895 8602811372696930744816843)
                ·
                  refine ⟨12904217059045396117225265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8602811372696930744816843 12904217059045396117225265)
                  ·
                    refine ⟨9678162794284047087918949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12904217059045396117225265 9678162794284047087918949)
                    ·
                      refine ⟨1814655523928258828984803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9678162794284047087918949 1814655523928258828984803)
                      ·
                        rfl

theorem cell23_3534029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_3534029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534029 prefixEnd_3534029 := by exact prefixLift 3534029
  have htrace : WordTrace (prefixWord ++ tailWord_3534029) baseStart_3534029 baseEnd_3534029 := by
    simpa [prefixWord, tailWord_3534029, baseEnd_3534029] using wordTrace_append hprefix tailTrace_3534029
  have hstable : (prefixWord ++ tailWord_3534029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534029).length < 2 ^ (prefixWord ++ tailWord_3534029).sum := by decide
  have hdescent : baseEnd_3534029 < baseStart_3534029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534041 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 2, 1, 5]
def baseStart_3534041 : Nat := 118140960795 + 3534041 * 2 ^ 59
def prefixEnd_3534041 : Nat := 4983230072969 + 3 ^ 40 * 3534041 * 2
def baseEnd_3534041 : Nat := 1814661685696112782034747

theorem tailTrace_3534041 : CollatzResearch.WordTrace tailWord_3534041 prefixEnd_3534041 1814661685696112782034747 := by
  unfold tailWord_3534041
  simp only [CollatzResearch.WordTrace]
  refine ⟨128897064589780497995553977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85931376393186998663702651 128897064589780497995553977)
  ·
    refine ⟨96672798442335373496665483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128897064589780497995553977 96672798442335373496665483)
    ·
      refine ⟨145009197663503060244998225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96672798442335373496665483 145009197663503060244998225)
      ·
        refine ⟨108756898247627295183748669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145009197663503060244998225 108756898247627295183748669)
        ·
          refine ⟨40783836842860235693905751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108756898247627295183748669 40783836842860235693905751)
          ·
            refine ⟨61175755264290353540858627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40783836842860235693905751 61175755264290353540858627)
            ·
              refine ⟨91763632896435530311287941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61175755264290353540858627 91763632896435530311287941)
              ·
                refine ⟨17205681168081661933366489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 91763632896435530311287941 17205681168081661933366489)
                ·
                  refine ⟨12904260876061246450024867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17205681168081661933366489 12904260876061246450024867)
                  ·
                    refine ⟨19356391314091869675037301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12904260876061246450024867 19356391314091869675037301)
                    ·
                      refine ⟨1814661685696112782034747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19356391314091869675037301 1814661685696112782034747)
                      ·
                        rfl

theorem cell23_3534041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_3534041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534041 prefixEnd_3534041 := by exact prefixLift 3534041
  have htrace : WordTrace (prefixWord ++ tailWord_3534041) baseStart_3534041 baseEnd_3534041 := by
    simpa [prefixWord, tailWord_3534041, baseEnd_3534041] using wordTrace_append hprefix tailTrace_3534041
  have hstable : (prefixWord ++ tailWord_3534041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534041).length < 2 ^ (prefixWord ++ tailWord_3534041).sum := by decide
  have hdescent : baseEnd_3534041 < baseStart_3534041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534058 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_3534058 : Nat := 118140960795 + 3534058 * 2 ^ 59
def prefixEnd_3534058 : Nat := 4983230072969 + 3 ^ 40 * 3534058 * 2
def baseEnd_3534058 : Nat := 1814670414867239215522169

theorem tailTrace_3534058 : CollatzResearch.WordTrace tailWord_3534058 prefixEnd_3534058 1814670414867239215522169 := by
  unfold tailWord_3534058
  simp only [CollatzResearch.WordTrace]
  refine ⟨32224421157679727474730707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85931789753812606599281885 32224421157679727474730707)
  ·
    refine ⟨48336631736519591212096061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32224421157679727474730707 48336631736519591212096061)
    ·
      refine ⟨18126236901194846704536023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48336631736519591212096061 18126236901194846704536023)
      ·
        refine ⟨27189355351792270056804035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18126236901194846704536023 27189355351792270056804035)
        ·
          refine ⟨40784033027688405085206053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27189355351792270056804035 40784033027688405085206053)
          ·
            refine ⟨7647006192691575953476135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40784033027688405085206053 7647006192691575953476135)
            ·
              refine ⟨11470509289037363930214203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7647006192691575953476135 11470509289037363930214203)
              ·
                refine ⟨17205763933556045895321305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11470509289037363930214203 17205763933556045895321305)
                ·
                  refine ⟨12904322950167034421490979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17205763933556045895321305 12904322950167034421490979)
                  ·
                    refine ⟨19356484425250551632236469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12904322950167034421490979 19356484425250551632236469)
                    ·
                      refine ⟨1814670414867239215522169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19356484425250551632236469 1814670414867239215522169)
                      ·
                        rfl

theorem cell23_3534058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_3534058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534058 prefixEnd_3534058 := by exact prefixLift 3534058
  have htrace : WordTrace (prefixWord ++ tailWord_3534058) baseStart_3534058 baseEnd_3534058 := by
    simpa [prefixWord, tailWord_3534058, baseEnd_3534058] using wordTrace_append hprefix tailTrace_3534058
  have hstable : (prefixWord ++ tailWord_3534058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534058).length < 2 ^ (prefixWord ++ tailWord_3534058).sum := by decide
  have hdescent : baseEnd_3534058 < baseStart_3534058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534101 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_3534101 : Nat := 118140960795 + 3534101 * 2 ^ 59
def prefixEnd_3534101 : Nat := 4983230072969 + 3 ^ 40 * 3534101 * 2
def baseEnd_3534101 : Nat := 1814692494535382547284471

theorem tailTrace_3534101 : CollatzResearch.WordTrace tailWord_3534101 prefixEnd_3534101 1814692494535382547284471 := by
  unfold tailWord_3534101
  simp only [CollatzResearch.WordTrace]
  refine ⟨128899252969563128242738157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85932835313042085495158771 128899252969563128242738157)
  ·
    refine ⟨48337219863586173091026809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128899252969563128242738157 48337219863586173091026809)
    ·
      refine ⟨36252914897689629818270107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48337219863586173091026809 36252914897689629818270107)
      ·
        refine ⟨54379372346534444727405161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36252914897689629818270107 54379372346534444727405161)
        ·
          refine ⟨40784529259900833545553871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54379372346534444727405161 40784529259900833545553871)
          ·
            refine ⟨61176793889851250318330807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40784529259900833545553871 61176793889851250318330807)
            ·
              refine ⟨91765190834776875477496211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61176793889851250318330807 91765190834776875477496211)
              ·
                refine ⟨137647786252165313216244317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91765190834776875477496211 137647786252165313216244317)
                ·
                  refine ⟨51617919844561992456091619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137647786252165313216244317 51617919844561992456091619)
                  ·
                    refine ⟨77426879766842988684137429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51617919844561992456091619 77426879766842988684137429)
                    ·
                      refine ⟨1814692494535382547284471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77426879766842988684137429 1814692494535382547284471)
                      ·
                        rfl

theorem cell23_3534101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_3534101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534101 prefixEnd_3534101 := by exact prefixLift 3534101
  have htrace : WordTrace (prefixWord ++ tailWord_3534101) baseStart_3534101 baseEnd_3534101 := by
    simpa [prefixWord, tailWord_3534101, baseEnd_3534101] using wordTrace_append hprefix tailTrace_3534101
  have hstable : (prefixWord ++ tailWord_3534101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534101).length < 2 ^ (prefixWord ++ tailWord_3534101).sum := by decide
  have hdescent : baseEnd_3534101 < baseStart_3534101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534108 : List Nat := [2, 2, 3, 1, 1, 1, 3, 3, 2, 5]
def baseStart_3534108 : Nat := 118140960795 + 3534108 * 2 ^ 59
def prefixEnd_3534108 : Nat := 4983230072969 + 3 ^ 40 * 3534108 * 2
def baseEnd_3534108 : Nat := 604898696299988006632313

theorem tailTrace_3534108 : CollatzResearch.WordTrace tailWord_3534108 prefixEnd_3534108 604898696299988006632313 := by
  unfold tailWord_3534108
  simp only [CollatzResearch.WordTrace]
  refine ⟨64449754140268884219121489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85933005520358512292161985 64449754140268884219121489)
  ·
    refine ⟨48337315605201663164341117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64449754140268884219121489 48337315605201663164341117)
    ·
      refine ⟨18126493351950623686627919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48337315605201663164341117 18126493351950623686627919)
      ·
        refine ⟨27189740027925935529941879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18126493351950623686627919 27189740027925935529941879)
        ·
          refine ⟨40784610041888903294912819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27189740027925935529941879 40784610041888903294912819)
          ·
            refine ⟨61176915062833354942369229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40784610041888903294912819 61176915062833354942369229)
            ·
              refine ⟨22941343148562508103388461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61176915062833354942369229 22941343148562508103388461)
              ·
                refine ⟨8603003680710940538770673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22941343148562508103388461 8603003680710940538770673)
                ·
                  refine ⟨6452252760533205404078005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8603003680710940538770673 6452252760533205404078005)
                  ·
                    refine ⟨604898696299988006632313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6452252760533205404078005 604898696299988006632313)
                    ·
                      rfl

theorem cell23_3534108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_3534108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534108 prefixEnd_3534108 := by exact prefixLift 3534108
  have htrace : WordTrace (prefixWord ++ tailWord_3534108) baseStart_3534108 baseEnd_3534108 := by
    simpa [prefixWord, tailWord_3534108, baseEnd_3534108] using wordTrace_append hprefix tailTrace_3534108
  have hstable : (prefixWord ++ tailWord_3534108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534108).length < 2 ^ (prefixWord ++ tailWord_3534108).sum := by decide
  have hdescent : baseEnd_3534108 < baseStart_3534108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534128 : List Nat := [2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 4]
def baseStart_3534128 : Nat := 118140960795 + 3534128 * 2 ^ 59
def prefixEnd_3534128 : Nat := 4983230072969 + 3 ^ 40 * 3534128 * 2
def baseEnd_3534128 : Nat := 1814706358513053941646847

theorem tailTrace_3534128 : CollatzResearch.WordTrace tailWord_3534128 prefixEnd_3534128 1814706358513053941646847 := by
  unfold tailWord_3534128
  simp only [CollatzResearch.WordTrace]
  refine ⟨64450118870232655926985519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85933491826976874569314025 64450118870232655926985519)
  ·
    refine ⟨96675178305348983890478279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64450118870232655926985519 96675178305348983890478279)
    ·
      refine ⟨145012767458023475835717419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96675178305348983890478279 145012767458023475835717419)
      ·
        refine ⟨217519151187035213753576129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145012767458023475835717419 217519151187035213753576129)
        ·
          refine ⟨163139363390276410315182097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217519151187035213753576129 163139363390276410315182097)
          ·
            refine ⟨122354522542707307736386573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163139363390276410315182097 122354522542707307736386573)
            ·
              refine ⟨45882945953515240401144965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 122354522542707307736386573 45882945953515240401144965)
              ·
                refine ⟨8603052366284107575214681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45882945953515240401144965 8603052366284107575214681)
                ·
                  refine ⟨6452289274713080681411011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8603052366284107575214681 6452289274713080681411011)
                  ·
                    refine ⟨9678433912069621022116517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6452289274713080681411011 9678433912069621022116517)
                    ·
                      refine ⟨1814706358513053941646847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9678433912069621022116517 1814706358513053941646847)
                      ·
                        rfl

theorem cell23_3534128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 4].length) (baseStart_3534128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534128 prefixEnd_3534128 := by exact prefixLift 3534128
  have htrace : WordTrace (prefixWord ++ tailWord_3534128) baseStart_3534128 baseEnd_3534128 := by
    simpa [prefixWord, tailWord_3534128, baseEnd_3534128] using wordTrace_append hprefix tailTrace_3534128
  have hstable : (prefixWord ++ tailWord_3534128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534128).length < 2 ^ (prefixWord ++ tailWord_3534128).sum := by decide
  have hdescent : baseEnd_3534128 < baseStart_3534128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534165 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 1, 4, 3]
def baseStart_3534165 : Nat := 118140960795 + 3534165 * 2 ^ 59
def prefixEnd_3534165 : Nat := 4983230072969 + 3 ^ 40 * 3534165 * 2
def baseEnd_3534165 : Nat := 1814725357297270296884177

theorem tailTrace_3534165 : CollatzResearch.WordTrace tailWord_3534165 prefixEnd_3534165 1814725357297270296884177 := by
  unfold tailWord_3534165
  simp only [CollatzResearch.WordTrace]
  refine ⟨128901587241331267173067949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85934391494220844782045299 128901587241331267173067949)
  ·
    refine ⟨48338095215499225189900481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128901587241331267173067949 48338095215499225189900481)
    ·
      refine ⟨36253571411624418892425361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48338095215499225189900481 36253571411624418892425361)
      ·
        refine ⟨27190178558718314169319021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36253571411624418892425361 27190178558718314169319021)
        ·
          refine ⟨10196316959519367813494633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27190178558718314169319021 10196316959519367813494633)
          ·
            refine ⟨7647237719639525860120975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10196316959519367813494633 7647237719639525860120975)
            ·
              refine ⟨11470856579459288790181463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7647237719639525860120975 11470856579459288790181463)
              ·
                refine ⟨17206284869188933185272195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11470856579459288790181463 17206284869188933185272195)
                ·
                  refine ⟨25809427303783399777908293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17206284869188933185272195 25809427303783399777908293)
                  ·
                    refine ⟨4839267619459387458357805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25809427303783399777908293 4839267619459387458357805)
                    ·
                      refine ⟨1814725357297270296884177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4839267619459387458357805 1814725357297270296884177)
                      ·
                        rfl

theorem cell23_3534165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_3534165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534165 prefixEnd_3534165 := by exact prefixLift 3534165
  have htrace : WordTrace (prefixWord ++ tailWord_3534165) baseStart_3534165 baseEnd_3534165 := by
    simpa [prefixWord, tailWord_3534165, baseEnd_3534165] using wordTrace_append hprefix tailTrace_3534165
  have hstable : (prefixWord ++ tailWord_3534165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534165).length < 2 ^ (prefixWord ++ tailWord_3534165).sum := by decide
  have hdescent : baseEnd_3534165 < baseStart_3534165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534188 : List Nat := [2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 6]
def baseStart_3534188 : Nat := 118140960795 + 3534188 * 2 ^ 59
def prefixEnd_3534188 : Nat := 4983230072969 + 3 ^ 40 * 3534188 * 2
def baseEnd_3534188 : Nat := 1814737167352323706896571

theorem tailTrace_3534188 : CollatzResearch.WordTrace tailWord_3534188 prefixEnd_3534188 1814737167352323706896571 := by
  unfold tailWord_3534188
  simp only [CollatzResearch.WordTrace]
  refine ⟨64451213060123971050577609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85934950746831961400770145 64451213060123971050577609)
  ·
    refine ⟨48338409795092978287933207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64451213060123971050577609 48338409795092978287933207)
    ·
      refine ⟨72507614692639467431899811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48338409795092978287933207 72507614692639467431899811)
      ·
        refine ⟨108761422038959201147849717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72507614692639467431899811 108761422038959201147849717)
        ·
          refine ⟨10196383316152425107610911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108761422038959201147849717 10196383316152425107610911)
          ·
            refine ⟨15294574974228637661416367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10196383316152425107610911 15294574974228637661416367)
            ·
              refine ⟨22941862461342956492124551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15294574974228637661416367 22941862461342956492124551)
              ·
                refine ⟨34412793692014434738186827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22941862461342956492124551 34412793692014434738186827)
                ·
                  refine ⟨51619190538021652107280241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34412793692014434738186827 51619190538021652107280241)
                  ·
                    refine ⟨38714392903516239080460181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51619190538021652107280241 38714392903516239080460181)
                    ·
                      refine ⟨1814737167352323706896571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38714392903516239080460181 1814737167352323706896571)
                      ·
                        rfl

theorem cell23_3534188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 6].length) (baseStart_3534188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534188 prefixEnd_3534188 := by exact prefixLift 3534188
  have htrace : WordTrace (prefixWord ++ tailWord_3534188) baseStart_3534188 baseEnd_3534188 := by
    simpa [prefixWord, tailWord_3534188, baseEnd_3534188] using wordTrace_append hprefix tailTrace_3534188
  have hstable : (prefixWord ++ tailWord_3534188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534188).length < 2 ^ (prefixWord ++ tailWord_3534188).sum := by decide
  have hdescent : baseEnd_3534188 < baseStart_3534188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534205 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 3, 5, 2]
def baseStart_3534205 : Nat := 118140960795 + 3534205 * 2 ^ 59
def prefixEnd_3534205 : Nat := 4983230072969 + 3 ^ 40 * 3534205 * 2
def baseEnd_3534205 : Nat := 1814745896523450140383993

theorem tailTrace_3534205 : CollatzResearch.WordTrace tailWord_3534205 prefixEnd_3534205 1814745896523450140383993 := by
  unfold tailWord_3534205
  simp only [CollatzResearch.WordTrace]
  refine ⟨128903046161186354004524069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85935364107457569336349379 128903046161186354004524069)
  ·
    refine ⟨24169321155222441375848263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128903046161186354004524069 24169321155222441375848263)
    ·
      refine ⟨36253981732833662063772395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24169321155222441375848263 36253981732833662063772395)
      ·
        refine ⟨54380972599250493095658593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36253981732833662063772395 54380972599250493095658593)
        ·
          refine ⟨40785729449437869821743945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54380972599250493095658593 40785729449437869821743945)
          ·
            refine ⟨30589297087078402366307959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40785729449437869821743945 30589297087078402366307959)
            ·
              refine ⟨45883945630617603549461939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30589297087078402366307959 45883945630617603549461939)
              ·
                refine ⟨68825918445926405324192909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45883945630617603549461939 68825918445926405324192909)
                ·
                  refine ⟨25809719417222401996572341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 68825918445926405324192909 25809719417222401996572341)
                  ·
                    refine ⟨2419661195364600187178657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 25809719417222401996572341 2419661195364600187178657)
                    ·
                      refine ⟨1814745896523450140383993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2419661195364600187178657 1814745896523450140383993)
                      ·
                        rfl

theorem cell23_3534205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_3534205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534205 prefixEnd_3534205 := by exact prefixLift 3534205
  have htrace : WordTrace (prefixWord ++ tailWord_3534205) baseStart_3534205 baseEnd_3534205 := by
    simpa [prefixWord, tailWord_3534205, baseEnd_3534205] using wordTrace_append hprefix tailTrace_3534205
  have hstable : (prefixWord ++ tailWord_3534205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534205).length < 2 ^ (prefixWord ++ tailWord_3534205).sum := by decide
  have hdescent : baseEnd_3534205 < baseStart_3534205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534212 : List Nat := [2, 3, 2, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_3534212 : Nat := 118140960795 + 3534212 * 2 ^ 59
def prefixEnd_3534212 : Nat := 4983230072969 + 3 ^ 40 * 3534212 * 2
def baseEnd_3534212 : Nat := 1814749490888031612996461

theorem tailTrace_3534212 : CollatzResearch.WordTrace tailWord_3534212 prefixEnd_3534212 1814749490888031612996461 := by
  unfold tailWord_3534212
  simp only [CollatzResearch.WordTrace]
  refine ⟨64451650736080497100014445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85935534314773996133352593 64451650736080497100014445)
  ·
    refine ⟨24169369026030186412505417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64451650736080497100014445 24169369026030186412505417)
    ·
      refine ⟨18127026769522639809379063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24169369026030186412505417 18127026769522639809379063)
      ·
        refine ⟨27190540154283959714068595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18127026769522639809379063 27190540154283959714068595)
        ·
          refine ⟨40785810231425939571102893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27190540154283959714068595 40785810231425939571102893)
          ·
            refine ⟨15294678836784727339163585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40785810231425939571102893 15294678836784727339163585)
            ·
              refine ⟨11471009127588545504372689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15294678836784727339163585 11471009127588545504372689)
              ·
                refine ⟨8603256845691409128279517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11471009127588545504372689 8603256845691409128279517)
                ·
                  refine ⟨3226221317134278423104819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8603256845691409128279517 3226221317134278423104819)
                  ·
                    refine ⟨4839331975701417634657229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3226221317134278423104819 4839331975701417634657229)
                    ·
                      refine ⟨1814749490888031612996461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4839331975701417634657229 1814749490888031612996461)
                      ·
                        rfl

theorem cell23_3534212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_3534212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534212 prefixEnd_3534212 := by exact prefixLift 3534212
  have htrace : WordTrace (prefixWord ++ tailWord_3534212) baseStart_3534212 baseEnd_3534212 := by
    simpa [prefixWord, tailWord_3534212, baseEnd_3534212] using wordTrace_append hprefix tailTrace_3534212
  have hstable : (prefixWord ++ tailWord_3534212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534212).length < 2 ^ (prefixWord ++ tailWord_3534212).sum := by decide
  have hdescent : baseEnd_3534212 < baseStart_3534212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534215 : List Nat := [1, 1, 4, 2, 2, 2, 1, 4, 1, 5]
def baseStart_3534215 : Nat := 118140960795 + 3534215 * 2 ^ 59
def prefixEnd_3534215 : Nat := 4983230072969 + 3 ^ 40 * 3534215 * 2
def baseEnd_3534215 : Nat := 604917010443331700419649

theorem tailTrace_3534215 : CollatzResearch.WordTrace tailWord_3534215 prefixEnd_3534215 604917010443331700419649 := by
  unfold tailWord_3534215
  simp only [CollatzResearch.WordTrace]
  refine ⟨128903410891150125712388099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85935607260766750474925399 128903410891150125712388099)
  ·
    refine ⟨193355116336725188568582149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128903410891150125712388099 193355116336725188568582149)
    ·
      refine ⟨36254084313135972856609153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193355116336725188568582149 36254084313135972856609153)
      ·
        refine ⟨27190563234851979642456865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36254084313135972856609153 27190563234851979642456865)
        ·
          refine ⟨20392922426138984731842649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27190563234851979642456865 20392922426138984731842649)
          ·
            refine ⟨15294691819604238548881987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20392922426138984731842649 15294691819604238548881987)
            ·
              refine ⟨22942037729406357823322981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15294691819604238548881987 22942037729406357823322981)
              ·
                refine ⟨4301632074263692091873059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22942037729406357823322981 4301632074263692091873059)
                ·
                  refine ⟨6452448111395538137809589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4301632074263692091873059 6452448111395538137809589)
                  ·
                    refine ⟨604917010443331700419649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6452448111395538137809589 604917010443331700419649)
                    ·
                      rfl

theorem cell23_3534215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_3534215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534215 prefixEnd_3534215 := by exact prefixLift 3534215
  have htrace : WordTrace (prefixWord ++ tailWord_3534215) baseStart_3534215 baseEnd_3534215 := by
    simpa [prefixWord, tailWord_3534215, baseEnd_3534215] using wordTrace_append hprefix tailTrace_3534215
  have hstable : (prefixWord ++ tailWord_3534215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534215).length < 2 ^ (prefixWord ++ tailWord_3534215).sum := by decide
  have hdescent : baseEnd_3534215 < baseStart_3534215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534229 : List Nat := [1, 3, 2, 1, 1, 2, 5, 3, 1, 1, 3]
def baseStart_3534229 : Nat := 118140960795 + 3534229 * 2 ^ 59
def prefixEnd_3534229 : Nat := 4983230072969 + 3 ^ 40 * 3534229 * 2
def baseEnd_3534229 : Nat := 1814758220059158046483883

theorem tailTrace_3534229 : CollatzResearch.WordTrace tailWord_3534229 prefixEnd_3534229 1814758220059158046483883 := by
  unfold tailWord_3534229
  simp only [CollatzResearch.WordTrace]
  refine ⟨128903921513099406103397741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85935947675399604068931827 128903921513099406103397741)
  ·
    refine ⟨48338970567412277288774153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128903921513099406103397741 48338970567412277288774153)
    ·
      refine ⟨36254227925559207966580615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48338970567412277288774153 36254227925559207966580615)
      ·
        refine ⟨54381341888338811949870923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36254227925559207966580615 54381341888338811949870923)
        ·
          refine ⟨81572012832508217924806385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54381341888338811949870923 81572012832508217924806385)
          ·
            refine ⟨61179009624381163443604789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81572012832508217924806385 61179009624381163443604789)
            ·
              refine ⟨5735532152285734072837949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61179009624381163443604789 5735532152285734072837949)
              ·
                refine ⟨2150824557107150277314231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5735532152285734072837949 2150824557107150277314231)
                ·
                  refine ⟨3226236835660725415971347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150824557107150277314231 3226236835660725415971347)
                  ·
                    refine ⟨4839355253491088123957021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3226236835660725415971347 4839355253491088123957021)
                    ·
                      refine ⟨1814758220059158046483883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4839355253491088123957021 1814758220059158046483883)
                      ·
                        rfl

theorem cell23_3534229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3, 1, 1, 3].length) (baseStart_3534229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534229 prefixEnd_3534229 := by exact prefixLift 3534229
  have htrace : WordTrace (prefixWord ++ tailWord_3534229) baseStart_3534229 baseEnd_3534229 := by
    simpa [prefixWord, tailWord_3534229, baseEnd_3534229] using wordTrace_append hprefix tailTrace_3534229
  have hstable : (prefixWord ++ tailWord_3534229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534229).length < 2 ^ (prefixWord ++ tailWord_3534229).sum := by decide
  have hdescent : baseEnd_3534229 < baseStart_3534229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534272 : List Nat := [2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 3]
def baseStart_3534272 : Nat := 118140960795 + 3534272 * 2 ^ 59
def prefixEnd_3534272 : Nat := 4983230072969 + 3 ^ 40 * 3534272 * 2
def baseEnd_3534272 : Nat := 1814780299727301378246185

theorem tailTrace_3534272 : CollatzResearch.WordTrace tailWord_3534272 prefixEnd_3534272 1814780299727301378246185 := by
  unfold tailWord_3534272
  simp only [CollatzResearch.WordTrace]
  refine ⟨64452744925971812223606535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85936993234629082964808713 64452744925971812223606535)
  ·
    refine ⟨96679117388957718335409803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64452744925971812223606535 96679117388957718335409803)
    ·
      refine ⟨145018676083436577503114705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96679117388957718335409803 145018676083436577503114705)
      ·
        refine ⟨108764007062577433127336029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145018676083436577503114705 108764007062577433127336029)
        ·
          refine ⟨40786502648466537422751011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108764007062577433127336029 40786502648466537422751011)
          ·
            refine ⟨61179753972699806134126517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40786502648466537422751011 61179753972699806134126517)
            ·
              refine ⟨5735601934940606825074361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61179753972699806134126517 5735601934940606825074361)
              ·
                refine ⟨4301701451205455118805771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5735601934940606825074361 4301701451205455118805771)
                ·
                  refine ⟨6452552176808182678208657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4301701451205455118805771 6452552176808182678208657)
                  ·
                    refine ⟨4839414132606137008656493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6452552176808182678208657 4839414132606137008656493)
                    ·
                      refine ⟨1814780299727301378246185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4839414132606137008656493 1814780299727301378246185)
                      ·
                        rfl

theorem cell23_3534272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 3].length) (baseStart_3534272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534272 prefixEnd_3534272 := by exact prefixLift 3534272
  have htrace : WordTrace (prefixWord ++ tailWord_3534272) baseStart_3534272 baseEnd_3534272 := by
    simpa [prefixWord, tailWord_3534272, baseEnd_3534272] using wordTrace_append hprefix tailTrace_3534272
  have hstable : (prefixWord ++ tailWord_3534272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534272).length < 2 ^ (prefixWord ++ tailWord_3534272).sum := by decide
  have hdescent : baseEnd_3534272 < baseStart_3534272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534312 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 5, 3, 2]
def baseStart_3534312 : Nat := 118140960795 + 3534312 * 2 ^ 59
def prefixEnd_3534312 : Nat := 4983230072969 + 3 ^ 40 * 3534312 * 2
def baseEnd_3534312 : Nat := 1814800838953481221746001

theorem tailTrace_3534312 : CollatzResearch.WordTrace tailWord_3534312 prefixEnd_3534312 1814800838953481221746001 := by
  unfold tailWord_3534312
  simp only [CollatzResearch.WordTrace]
  refine ⟨64453474385899355639334595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85937965847865807519112793 64453474385899355639334595)
  ·
    refine ⟨96680211578849033459001893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64453474385899355639334595 96680211578849033459001893)
    ·
      refine ⟨18127539671034193773562855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 96680211578849033459001893 18127539671034193773562855)
      ·
        refine ⟨27191309506551290660344283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18127539671034193773562855 27191309506551290660344283)
        ·
          refine ⟨40786964259826935990516425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27191309506551290660344283 40786964259826935990516425)
          ·
            refine ⟨30590223194870201992887319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40786964259826935990516425 30590223194870201992887319)
            ·
              refine ⟨45885334792305302989330979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30590223194870201992887319 45885334792305302989330979)
              ·
                refine ⟨68828002188457954483996469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45885334792305302989330979 68828002188457954483996469)
                ·
                  refine ⟨6452625205167933232874669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68828002188457954483996469 6452625205167933232874669)
                  ·
                    refine ⟨2419734451937974962328001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6452625205167933232874669 2419734451937974962328001)
                    ·
                      refine ⟨1814800838953481221746001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2419734451937974962328001 1814800838953481221746001)
                      ·
                        rfl

theorem cell23_3534312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_3534312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534312 prefixEnd_3534312 := by exact prefixLift 3534312
  have htrace : WordTrace (prefixWord ++ tailWord_3534312) baseStart_3534312 baseEnd_3534312 := by
    simpa [prefixWord, tailWord_3534312, baseEnd_3534312] using wordTrace_append hprefix tailTrace_3534312
  have hstable : (prefixWord ++ tailWord_3534312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534312).length < 2 ^ (prefixWord ++ tailWord_3534312).sum := by decide
  have hdescent : baseEnd_3534312 < baseStart_3534312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534346 : List Nat := [3, 1, 2, 2, 2, 2, 4, 1, 1, 3, 2]
def baseStart_3534346 : Nat := 118140960795 + 3534346 * 2 ^ 59
def prefixEnd_3534346 : Nat := 4983230072969 + 3 ^ 40 * 3534346 * 2
def baseEnd_3534346 : Nat := 1814818297295734088720845

theorem tailTrace_3534346 : CollatzResearch.WordTrace tailWord_3534346 prefixEnd_3534346 1814818297295734088720845 := by
  unfold tailWord_3534346
  simp only [CollatzResearch.WordTrace]
  refine ⟨32227047213418883771351723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85938792569117023390271261 32227047213418883771351723)
  ·
    refine ⟨48340570820128325657027585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32227047213418883771351723 48340570820128325657027585)
    ·
      refine ⟨36255428115096244242770689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48340570820128325657027585 36255428115096244242770689)
      ·
        refine ⟨27191571086322183182078017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36255428115096244242770689 27191571086322183182078017)
        ·
          refine ⟨20393678314741637386558513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27191571086322183182078017 20393678314741637386558513)
          ·
            refine ⟨15295258736056228039918885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20393678314741637386558513 15295258736056228039918885)
            ·
              refine ⟨2867861013010542757484791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15295258736056228039918885 2867861013010542757484791)
              ·
                refine ⟨4301791519515814136227187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2867861013010542757484791 4301791519515814136227187)
                ·
                  refine ⟨6452687279273721204340781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4301791519515814136227187 6452687279273721204340781)
                  ·
                    refine ⟨2419757729727645451627793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6452687279273721204340781 2419757729727645451627793)
                    ·
                      refine ⟨1814818297295734088720845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2419757729727645451627793 1814818297295734088720845)
                      ·
                        rfl

theorem cell23_3534346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_3534346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534346 prefixEnd_3534346 := by exact prefixLift 3534346
  have htrace : WordTrace (prefixWord ++ tailWord_3534346) baseStart_3534346 baseEnd_3534346 := by
    simpa [prefixWord, tailWord_3534346, baseEnd_3534346] using wordTrace_append hprefix tailTrace_3534346
  have hstable : (prefixWord ++ tailWord_3534346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534346).length < 2 ^ (prefixWord ++ tailWord_3534346).sum := by decide
  have hdescent : baseEnd_3534346 < baseStart_3534346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534355 : List Nat := [1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 4]
def baseStart_3534355 : Nat := 118140960795 + 3534355 * 2 ^ 59
def prefixEnd_3534355 : Nat := 4983230072969 + 3 ^ 40 * 3534355 * 2
def baseEnd_3534355 : Nat := 1814822918621624553508303

theorem tailTrace_3534355 : CollatzResearch.WordTrace tailWord_3534355 prefixEnd_3534355 1814822918621624553508303 := by
  unfold tailWord_3534355
  simp only [CollatzResearch.WordTrace]
  refine ⟨128908517110642929622484519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85939011407095286414989679 128908517110642929622484519)
  ·
    refine ⟨193362775665964394433726779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128908517110642929622484519 193362775665964394433726779)
    ·
      refine ⟨290044163498946591650590169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193362775665964394433726779 290044163498946591650590169)
      ·
        refine ⟨217533122624209943737942627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 290044163498946591650590169 217533122624209943737942627)
        ·
          refine ⟨326299683936314915606913941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217533122624209943737942627 326299683936314915606913941)
          ·
            refine ⟨15295297684514761669074091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 326299683936314915606913941 15295297684514761669074091)
            ·
              refine ⟨22942946526772142503611137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15295297684514761669074091 22942946526772142503611137)
              ·
                refine ⟨17207209895079106877708353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22942946526772142503611137 17207209895079106877708353)
                ·
                  refine ⟨12905407421309330158281265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17207209895079106877708353 12905407421309330158281265)
                  ·
                    refine ⟨9679055565981997618710949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12905407421309330158281265 9679055565981997618710949)
                    ·
                      refine ⟨1814822918621624553508303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9679055565981997618710949 1814822918621624553508303)
                      ·
                        rfl

theorem cell23_3534355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_3534355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534355 prefixEnd_3534355 := by exact prefixLift 3534355
  have htrace : WordTrace (prefixWord ++ tailWord_3534355) baseStart_3534355 baseEnd_3534355 := by
    simpa [prefixWord, tailWord_3534355, baseEnd_3534355] using wordTrace_append hprefix tailTrace_3534355
  have hstable : (prefixWord ++ tailWord_3534355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534355).length < 2 ^ (prefixWord ++ tailWord_3534355).sum := by decide
  have hdescent : baseEnd_3534355 < baseStart_3534355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534382 : List Nat := [4, 1, 3, 1, 2, 1, 2, 2, 7]
def baseStart_3534382 : Nat := 118140960795 + 3534382 * 2 ^ 59
def prefixEnd_3534382 : Nat := 4983230072969 + 3 ^ 40 * 3534382 * 2
def baseEnd_3534382 : Nat := 201648531399921771985631

theorem tailTrace_3534382 : CollatzResearch.WordTrace tailWord_3534382 prefixEnd_3534382 201648531399921771985631 := by
  unfold tailWord_3534382
  simp only [CollatzResearch.WordTrace]
  refine ⟨16113687735193139154214675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85939667921030075489144933 16113687735193139154214675)
  ·
    refine ⟨24170531602789708731322013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16113687735193139154214675 24170531602789708731322013)
    ·
      refine ⟨9063949351046140774245755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24170531602789708731322013 9063949351046140774245755)
      ·
        refine ⟨13595924026569211161368633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9063949351046140774245755 13595924026569211161368633)
        ·
          refine ⟨10196943019926908371026475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13595924026569211161368633 10196943019926908371026475)
          ·
            refine ⟨15295414529890362556539713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10196943019926908371026475 15295414529890362556539713)
            ·
              refine ⟨11471560897417771917404785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15295414529890362556539713 11471560897417771917404785)
              ·
                refine ⟨8603670673063328938053589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11471560897417771917404785 8603670673063328938053589)
                ·
                  refine ⟨201648531399921771985631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8603670673063328938053589 201648531399921771985631)
                  ·
                    rfl

theorem cell23_3534382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_3534382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534382 prefixEnd_3534382 := by exact prefixLift 3534382
  have htrace : WordTrace (prefixWord ++ tailWord_3534382) baseStart_3534382 baseEnd_3534382 := by
    simpa [prefixWord, tailWord_3534382, baseEnd_3534382] using wordTrace_append hprefix tailTrace_3534382
  have hstable : (prefixWord ++ tailWord_3534382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534382).length < 2 ^ (prefixWord ++ tailWord_3534382).sum := by decide
  have hdescent : baseEnd_3534382 < baseStart_3534382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534399 : List Nat := [1, 1, 2, 2, 3, 5, 1, 3, 5]
def baseStart_3534399 : Nat := 118140960795 + 3534399 * 2 ^ 59
def prefixEnd_3534399 : Nat := 4983230072969 + 3 ^ 40 * 3534399 * 2
def baseEnd_3534399 : Nat := 201649501307824709039789

theorem tailTrace_3534399 : CollatzResearch.WordTrace tailWord_3534399 prefixEnd_3534399 201649501307824709039789 := by
  unfold tailWord_3534399
  simp only [CollatzResearch.WordTrace]
  refine ⟨128910121922483525137086251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85940081281655683424724167 128910121922483525137086251)
  ·
    refine ⟨193365182883725287705629377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128910121922483525137086251 193365182883725287705629377)
    ·
      refine ⟨145023887162793965779222033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193365182883725287705629377 145023887162793965779222033)
      ·
        refine ⟨108767915372095474334416525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145023887162793965779222033 108767915372095474334416525)
        ·
          refine ⟨40787968264535802875406197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 108767915372095474334416525 40787968264535802875406197)
          ·
            refine ⟨3823872024800231519569331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40787968264535802875406197 3823872024800231519569331)
            ·
              refine ⟨5735808037200347279353997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3823872024800231519569331 5735808037200347279353997)
              ·
                refine ⟨2150928013950130229757749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5735808037200347279353997 2150928013950130229757749)
                ·
                  refine ⟨201649501307824709039789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2150928013950130229757749 201649501307824709039789)
                  ·
                    rfl

theorem cell23_3534399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 5].length) (baseStart_3534399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534399 prefixEnd_3534399 := by exact prefixLift 3534399
  have htrace : WordTrace (prefixWord ++ tailWord_3534399) baseStart_3534399 baseEnd_3534399 := by
    simpa [prefixWord, tailWord_3534399, baseEnd_3534399] using wordTrace_append hprefix tailTrace_3534399
  have hstable : (prefixWord ++ tailWord_3534399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534399).length < 2 ^ (prefixWord ++ tailWord_3534399).sum := by decide
  have hdescent : baseEnd_3534399 < baseStart_3534399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534405 : List Nat := [1, 3, 1, 1, 1, 4, 2, 2, 1, 2, 5]
def baseStart_3534405 : Nat := 118140960795 + 3534405 * 2 ^ 59
def prefixEnd_3534405 : Nat := 4983230072969 + 3 ^ 40 * 3534405 * 2
def baseEnd_3534405 : Nat := 1814848592654349357883073

theorem tailTrace_3534405 : CollatzResearch.WordTrace tailWord_3534405 prefixEnd_3534405 1814848592654349357883073 := by
  unfold tailWord_3534405
  simp only [CollatzResearch.WordTrace]
  refine ⟨128910340760461788161804669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85940227173641192107869779 128910340760461788161804669)
  ·
    refine ⟨48341377785173170560676751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128910340760461788161804669 48341377785173170560676751)
    ·
      refine ⟨72512066677759755841015127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48341377785173170560676751 72512066677759755841015127)
      ·
        refine ⟨108768100016639633761522691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72512066677759755841015127 108768100016639633761522691)
        ·
          refine ⟨163152150024959450642284037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108768100016639633761522691 163152150024959450642284037)
          ·
            refine ⟨30591028129679896995428257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 163152150024959450642284037 30591028129679896995428257)
            ·
              refine ⟨22943271097259922746571193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30591028129679896995428257 22943271097259922746571193)
              ·
                refine ⟨17207453322944942059928395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22943271097259922746571193 17207453322944942059928395)
                ·
                  refine ⟨25811179984417413089892593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17207453322944942059928395 25811179984417413089892593)
                  ·
                    refine ⟨19358384988313059817419445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25811179984417413089892593 19358384988313059817419445)
                    ·
                      refine ⟨1814848592654349357883073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19358384988313059817419445 1814848592654349357883073)
                      ·
                        rfl

theorem cell23_3534405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_3534405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534405 prefixEnd_3534405 := by exact prefixLift 3534405
  have htrace : WordTrace (prefixWord ++ tailWord_3534405) baseStart_3534405 baseEnd_3534405 := by
    simpa [prefixWord, tailWord_3534405, baseEnd_3534405] using wordTrace_append hprefix tailTrace_3534405
  have hstable : (prefixWord ++ tailWord_3534405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534405).length < 2 ^ (prefixWord ++ tailWord_3534405).sum := by decide
  have hdescent : baseEnd_3534405 < baseStart_3534405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534412 : List Nat := [2, 2, 1, 3, 1, 4, 1, 2, 2, 5]
def baseStart_3534412 : Nat := 118140960795 + 3534412 * 2 ^ 59
def prefixEnd_3534412 : Nat := 4983230072969 + 3 ^ 40 * 3534412 * 2
def baseEnd_3534412 : Nat := 604950729006310276831847

theorem tailTrace_3534412 : CollatzResearch.WordTrace tailWord_3534412 prefixEnd_3534412 604950729006310276831847 := by
  unfold tailWord_3534412
  simp only [CollatzResearch.WordTrace]
  refine ⟨64455298035718214178654745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85940397380957618904872993 64455298035718214178654745)
  ·
    refine ⟨48341473526788660633991059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64455298035718214178654745 48341473526788660633991059)
    ·
      refine ⟨72512210290182990950986589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48341473526788660633991059 72512210290182990950986589)
      ·
        refine ⟨27192078858818621606619971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72512210290182990950986589 27192078858818621606619971)
        ·
          refine ⟨40788118288227932409929957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27192078858818621606619971 40788118288227932409929957)
          ·
            refine ⟨7647772179042737326861867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40788118288227932409929957 7647772179042737326861867)
            ·
              refine ⟨11471658268564105990292801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7647772179042737326861867 11471658268564105990292801)
              ·
                refine ⟨8603743701423079492719601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11471658268564105990292801 8603743701423079492719601)
                ·
                  refine ⟨6452807776067309619539701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8603743701423079492719601 6452807776067309619539701)
                  ·
                    refine ⟨604950729006310276831847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6452807776067309619539701 604950729006310276831847)
                    ·
                      rfl

theorem cell23_3534412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_3534412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534412 prefixEnd_3534412 := by exact prefixLift 3534412
  have htrace : WordTrace (prefixWord ++ tailWord_3534412) baseStart_3534412 baseEnd_3534412 := by
    simpa [prefixWord, tailWord_3534412, baseEnd_3534412] using wordTrace_append hprefix tailTrace_3534412
  have hstable : (prefixWord ++ tailWord_3534412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534412).length < 2 ^ (prefixWord ++ tailWord_3534412).sum := by decide
  have hdescent : baseEnd_3534412 < baseStart_3534412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534432 : List Nat := [2, 1, 1, 3, 2, 1, 1, 3, 1, 6, 2]
def baseStart_3534432 : Nat := 118140960795 + 3534432 * 2 ^ 59
def prefixEnd_3534432 : Nat := 4983230072969 + 3 ^ 40 * 3534432 * 2
def baseEnd_3534432 : Nat := 1814862456632020752245449

theorem tailTrace_3534432 : CollatzResearch.WordTrace tailWord_3534432 prefixEnd_3534432 1814862456632020752245449 := by
  unfold tailWord_3534432
  simp only [CollatzResearch.WordTrace]
  refine ⟨64455662765681985886518775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85940883687575981182025033 64455662765681985886518775)
  ·
    refine ⟨96683494148522978829778163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64455662765681985886518775 96683494148522978829778163)
    ·
      refine ⟨145025241222784468244667245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96683494148522978829778163 145025241222784468244667245)
      ·
        refine ⟨54384465458544175591750217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 145025241222784468244667245 54384465458544175591750217)
        ·
          refine ⟨40788349093908131693812663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54384465458544175591750217 40788349093908131693812663)
          ·
            refine ⟨61182523640862197540718995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40788349093908131693812663 61182523640862197540718995)
            ·
              refine ⟨91773785461293296311078493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61182523640862197540718995 91773785461293296311078493)
              ·
                refine ⟨34415169547984986116654435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91773785461293296311078493 34415169547984986116654435)
                ·
                  refine ⟨51622754321977479174981653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34415169547984986116654435 51622754321977479174981653)
                  ·
                    refine ⟨2419816608842694336327265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51622754321977479174981653 2419816608842694336327265)
                    ·
                      refine ⟨1814862456632020752245449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2419816608842694336327265 1814862456632020752245449)
                      ·
                        rfl

theorem cell23_3534432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_3534432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534432 prefixEnd_3534432 := by exact prefixLift 3534432
  have htrace : WordTrace (prefixWord ++ tailWord_3534432) baseStart_3534432 baseEnd_3534432 := by
    simpa [prefixWord, tailWord_3534432, baseEnd_3534432] using wordTrace_append hprefix tailTrace_3534432
  have hstable : (prefixWord ++ tailWord_3534432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534432).length < 2 ^ (prefixWord ++ tailWord_3534432).sum := by decide
  have hdescent : baseEnd_3534432 < baseStart_3534432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534459 : List Nat := [1, 1, 1, 1, 1, 4, 4, 5, 1, 4]
def baseStart_3534459 : Nat := 118140960795 + 3534459 * 2 ^ 59
def prefixEnd_3534459 : Nat := 4983230072969 + 3 ^ 40 * 3534459 * 2
def baseEnd_3534459 : Nat := 604958773536564048869275

theorem tailTrace_3534459 : CollatzResearch.WordTrace tailWord_3534459 prefixEnd_3534459 604958773536564048869275 := by
  unfold tailWord_3534459
  simp only [CollatzResearch.WordTrace]
  refine ⟨128912310302266155384270431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85941540201510770256180287 128912310302266155384270431)
  ·
    refine ⟨193368465453399233076405647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128912310302266155384270431 193368465453399233076405647)
    ·
      refine ⟨290052698180098849614608471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193368465453399233076405647 290052698180098849614608471)
      ·
        refine ⟨435079047270148274421912707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290052698180098849614608471 435079047270148274421912707)
        ·
          refine ⟨652618570905222411632869061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435079047270148274421912707 652618570905222411632869061)
          ·
            refine ⟨122365982044729202181162949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 652618570905222411632869061 122365982044729202181162949)
            ·
              refine ⟨22943621633386725408968053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122365982044729202181162949 22943621633386725408968053)
              ·
                refine ⟨2150964528130005507090755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22943621633386725408968053 2150964528130005507090755)
                ·
                  refine ⟨3226446792195008260636133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150964528130005507090755 3226446792195008260636133)
                  ·
                    refine ⟨604958773536564048869275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3226446792195008260636133 604958773536564048869275)
                    ·
                      rfl

theorem cell23_3534459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 1, 4].length) (baseStart_3534459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534459 prefixEnd_3534459 := by exact prefixLift 3534459
  have htrace : WordTrace (prefixWord ++ tailWord_3534459) baseStart_3534459 baseEnd_3534459 := by
    simpa [prefixWord, tailWord_3534459, baseEnd_3534459] using wordTrace_append hprefix tailTrace_3534459
  have hstable : (prefixWord ++ tailWord_3534459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534459).length < 2 ^ (prefixWord ++ tailWord_3534459).sum := by decide
  have hdescent : baseEnd_3534459 < baseStart_3534459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534475 : List Nat := [1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 6]
def baseStart_3534475 : Nat := 118140960795 + 3534475 * 2 ^ 59
def prefixEnd_3534475 : Nat := 4983230072969 + 3 ^ 40 * 3534475 * 2
def baseEnd_3534475 : Nat := 1814884536300164084007751

theorem tailTrace_3534475 : CollatzResearch.WordTrace tailWord_3534475 prefixEnd_3534475 1814884536300164084007751 := by
  unfold tailWord_3534475
  simp only [CollatzResearch.WordTrace]
  refine ⟨128912893870208190116852879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85941929246805460077901919 128912893870208190116852879)
  ·
    refine ⟨193369340805312285175279319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128912893870208190116852879 193369340805312285175279319)
    ·
      refine ⟨290054011207968427762918979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193369340805312285175279319 290054011207968427762918979)
      ·
        refine ⟨435081016811952641644378469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290054011207968427762918979 435081016811952641644378469)
        ·
          refine ⟨81577690652241120308320963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 435081016811952641644378469 81577690652241120308320963)
          ·
            refine ⟨122366535978361680462481445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81577690652241120308320963 122366535978361680462481445)
            ·
              refine ⟨22943725495942815086715271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 122366535978361680462481445 22943725495942815086715271)
              ·
                refine ⟨34415588243914222630072907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22943725495942815086715271 34415588243914222630072907)
                ·
                  refine ⟨51623382365871333945109361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34415588243914222630072907 51623382365871333945109361)
                  ·
                    refine ⟨38717536774403500458832021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 51623382365871333945109361 38717536774403500458832021)
                    ·
                      refine ⟨1814884536300164084007751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38717536774403500458832021 1814884536300164084007751)
                      ·
                        rfl

theorem cell23_3534475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 6].length) (baseStart_3534475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534475 prefixEnd_3534475 := by exact prefixLift 3534475
  have htrace : WordTrace (prefixWord ++ tailWord_3534475) baseStart_3534475 baseEnd_3534475 := by
    simpa [prefixWord, tailWord_3534475, baseEnd_3534475] using wordTrace_append hprefix tailTrace_3534475
  have hstable : (prefixWord ++ tailWord_3534475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534475).length < 2 ^ (prefixWord ++ tailWord_3534475).sum := by decide
  have hdescent : baseEnd_3534475 < baseStart_3534475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534499 : List Nat := [1, 1, 1, 4, 1, 1, 5, 2, 3, 1, 3]
def baseStart_3534499 : Nat := 118140960795 + 3534499 * 2 ^ 59
def prefixEnd_3534499 : Nat := 4983230072969 + 3 ^ 40 * 3534499 * 2
def baseEnd_3534499 : Nat := 1814896859835871990107641

theorem tailTrace_3534499 : CollatzResearch.WordTrace tailWord_3534499 prefixEnd_3534499 1814896859835871990107641 := by
  unfold tailWord_3534499
  simp only [CollatzResearch.WordTrace]
  refine ⟨128913769222121242215726551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85942512814747494810484367 128913769222121242215726551)
  ·
    refine ⟨193370653833181863323589827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128913769222121242215726551 193370653833181863323589827)
    ·
      refine ⟨290055980749772794985384741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193370653833181863323589827 290055980749772794985384741)
      ·
        refine ⟨54385496390582399059759639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 290055980749772794985384741 54385496390582399059759639)
        ·
          refine ⟨81578244585873598589639459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54385496390582399059759639 81578244585873598589639459)
          ·
            refine ⟨122367366878810397884459189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81578244585873598589639459 122367366878810397884459189)
            ·
              refine ⟨11471940644888474801668049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122367366878810397884459189 11471940644888474801668049)
              ·
                refine ⟨8603955483666356101251037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11471940644888474801668049 8603955483666356101251037)
                ·
                  refine ⟨3226483306374883537969139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8603955483666356101251037 3226483306374883537969139)
                  ·
                    refine ⟨4839724959562325306953709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3226483306374883537969139 4839724959562325306953709)
                    ·
                      refine ⟨1814896859835871990107641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4839724959562325306953709 1814896859835871990107641)
                      ·
                        rfl

theorem cell23_3534499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_3534499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534499 prefixEnd_3534499 := by exact prefixLift 3534499
  have htrace : WordTrace (prefixWord ++ tailWord_3534499) baseStart_3534499 baseEnd_3534499 := by
    simpa [prefixWord, tailWord_3534499, baseEnd_3534499] using wordTrace_append hprefix tailTrace_3534499
  have hstable : (prefixWord ++ tailWord_3534499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534499).length < 2 ^ (prefixWord ++ tailWord_3534499).sum := by decide
  have hdescent : baseEnd_3534499 < baseStart_3534499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534510 : List Nat := [4, 1, 4, 1, 2, 1, 2, 3, 1, 4]
def baseStart_3534510 : Nat := 118140960795 + 3534510 * 2 ^ 59
def prefixEnd_3534510 : Nat := 4983230072969 + 3 ^ 40 * 3534510 * 2
def baseEnd_3534510 : Nat := 604967502707690482356697

theorem tailTrace_3534510 : CollatzResearch.WordTrace tailWord_3534510 prefixEnd_3534510 604967502707690482356697 := by
  unfold tailWord_3534510
  simp only [CollatzResearch.WordTrace]
  refine ⟨16114271303135173886797123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85942780283387594062917989 16114271303135173886797123)
  ·
    refine ⟨24171406954702760830195685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16114271303135173886797123 24171406954702760830195685)
    ·
      refine ⟨4532138804006767655661691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24171406954702760830195685 4532138804006767655661691)
      ·
        refine ⟨6798208206010151483492537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4532138804006767655661691 6798208206010151483492537)
        ·
          refine ⟨5098656154507613612619403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6798208206010151483492537 5098656154507613612619403)
          ·
            refine ⟨7647984231761420418929105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5098656154507613612619403 7647984231761420418929105)
            ·
              refine ⟨5735988173821065314196829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7647984231761420418929105 5735988173821065314196829)
              ·
                refine ⟨2150995565182899492823811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5735988173821065314196829 2150995565182899492823811)
                ·
                  refine ⟨3226493347774349239235717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2150995565182899492823811 3226493347774349239235717)
                  ·
                    refine ⟨604967502707690482356697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3226493347774349239235717 604967502707690482356697)
                    ·
                      rfl

theorem cell23_3534510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_3534510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534510 prefixEnd_3534510 := by exact prefixLift 3534510
  have htrace : WordTrace (prefixWord ++ tailWord_3534510) baseStart_3534510 baseEnd_3534510 := by
    simpa [prefixWord, tailWord_3534510, baseEnd_3534510] using wordTrace_append hprefix tailTrace_3534510
  have hstable : (prefixWord ++ tailWord_3534510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534510).length < 2 ^ (prefixWord ++ tailWord_3534510).sum := by decide
  have hdescent : baseEnd_3534510 < baseStart_3534510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534519 : List Nat := [1, 1, 3, 1, 5, 2, 1, 3, 1, 5]
def baseStart_3534519 : Nat := 118140960795 + 3534519 * 2 ^ 59
def prefixEnd_3534519 : Nat := 4983230072969 + 3 ^ 40 * 3534519 * 2
def baseEnd_3534519 : Nat := 604969043149653970619183

theorem tailTrace_3534519 : CollatzResearch.WordTrace tailWord_3534519 prefixEnd_3534519 604969043149653970619183 := by
  unfold tailWord_3534519
  simp only [CollatzResearch.WordTrace]
  refine ⟨128914498682048785631454611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85942999121365857087636407 128914498682048785631454611)
  ·
    refine ⟨193371748023073178447181917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128914498682048785631454611 193371748023073178447181917)
    ·
      refine ⟨72514405508652441917693219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193371748023073178447181917 72514405508652441917693219)
      ·
        refine ⟨108771608262978662876539829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72514405508652441917693219 108771608262978662876539829)
        ·
          refine ⟨10197338274654249644675609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108771608262978662876539829 10197338274654249644675609)
          ·
            refine ⟨7648003705990687233506707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10197338274654249644675609 7648003705990687233506707)
            ·
              refine ⟨11472005558986030850260061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7648003705990687233506707 11472005558986030850260061)
              ·
                refine ⟨4302002084619761568847523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11472005558986030850260061 4302002084619761568847523)
                ·
                  refine ⟨6453003126929642353271285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4302002084619761568847523 6453003126929642353271285)
                  ·
                    refine ⟨604969043149653970619183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6453003126929642353271285 604969043149653970619183)
                    ·
                      rfl

theorem cell23_3534519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_3534519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534519 prefixEnd_3534519 := by exact prefixLift 3534519
  have htrace : WordTrace (prefixWord ++ tailWord_3534519) baseStart_3534519 baseEnd_3534519 := by
    simpa [prefixWord, tailWord_3534519, baseEnd_3534519] using wordTrace_append hprefix tailTrace_3534519
  have hstable : (prefixWord ++ tailWord_3534519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534519).length < 2 ^ (prefixWord ++ tailWord_3534519).sum := by decide
  have hdescent : baseEnd_3534519 < baseStart_3534519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534552 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 1, 1, 6]
def baseStart_3534552 : Nat := 118140960795 + 3534552 * 2 ^ 59
def prefixEnd_3534552 : Nat := 4983230072969 + 3 ^ 40 * 3534552 * 2
def baseEnd_3534552 : Nat := 1814924074310560282744897

theorem tailTrace_3534552 : CollatzResearch.WordTrace tailWord_3534552 prefixEnd_3534552 1814924074310560282744897 := by
  unfold tailWord_3534552
  simp only [CollatzResearch.WordTrace]
  refine ⟨64457851145464616133702955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85943801527286154844937273 64457851145464616133702955)
  ·
    refine ⟨96686776718196924200554433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64457851145464616133702955 96686776718196924200554433)
    ·
      refine ⟨72515082538647693150415825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96686776718196924200554433 72515082538647693150415825)
      ·
        refine ⟨54386311903985769862811869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72515082538647693150415825 54386311903985769862811869)
        ·
          refine ⟨20394866963994663698554451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54386311903985769862811869 20394866963994663698554451)
          ·
            refine ⟨30592300445991995547831677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20394866963994663698554451 30592300445991995547831677)
            ·
              refine ⟨11472112667246998330436879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30592300445991995547831677 11472112667246998330436879)
              ·
                refine ⟨17208169000870497495655319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11472112667246998330436879 17208169000870497495655319)
                ·
                  refine ⟨25812253501305746243482979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17208169000870497495655319 25812253501305746243482979)
                  ·
                    refine ⟨38718380251958619365224469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25812253501305746243482979 38718380251958619365224469)
                    ·
                      refine ⟨1814924074310560282744897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 38718380251958619365224469 1814924074310560282744897)
                      ·
                        rfl

theorem cell23_3534552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_3534552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534552 prefixEnd_3534552 := by exact prefixLift 3534552
  have htrace : WordTrace (prefixWord ++ tailWord_3534552) baseStart_3534552 baseEnd_3534552 := by
    simpa [prefixWord, tailWord_3534552, baseEnd_3534552] using wordTrace_append hprefix tailTrace_3534552
  have hstable : (prefixWord ++ tailWord_3534552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534552).length < 2 ^ (prefixWord ++ tailWord_3534552).sum := by decide
  have hdescent : baseEnd_3534552 < baseStart_3534552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534567 : List Nat := [1, 1, 5, 4, 1, 2, 1, 3, 1, 1, 3]
def baseStart_3534567 : Nat := 118140960795 + 3534567 * 2 ^ 59
def prefixEnd_3534567 : Nat := 4983230072969 + 3 ^ 40 * 3534567 * 2
def baseEnd_3534567 : Nat := 1814931776520377724057329

theorem tailTrace_3534567 : CollatzResearch.WordTrace tailWord_3534567 prefixEnd_3534567 1814931776520377724057329 := by
  unfold tailWord_3534567
  simp only [CollatzResearch.WordTrace]
  refine ⟨128916249385874889829201955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85944166257249926552801303 128916249385874889829201955)
  ·
    refine ⟨193374374078812334743802933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128916249385874889829201955 193374374078812334743802933)
    ·
      refine ⟨18128847569888656382231525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 193374374078812334743802933 18128847569888656382231525)
      ·
        refine ⟨3399158919354123071668411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18128847569888656382231525 3399158919354123071668411)
        ·
          refine ⟨5098738379031184607502617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3399158919354123071668411 5098738379031184607502617)
          ·
            refine ⟨3824053784273388455626963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5098738379031184607502617 3824053784273388455626963)
            ·
              refine ⟨5736080676410082683440445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824053784273388455626963 5736080676410082683440445)
              ·
                refine ⟨2151030253653781006290167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5736080676410082683440445 2151030253653781006290167)
                ·
                  refine ⟨3226545380480671509435251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151030253653781006290167 3226545380480671509435251)
                  ·
                    refine ⟨4839818070721007264152877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3226545380480671509435251 4839818070721007264152877)
                    ·
                      refine ⟨1814931776520377724057329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4839818070721007264152877 1814931776520377724057329)
                      ·
                        rfl

theorem cell23_3534567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_3534567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534567 prefixEnd_3534567 := by exact prefixLift 3534567
  have htrace : WordTrace (prefixWord ++ tailWord_3534567) baseStart_3534567 baseEnd_3534567 := by
    simpa [prefixWord, tailWord_3534567, baseEnd_3534567] using wordTrace_append hprefix tailTrace_3534567
  have hstable : (prefixWord ++ tailWord_3534567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534567).length < 2 ^ (prefixWord ++ tailWord_3534567).sum := by decide
  have hdescent : baseEnd_3534567 < baseStart_3534567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534610 : List Nat := [3, 2, 4, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_3534610 : Nat := 118140960795 + 3534610 * 2 ^ 59
def prefixEnd_3534610 : Nat := 4983230072969 + 3 ^ 40 * 3534610 * 2
def baseEnd_3534610 : Nat := 1814953856188521055819631

theorem tailTrace_3534610 : CollatzResearch.WordTrace tailWord_3534610 prefixEnd_3534610 1814953856188521055819631 := by
  unfold tailWord_3534610
  simp only [CollatzResearch.WordTrace]
  refine ⟨32229454431179777043254321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85945211816479405448678189 32229454431179777043254321)
  ·
    refine ⟨24172090823384832782440741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32229454431179777043254321 24172090823384832782440741)
    ·
      refine ⟨4532267029384656146707639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24172090823384832782440741 4532267029384656146707639)
      ·
        refine ⟨6798400544076984220061459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4532267029384656146707639 6798400544076984220061459)
        ·
          refine ⟨10197600816115476330092189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6798400544076984220061459 10197600816115476330092189)
          ·
            refine ⟨3824100306043303623784571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10197600816115476330092189 3824100306043303623784571)
            ·
              refine ⟨5736150459064955435676857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824100306043303623784571 5736150459064955435676857)
              ·
                refine ⟨4302112844298716576757643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5736150459064955435676857 4302112844298716576757643)
                ·
                  refine ⟨6453169266448074865136465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4302112844298716576757643 6453169266448074865136465)
                  ·
                    refine ⟨4839876949836056148852349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6453169266448074865136465 4839876949836056148852349)
                    ·
                      refine ⟨1814953856188521055819631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4839876949836056148852349 1814953856188521055819631)
                      ·
                        rfl

theorem cell23_3534610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_3534610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534610 prefixEnd_3534610 := by exact prefixLift 3534610
  have htrace : WordTrace (prefixWord ++ tailWord_3534610) baseStart_3534610 baseEnd_3534610 := by
    simpa [prefixWord, tailWord_3534610, baseEnd_3534610] using wordTrace_append hprefix tailTrace_3534610
  have hstable : (prefixWord ++ tailWord_3534610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534610).length < 2 ^ (prefixWord ++ tailWord_3534610).sum := by decide
  have hdescent : baseEnd_3534610 < baseStart_3534610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534646 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_3534646 : Nat := 118140960795 + 3534646 * 2 ^ 59
def prefixEnd_3534646 : Nat := 4983230072969 + 3 ^ 40 * 3534646 * 2
def baseEnd_3534646 : Nat := 1814972341492082914969465

theorem tailTrace_3534646 : CollatzResearch.WordTrace tailWord_3534646 prefixEnd_3534646 1814972341492082914969465 := by
  unfold tailWord_3534646
  simp only [CollatzResearch.WordTrace]
  refine ⟨8057445672036792895082987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 85946087168392457547551861 8057445672036792895082987)
  ·
    refine ⟨12086168508055189342624481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8057445672036792895082987 12086168508055189342624481)
    ·
      refine ⟨9064626381041392006968361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12086168508055189342624481 9064626381041392006968361)
      ·
        refine ⟨6798469785781044005226271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9064626381041392006968361 6798469785781044005226271)
        ·
          refine ⟨10197704678671566007839407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6798469785781044005226271 10197704678671566007839407)
          ·
            refine ⟨15296557018007349011759111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10197704678671566007839407 15296557018007349011759111)
            ·
              refine ⟨22944835527011023517638667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15296557018007349011759111 22944835527011023517638667)
              ·
                refine ⟨34417253290516535276458001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22944835527011023517638667 34417253290516535276458001)
                ·
                  refine ⟨25812939967887401457343501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34417253290516535276458001 25812939967887401457343501)
                  ·
                    refine ⟨9679852487957775546503813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25812939967887401457343501 9679852487957775546503813)
                    ·
                      refine ⟨1814972341492082914969465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9679852487957775546503813 1814972341492082914969465)
                      ·
                        rfl

theorem cell23_3534646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_3534646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534646 prefixEnd_3534646 := by exact prefixLift 3534646
  have htrace : WordTrace (prefixWord ++ tailWord_3534646) baseStart_3534646 baseEnd_3534646 := by
    simpa [prefixWord, tailWord_3534646, baseEnd_3534646] using wordTrace_append hprefix tailTrace_3534646
  have hstable : (prefixWord ++ tailWord_3534646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534646).length < 2 ^ (prefixWord ++ tailWord_3534646).sum := by decide
  have hdescent : baseEnd_3534646 < baseStart_3534646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534659 : List Nat := [1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 4]
def baseStart_3534659 : Nat := 118140960795 + 3534659 * 2 ^ 59
def prefixEnd_3534659 : Nat := 4983230072969 + 3 ^ 40 * 3534659 * 2
def baseEnd_3534659 : Nat := 1814979016740591364106905

theorem tailTrace_3534659 : CollatzResearch.WordTrace tailWord_3534659 prefixEnd_3534659 1814979016740591364106905 := by
  unfold tailWord_3534659
  simp only [CollatzResearch.WordTrace]
  refine ⟨128919604901541589541551031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85946403267694393027700687 128919604901541589541551031)
  ·
    refine ⟨193379407352312384312326547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128919604901541589541551031 193379407352312384312326547)
    ·
      refine ⟨290069111028468576468489821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193379407352312384312326547 290069111028468576468489821)
      ·
        refine ⟨108775916635675716175683683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 290069111028468576468489821 108775916635675716175683683)
        ·
          refine ⟨163163874953513574263525525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108775916635675716175683683 163163874953513574263525525)
          ·
            refine ⟨7648306638445948793602759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 163163874953513574263525525 7648306638445948793602759)
            ·
              refine ⟨11472459957668923190404139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7648306638445948793602759 11472459957668923190404139)
              ·
                refine ⟨17208689936503384785606209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11472459957668923190404139 17208689936503384785606209)
                ·
                  refine ⟨12906517452377538589204657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17208689936503384785606209 12906517452377538589204657)
                  ·
                    refine ⟨9679888089283153941903493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12906517452377538589204657 9679888089283153941903493)
                    ·
                      refine ⟨1814979016740591364106905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9679888089283153941903493 1814979016740591364106905)
                      ·
                        rfl

theorem cell23_3534659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_3534659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534659 prefixEnd_3534659 := by exact prefixLift 3534659
  have htrace : WordTrace (prefixWord ++ tailWord_3534659) baseStart_3534659 baseEnd_3534659 := by
    simpa [prefixWord, tailWord_3534659, baseEnd_3534659] using wordTrace_append hprefix tailTrace_3534659
  have hstable : (prefixWord ++ tailWord_3534659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534659).length < 2 ^ (prefixWord ++ tailWord_3534659).sum := by decide
  have hdescent : baseEnd_3534659 < baseStart_3534659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534663 : List Nat := [1, 1, 4, 1, 2, 1, 4, 3, 2, 2, 2]
def baseStart_3534663 : Nat := 118140960795 + 3534663 * 2 ^ 59
def prefixEnd_3534663 : Nat := 4983230072969 + 3 ^ 40 * 3534663 * 2
def baseEnd_3534663 : Nat := 1814981070663209348456887

theorem tailTrace_3534663 : CollatzResearch.WordTrace tailWord_3534663 prefixEnd_3534663 1814981070663209348456887 := by
  unfold tailWord_3534663
  simp only [CollatzResearch.WordTrace]
  refine ⟨128919750793527098224696643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85946500529018065483131095 128919750793527098224696643)
  ·
    refine ⟨193379626190290647337044965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128919750793527098224696643 193379626190290647337044965)
    ·
      refine ⟨36258679910679496375695931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 193379626190290647337044965 36258679910679496375695931)
      ·
        refine ⟨54388019866019244563543897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36258679910679496375695931 54388019866019244563543897)
        ·
          refine ⟨40791014899514433422657923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54388019866019244563543897 40791014899514433422657923)
          ·
            refine ⟨61186522349271650133986885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40791014899514433422657923 61186522349271650133986885)
            ·
              refine ⟨11472472940488434400122541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61186522349271650133986885 11472472940488434400122541)
              ·
                refine ⟨4302177352683162900045953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11472472940488434400122541 4302177352683162900045953)
                ·
                  refine ⟨3226633014512372175034465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4302177352683162900045953 3226633014512372175034465)
                  ·
                    refine ⟨2419974760884279131275849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3226633014512372175034465 2419974760884279131275849)
                    ·
                      refine ⟨1814981070663209348456887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2419974760884279131275849 1814981070663209348456887)
                      ·
                        rfl

theorem cell23_3534663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_3534663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534663 prefixEnd_3534663 := by exact prefixLift 3534663
  have htrace : WordTrace (prefixWord ++ tailWord_3534663) baseStart_3534663 baseEnd_3534663 := by
    simpa [prefixWord, tailWord_3534663, baseEnd_3534663] using wordTrace_append hprefix tailTrace_3534663
  have hstable : (prefixWord ++ tailWord_3534663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534663).length < 2 ^ (prefixWord ++ tailWord_3534663).sum := by decide
  have hdescent : baseEnd_3534663 < baseStart_3534663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534684 : List Nat := [2, 2, 4, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_3534684 : Nat := 118140960795 + 3534684 * 2 ^ 59
def prefixEnd_3534684 : Nat := 4983230072969 + 3 ^ 40 * 3534684 * 2
def baseEnd_3534684 : Nat := 1814991853756953766294291

theorem tailTrace_3534684 : CollatzResearch.WordTrace tailWord_3534684 prefixEnd_3534684 1814991853756953766294291 := by
  unfold tailWord_3534684
  simp only [CollatzResearch.WordTrace]
  refine ⟨64460258363225509405605553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85947011150967345874140737 64460258363225509405605553)
  ·
    refine ⟨48345193772419132054204165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 64460258363225509405605553 48345193772419132054204165)
    ·
      refine ⟨9064723832328587260163281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48345193772419132054204165 9064723832328587260163281)
      ·
        refine ⟨6798542874246440445122461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9064723832328587260163281 6798542874246440445122461)
        ·
          refine ⟨2549453577842415166920923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6798542874246440445122461 2549453577842415166920923)
          ·
            refine ⟨3824180366763622750381385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549453577842415166920923 3824180366763622750381385)
            ·
              refine ⟨2868135275072717062786039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3824180366763622750381385 2868135275072717062786039)
              ·
                refine ⟨4302202912609075594179059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2868135275072717062786039 4302202912609075594179059)
                ·
                  refine ⟨6453304368913613391268589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4302202912609075594179059 6453304368913613391268589)
                  ·
                    refine ⟨2419989138342605021725721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6453304368913613391268589 2419989138342605021725721)
                    ·
                      refine ⟨1814991853756953766294291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2419989138342605021725721 1814991853756953766294291)
                      ·
                        rfl

theorem cell23_3534684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_3534684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534684 prefixEnd_3534684 := by exact prefixLift 3534684
  have htrace : WordTrace (prefixWord ++ tailWord_3534684) baseStart_3534684 baseEnd_3534684 := by
    simpa [prefixWord, tailWord_3534684, baseEnd_3534684] using wordTrace_append hprefix tailTrace_3534684
  have hstable : (prefixWord ++ tailWord_3534684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534684).length < 2 ^ (prefixWord ++ tailWord_3534684).sum := by decide
  have hdescent : baseEnd_3534684 < baseStart_3534684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534709 : List Nat := [1, 3, 4, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_3534709 : Nat := 118140960795 + 3534709 * 2 ^ 59
def prefixEnd_3534709 : Nat := 4983230072969 + 3 ^ 40 * 3534709 * 2
def baseEnd_3534709 : Nat := 1815004690773316168481675

theorem tailTrace_3534709 : CollatzResearch.WordTrace tailWord_3534709 prefixEnd_3534709 1815004690773316168481675 := by
  unfold tailWord_3534709
  simp only [CollatzResearch.WordTrace]
  refine ⟨128921428551360448080871181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85947619034240298720580787 128921428551360448080871181)
  ·
    refine ⟨48345535706760168030326693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 128921428551360448080871181 48345535706760168030326693)
    ·
      refine ⟨9064787945017531505686255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48345535706760168030326693 9064787945017531505686255)
      ·
        refine ⟨13597181917526297258529383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9064787945017531505686255 13597181917526297258529383)
        ·
          refine ⟨20395772876289445887794075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13597181917526297258529383 20395772876289445887794075)
          ·
            refine ⟨30593659314434168831691113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20395772876289445887794075 30593659314434168831691113)
            ·
              refine ⟨22945244485825626623768335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30593659314434168831691113 22945244485825626623768335)
              ·
                refine ⟨34417866728738439935652503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22945244485825626623768335 34417866728738439935652503)
                ·
                  refine ⟨51626800093107659903478755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34417866728738439935652503 51626800093107659903478755)
                  ·
                    refine ⟨77440200139661489855218133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 51626800093107659903478755 77440200139661489855218133)
                    ·
                      refine ⟨1815004690773316168481675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 77440200139661489855218133 1815004690773316168481675)
                      ·
                        rfl

theorem cell23_3534709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_3534709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534709 prefixEnd_3534709 := by exact prefixLift 3534709
  have htrace : WordTrace (prefixWord ++ tailWord_3534709) baseStart_3534709 baseEnd_3534709 := by
    simpa [prefixWord, tailWord_3534709, baseEnd_3534709] using wordTrace_append hprefix tailTrace_3534709
  have hstable : (prefixWord ++ tailWord_3534709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534709).length < 2 ^ (prefixWord ++ tailWord_3534709).sum := by decide
  have hdescent : baseEnd_3534709 < baseStart_3534709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534750 : List Nat := [4, 3, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_3534750 : Nat := 118140960795 + 3534750 * 2 ^ 59
def prefixEnd_3534750 : Nat := 4983230072969 + 3 ^ 40 * 3534750 * 2
def baseEnd_3534750 : Nat := 605008581160050169356329

theorem tailTrace_3534750 : CollatzResearch.WordTrace tailWord_3534750 prefixEnd_3534750 605008581160050169356329 := by
  unfold tailWord_3534750
  simp only [CollatzResearch.WordTrace]
  refine ⟨16115365493026489010389213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 85948615962807941388742469 16115365493026489010389213)
  ·
    refine ⟨6043262059884933378895955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16115365493026489010389213 6043262059884933378895955)
    ·
      refine ⟨9064893089827400068343933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6043262059884933378895955 9064893089827400068343933)
      ·
        refine ⟨3399334908685275025628975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9064893089827400068343933 3399334908685275025628975)
        ·
          refine ⟨5099002363027912538443463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3399334908685275025628975 5099002363027912538443463)
          ·
            refine ⟨7648503544541868807665195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5099002363027912538443463 7648503544541868807665195)
            ·
              refine ⟨11472755316812803211497793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7648503544541868807665195 11472755316812803211497793)
              ·
                refine ⟨8604566487609602408623345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11472755316812803211497793 8604566487609602408623345)
                ·
                  refine ⟨6453424865707201806467509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8604566487609602408623345 6453424865707201806467509)
                  ·
                    refine ⟨605008581160050169356329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6453424865707201806467509 605008581160050169356329)
                    ·
                      rfl

theorem cell23_3534750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_3534750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534750 prefixEnd_3534750 := by exact prefixLift 3534750
  have htrace : WordTrace (prefixWord ++ tailWord_3534750) baseStart_3534750 baseEnd_3534750 := by
    simpa [prefixWord, tailWord_3534750, baseEnd_3534750] using wordTrace_append hprefix tailTrace_3534750
  have hstable : (prefixWord ++ tailWord_3534750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534750).length < 2 ^ (prefixWord ++ tailWord_3534750).sum := by decide
  have hdescent : baseEnd_3534750 < baseStart_3534750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534753 : List Nat := [1, 2, 3, 4, 2, 1, 1, 2, 2, 1, 4]
def baseStart_3534753 : Nat := 118140960795 + 3534753 * 2 ^ 59
def prefixEnd_3534753 : Nat := 4983230072969 + 3 ^ 40 * 3534753 * 2
def baseEnd_3534753 : Nat := 1815027283922113996331473

theorem tailTrace_3534753 : CollatzResearch.WordTrace tailWord_3534753 prefixEnd_3534753 1815027283922113996331473 := by
  unfold tailWord_3534753
  simp only [CollatzResearch.WordTrace]
  refine ⟨128923033363201043595472913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85948688908800695730315275 128923033363201043595472913)
  ·
    refine ⟨96692275022400782696604685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128923033363201043595472913 96692275022400782696604685)
    ·
      refine ⟨36259603133400293511226757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96692275022400782696604685 36259603133400293511226757)
      ·
        refine ⟨6798675587512555033355017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36259603133400293511226757 6798675587512555033355017)
        ·
          refine ⟨5099006690634416275016263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6798675587512555033355017 5099006690634416275016263)
          ·
            refine ⟨7648510035951624412524395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5099006690634416275016263 7648510035951624412524395)
            ·
              refine ⟨11472765053927436618786593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7648510035951624412524395 11472765053927436618786593)
              ·
                refine ⟨8604573790445577464089945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11472765053927436618786593 8604573790445577464089945)
                ·
                  refine ⟨6453430342834183098067459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8604573790445577464089945 6453430342834183098067459)
                  ·
                    refine ⟨9680145514251274647101189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6453430342834183098067459 9680145514251274647101189)
                    ·
                      refine ⟨1815027283922113996331473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9680145514251274647101189 1815027283922113996331473)
                      ·
                        rfl

theorem cell23_3534753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_3534753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534753 prefixEnd_3534753 := by exact prefixLift 3534753
  have htrace : WordTrace (prefixWord ++ tailWord_3534753) baseStart_3534753 baseEnd_3534753 := by
    simpa [prefixWord, tailWord_3534753, baseEnd_3534753] using wordTrace_append hprefix tailTrace_3534753
  have hstable : (prefixWord ++ tailWord_3534753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534753).length < 2 ^ (prefixWord ++ tailWord_3534753).sum := by decide
  have hdescent : baseEnd_3534753 < baseStart_3534753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534756 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 4, 2, 3]
def baseStart_3534756 : Nat := 118140960795 + 3534756 * 2 ^ 59
def prefixEnd_3534756 : Nat := 4983230072969 + 3 ^ 40 * 3534756 * 2
def baseEnd_3534756 : Nat := 1815028824364077484593959

theorem tailTrace_3534756 : CollatzResearch.WordTrace tailWord_3534756 prefixEnd_3534756 1815028824364077484593959 := by
  unfold tailWord_3534756
  simp only [CollatzResearch.WordTrace]
  refine ⟨64461571391095087553916061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85948761854793450071888081 64461571391095087553916061)
  ·
    refine ⟨24173089271660657832718523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64461571391095087553916061 24173089271660657832718523)
    ·
      refine ⟨36259633907490986749077785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24173089271660657832718523 36259633907490986749077785)
      ·
        refine ⟨27194725430618240061808339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36259633907490986749077785 27194725430618240061808339)
        ·
          refine ⟨40792088145927360092712509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27194725430618240061808339 40792088145927360092712509)
          ·
            refine ⟨15297033054722760034767191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40792088145927360092712509 15297033054722760034767191)
            ·
              refine ⟨22945549582084140052150787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15297033054722760034767191 22945549582084140052150787)
              ·
                refine ⟨34418324373126210078226181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22945549582084140052150787 34418324373126210078226181)
                ·
                  refine ⟨6453435819961164389667409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34418324373126210078226181 6453435819961164389667409)
                  ·
                    refine ⟨4840076864970873292250557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6453435819961164389667409 4840076864970873292250557)
                    ·
                      refine ⟨1815028824364077484593959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4840076864970873292250557 1815028824364077484593959)
                      ·
                        rfl

theorem cell23_3534756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_3534756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534756 prefixEnd_3534756 := by exact prefixLift 3534756
  have htrace : WordTrace (prefixWord ++ tailWord_3534756) baseStart_3534756 baseEnd_3534756 := by
    simpa [prefixWord, tailWord_3534756, baseEnd_3534756] using wordTrace_append hprefix tailTrace_3534756
  have hstable : (prefixWord ++ tailWord_3534756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534756).length < 2 ^ (prefixWord ++ tailWord_3534756).sum := by decide
  have hdescent : baseEnd_3534756 < baseStart_3534756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534820 : List Nat := [2, 3, 1, 1, 1, 1, 5, 4, 1, 1, 3]
def baseStart_3534820 : Nat := 118140960795 + 3534820 * 2 ^ 59
def prefixEnd_3534820 : Nat := 4983230072969 + 3 ^ 40 * 3534820 * 2
def baseEnd_3534820 : Nat := 1815061687125965234193665

theorem tailTrace_3534820 : CollatzResearch.WordTrace tailWord_3534820 prefixEnd_3534820 1815061687125965234193665 := by
  unfold tailWord_3534820
  simp only [CollatzResearch.WordTrace]
  refine ⟨64462738526979157019080957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85950318035972209358774609 64462738526979157019080957)
  ·
    refine ⟨24173526947617183882155359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 64462738526979157019080957 24173526947617183882155359)
    ·
      refine ⟨36260290421425775823233039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24173526947617183882155359 36260290421425775823233039)
      ·
        refine ⟨54390435632138663734849559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36260290421425775823233039 54390435632138663734849559)
        ·
          refine ⟨81585653448207995602274339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54390435632138663734849559 81585653448207995602274339)
          ·
            refine ⟨122378480172311993403411509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81585653448207995602274339 122378480172311993403411509)
            ·
              refine ⟨11472982516154249381569829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122378480172311993403411509 11472982516154249381569829)
              ·
                refine ⟨2151184221778921759044343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11472982516154249381569829 2151184221778921759044343)
                ·
                  refine ⟨3226776332668382638566515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2151184221778921759044343 3226776332668382638566515)
                  ·
                    refine ⟨4840164499002573957849773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3226776332668382638566515 4840164499002573957849773)
                    ·
                      refine ⟨1815061687125965234193665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4840164499002573957849773 1815061687125965234193665)
                      ·
                        rfl

theorem cell23_3534820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 4, 1, 1, 3].length) (baseStart_3534820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534820 prefixEnd_3534820 := by exact prefixLift 3534820
  have htrace : WordTrace (prefixWord ++ tailWord_3534820) baseStart_3534820 baseEnd_3534820 := by
    simpa [prefixWord, tailWord_3534820, baseEnd_3534820] using wordTrace_append hprefix tailTrace_3534820
  have hstable : (prefixWord ++ tailWord_3534820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534820).length < 2 ^ (prefixWord ++ tailWord_3534820).sum := by decide
  have hdescent : baseEnd_3534820 < baseStart_3534820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534826 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_3534826 : Nat := 118140960795 + 3534826 * 2 ^ 59
def prefixEnd_3534826 : Nat := 4983230072969 + 3 ^ 40 * 3534826 * 2
def baseEnd_3534826 : Nat := 1815064768009892210718637

theorem tailTrace_3534826 : CollatzResearch.WordTrace tailWord_3534826 prefixEnd_3534826 1815064768009892210718637 := by
  unfold tailWord_3534826
  simp only [CollatzResearch.WordTrace]
  refine ⟨32231423972984144265720083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85950463927957718041920221 32231423972984144265720083)
  ·
    refine ⟨48347135959476216398580125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32231423972984144265720083 48347135959476216398580125)
    ·
      refine ⟨18130175984803581149467547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48347135959476216398580125 18130175984803581149467547)
      ·
        refine ⟨27195263977205371724201321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18130175984803581149467547 27195263977205371724201321)
        ·
          refine ⟨20396447982904028793150991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27195263977205371724201321 20396447982904028793150991)
          ·
            refine ⟨30594671974356043189726487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20396447982904028793150991 30594671974356043189726487)
            ·
              refine ⟨45892007961534064784589731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30594671974356043189726487 45892007961534064784589731)
              ·
                refine ⟨68838011942301097176884597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45892007961534064784589731 68838011942301097176884597)
                ·
                  refine ⟨6453563619590727860332931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 68838011942301097176884597 6453563619590727860332931)
                  ·
                    refine ⟨9680345429386091790499397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6453563619590727860332931 9680345429386091790499397)
                    ·
                      refine ⟨1815064768009892210718637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9680345429386091790499397 1815064768009892210718637)
                      ·
                        rfl

theorem cell23_3534826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_3534826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534826 prefixEnd_3534826 := by exact prefixLift 3534826
  have htrace : WordTrace (prefixWord ++ tailWord_3534826) baseStart_3534826 baseEnd_3534826 := by
    simpa [prefixWord, tailWord_3534826, baseEnd_3534826] using wordTrace_append hprefix tailTrace_3534826
  have hstable : (prefixWord ++ tailWord_3534826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534826).length < 2 ^ (prefixWord ++ tailWord_3534826).sum := by decide
  have hdescent : baseEnd_3534826 < baseStart_3534826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534843 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 5, 2, 2]
def baseStart_3534843 : Nat := 118140960795 + 3534843 * 2 ^ 59
def prefixEnd_3534843 : Nat := 4983230072969 + 3 ^ 40 * 3534843 * 2
def baseEnd_3534843 : Nat := 1815073497181018644206059

theorem tailTrace_3534843 : CollatzResearch.WordTrace tailWord_3534843 prefixEnd_3534843 1815073497181018644206059 := by
  unfold tailWord_3534843
  simp only [CollatzResearch.WordTrace]
  refine ⟨128926315932874988966249183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85950877288583325977499455 128926315932874988966249183)
  ·
    refine ⟨193389473899312483449373775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128926315932874988966249183 193389473899312483449373775)
    ·
      refine ⟨290084210848968725174060663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 193389473899312483449373775 290084210848968725174060663)
      ·
        refine ⟨435126316273453087761090995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 290084210848968725174060663 435126316273453087761090995)
        ·
          refine ⟨652689474410179631641636493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 435126316273453087761090995 652689474410179631641636493)
          ·
            refine ⟨244758552903817361865613685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 652689474410179631641636493 244758552903817361865613685)
            ·
              refine ⟨22946114334732877674901283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 244758552903817361865613685 22946114334732877674901283)
              ·
                refine ⟨34419171502099316512351925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22946114334732877674901283 34419171502099316512351925)
                ·
                  refine ⟨3226797328321810923032993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34419171502099316512351925 3226797328321810923032993)
                  ·
                    refine ⟨2420097996241358192274745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3226797328321810923032993 2420097996241358192274745)
                    ·
                      refine ⟨1815073497181018644206059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2420097996241358192274745 1815073497181018644206059)
                      ·
                        rfl

theorem cell23_3534843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 2, 2].length) (baseStart_3534843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534843 prefixEnd_3534843 := by exact prefixLift 3534843
  have htrace : WordTrace (prefixWord ++ tailWord_3534843) baseStart_3534843 baseEnd_3534843 := by
    simpa [prefixWord, tailWord_3534843, baseEnd_3534843] using wordTrace_append hprefix tailTrace_3534843
  have hstable : (prefixWord ++ tailWord_3534843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534843).length < 2 ^ (prefixWord ++ tailWord_3534843).sum := by decide
  have hdescent : baseEnd_3534843 < baseStart_3534843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534856 : List Nat := [2, 1, 3, 2, 1, 2, 1, 4, 1, 2, 4]
def baseStart_3534856 : Nat := 118140960795 + 3534856 * 2 ^ 59
def prefixEnd_3534856 : Nat := 4983230072969 + 3 ^ 40 * 3534856 * 2
def baseEnd_3534856 : Nat := 1815080172429527093343499

theorem tailTrace_3534856 : CollatzResearch.WordTrace tailWord_3534856 prefixEnd_3534856 1815080172429527093343499 := by
  unfold tailWord_3534856
  simp only [CollatzResearch.WordTrace]
  refine ⟨64463395040913946093236211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85951193387885261457648281 64463395040913946093236211)
  ·
    refine ⟨96695092561370919139854317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64463395040913946093236211 96695092561370919139854317)
    ·
      refine ⟨36260659710514094677445369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96695092561370919139854317 36260659710514094677445369)
      ·
        refine ⟨27195494782885571008084027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36260659710514094677445369 27195494782885571008084027)
        ·
          refine ⟨40793242174328356512126041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27195494782885571008084027 40793242174328356512126041)
          ·
            refine ⟨30594931630746267384094531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40793242174328356512126041 30594931630746267384094531)
            ·
              refine ⟨45892397446119401076141797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30594931630746267384094531 45892397446119401076141797)
              ·
                refine ⟨8604824521147387701776587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45892397446119401076141797 8604824521147387701776587)
                ·
                  refine ⟨12907236781721081552664881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8604824521147387701776587 12907236781721081552664881)
                  ·
                    refine ⟨9680427586290811164498661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12907236781721081552664881 9680427586290811164498661)
                    ·
                      refine ⟨1815080172429527093343499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9680427586290811164498661 1815080172429527093343499)
                      ·
                        rfl

theorem cell23_3534856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_3534856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534856 prefixEnd_3534856 := by exact prefixLift 3534856
  have htrace : WordTrace (prefixWord ++ tailWord_3534856) baseStart_3534856 baseEnd_3534856 := by
    simpa [prefixWord, tailWord_3534856, baseEnd_3534856] using wordTrace_append hprefix tailTrace_3534856
  have hstable : (prefixWord ++ tailWord_3534856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534856).length < 2 ^ (prefixWord ++ tailWord_3534856).sum := by decide
  have hdescent : baseEnd_3534856 < baseStart_3534856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534877 : List Nat := [1, 4, 2, 2, 2, 2, 2, 1, 3, 2, 2]
def baseStart_3534877 : Nat := 118140960795 + 3534877 * 2 ^ 59
def prefixEnd_3534877 : Nat := 4983230072969 + 3 ^ 40 * 3534877 * 2
def baseEnd_3534877 : Nat := 1815090955523271511180903

theorem tailTrace_3534877 : CollatzResearch.WordTrace tailWord_3534877 prefixEnd_3534877 1815090955523271511180903 := by
  unfold tailWord_3534877
  simp only [CollatzResearch.WordTrace]
  refine ⟨128927556014751812772986885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85951704009834541848657923 128927556014751812772986885)
  ·
    refine ⟨24173916752765964894935041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 128927556014751812772986885 24173916752765964894935041)
    ·
      refine ⟨18130437564574473671201281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24173916752765964894935041 18130437564574473671201281)
      ·
        refine ⟨13597828173430855253400961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18130437564574473671201281 13597828173430855253400961)
        ·
          refine ⟨10198371130073141440050721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13597828173430855253400961 10198371130073141440050721)
          ·
            refine ⟨7648778347554856080038041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10198371130073141440050721 7648778347554856080038041)
            ·
              refine ⟨5736583760666142060028531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7648778347554856080038041 5736583760666142060028531)
              ·
                refine ⟨8604875640999213090042797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5736583760666142060028531 8604875640999213090042797)
                ·
                  refine ⟨3226828365374704908766049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8604875640999213090042797 3226828365374704908766049)
                  ·
                    refine ⟨2420121274031028681574537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3226828365374704908766049 2420121274031028681574537)
                    ·
                      refine ⟨1815090955523271511180903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2420121274031028681574537 1815090955523271511180903)
                      ·
                        rfl

theorem cell23_3534877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_3534877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534877 prefixEnd_3534877 := by exact prefixLift 3534877
  have htrace : WordTrace (prefixWord ++ tailWord_3534877) baseStart_3534877 baseEnd_3534877 := by
    simpa [prefixWord, tailWord_3534877, baseEnd_3534877] using wordTrace_append hprefix tailTrace_3534877
  have hstable : (prefixWord ++ tailWord_3534877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534877).length < 2 ^ (prefixWord ++ tailWord_3534877).sum := by decide
  have hdescent : baseEnd_3534877 < baseStart_3534877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534887 : List Nat := [1, 1, 7, 1, 3, 1, 1, 1, 1, 6]
def baseStart_3534887 : Nat := 118140960795 + 3534887 * 2 ^ 59
def prefixEnd_3534887 : Nat := 4983230072969 + 3 ^ 40 * 3534887 * 2
def baseEnd_3534887 : Nat := 605032030109938824018619

theorem tailTrace_3534887 : CollatzResearch.WordTrace tailWord_3534887 prefixEnd_3534887 605032030109938824018619 := by
  unfold tailWord_3534887
  simp only [CollatzResearch.WordTrace]
  refine ⟨128927920744715584480850915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85951947163143722987233943 128927920744715584480850915)
  ·
    refine ⟨193391881117073376721276373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128927920744715584480850915 193391881117073376721276373)
    ·
      refine ⟨4532622213681407266904915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 193391881117073376721276373 4532622213681407266904915)
      ·
        refine ⟨6798933320522110900357373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4532622213681407266904915 6798933320522110900357373)
        ·
          refine ⟨2549599995195791587634015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6798933320522110900357373 2549599995195791587634015)
          ·
            refine ⟨3824399992793687381451023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549599995195791587634015 3824399992793687381451023)
            ·
              refine ⟨5736599989190531072176535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824399992793687381451023 5736599989190531072176535)
              ·
                refine ⟨8604899983785796608264803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5736599989190531072176535 8604899983785796608264803)
                ·
                  refine ⟨12907349975678694912397205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8604899983785796608264803 12907349975678694912397205)
                  ·
                    refine ⟨605032030109938824018619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12907349975678694912397205 605032030109938824018619)
                    ·
                      rfl

theorem cell23_3534887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_3534887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534887 prefixEnd_3534887 := by exact prefixLift 3534887
  have htrace : WordTrace (prefixWord ++ tailWord_3534887) baseStart_3534887 baseEnd_3534887 := by
    simpa [prefixWord, tailWord_3534887, baseEnd_3534887] using wordTrace_append hprefix tailTrace_3534887
  have hstable : (prefixWord ++ tailWord_3534887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534887).length < 2 ^ (prefixWord ++ tailWord_3534887).sum := by decide
  have hdescent : baseEnd_3534887 < baseStart_3534887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534890 : List Nat := [3, 1, 4, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_3534890 : Nat := 118140960795 + 3534890 * 2 ^ 59
def prefixEnd_3534890 : Nat := 4983230072969 + 3 ^ 40 * 3534890 * 2
def baseEnd_3534890 : Nat := 1815097630771779960318343

theorem tailTrace_3534890 : CollatzResearch.WordTrace tailWord_3534890 prefixEnd_3534890 1815097630771779960318343 := by
  unfold tailWord_3534890
  simp only [CollatzResearch.WordTrace]
  refine ⟨32232007540926178998302531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85952020109136477328806749 32232007540926178998302531)
  ·
    refine ⟨48348011311389268497453797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32232007540926178998302531 48348011311389268497453797)
    ·
      refine ⟨9065252120885487843272587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48348011311389268497453797 9065252120885487843272587)
      ·
        refine ⟨13597878181328231764908881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9065252120885487843272587 13597878181328231764908881)
        ·
          refine ⟨10198408635996173823681661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13597878181328231764908881 10198408635996173823681661)
          ·
            refine ⟨3824403238498565183880623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10198408635996173823681661 3824403238498565183880623)
            ·
              refine ⟨5736604857747847775820935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824403238498565183880623 5736604857747847775820935)
              ·
                refine ⟨8604907286621771663731403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5736604857747847775820935 8604907286621771663731403)
                ·
                  refine ⟨12907360929932657495597105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8604907286621771663731403 12907360929932657495597105)
                  ·
                    refine ⟨9680520697449493121697829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12907360929932657495597105 9680520697449493121697829)
                    ·
                      refine ⟨1815097630771779960318343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9680520697449493121697829 1815097630771779960318343)
                      ·
                        rfl

theorem cell23_3534890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_3534890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534890 prefixEnd_3534890 := by exact prefixLift 3534890
  have htrace : WordTrace (prefixWord ++ tailWord_3534890) baseStart_3534890 baseEnd_3534890 := by
    simpa [prefixWord, tailWord_3534890, baseEnd_3534890] using wordTrace_append hprefix tailTrace_3534890
  have hstable : (prefixWord ++ tailWord_3534890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534890).length < 2 ^ (prefixWord ++ tailWord_3534890).sum := by decide
  have hdescent : baseEnd_3534890 < baseStart_3534890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534903 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 3, 3, 2]
def baseStart_3534903 : Nat := 118140960795 + 3534903 * 2 ^ 59
def prefixEnd_3534903 : Nat := 4983230072969 + 3 ^ 40 * 3534903 * 2
def baseEnd_3534903 : Nat := 1815104306020288409455783

theorem tailTrace_3534903 : CollatzResearch.WordTrace tailWord_3534903 prefixEnd_3534903 1815104306020288409455783 := by
  unfold tailWord_3534903
  simp only [CollatzResearch.WordTrace]
  refine ⟨128928504312657619213433363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85952336208438412808955575 128928504312657619213433363)
  ·
    refine ⟨193392756468986428820150045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128928504312657619213433363 193392756468986428820150045)
    ·
      refine ⟨72522283675869910807556267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 193392756468986428820150045 72522283675869910807556267)
      ·
        refine ⟨108783425513804866211334401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72522283675869910807556267 108783425513804866211334401)
        ·
          refine ⟨81587569135353649658500801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108783425513804866211334401 81587569135353649658500801)
          ·
            refine ⟨61190676851515237243875601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81587569135353649658500801 61190676851515237243875601)
            ·
              refine ⟨45893007638636427932906701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61190676851515237243875601 45893007638636427932906701)
              ·
                refine ⟨17209877864488660474840013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45893007638636427932906701 17209877864488660474840013)
                ·
                  refine ⟨6453704199183247678065005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17209877864488660474840013 6453704199183247678065005)
                  ·
                    refine ⟨2420139074693717879274377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6453704199183247678065005 2420139074693717879274377)
                    ·
                      refine ⟨1815104306020288409455783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2420139074693717879274377 1815104306020288409455783)
                      ·
                        rfl

theorem cell23_3534903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 3, 2].length) (baseStart_3534903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534903 prefixEnd_3534903 := by exact prefixLift 3534903
  have htrace : WordTrace (prefixWord ++ tailWord_3534903) baseStart_3534903 baseEnd_3534903 := by
    simpa [prefixWord, tailWord_3534903, baseEnd_3534903] using wordTrace_append hprefix tailTrace_3534903
  have hstable : (prefixWord ++ tailWord_3534903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534903).length < 2 ^ (prefixWord ++ tailWord_3534903).sum := by decide
  have hdescent : baseEnd_3534903 < baseStart_3534903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534954 : List Nat := [3, 1, 3, 2, 3, 2, 1, 2, 1, 3, 2]
def baseStart_3534954 : Nat := 118140960795 + 3534954 * 2 ^ 59
def prefixEnd_3534954 : Nat := 4983230072969 + 3 ^ 40 * 3534954 * 2
def baseEnd_3534954 : Nat := 1815130493533667709918049

theorem tailTrace_3534954 : CollatzResearch.WordTrace tailWord_3534954 prefixEnd_3534954 1815130493533667709918049 := by
  unfold tailWord_3534954
  simp only [CollatzResearch.WordTrace]
  refine ⟨32232591108868213730884979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85953576290315236615693277 32232591108868213730884979)
  ·
    refine ⟨48348886663302320596327469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32232591108868213730884979 48348886663302320596327469)
    ·
      refine ⟨18130832498738370223622801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48348886663302320596327469 18130832498738370223622801)
      ·
        refine ⟨13598124374053777667717101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18130832498738370223622801 13598124374053777667717101)
        ·
          refine ⟨5099296640270166625393913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13598124374053777667717101 5099296640270166625393913)
          ·
            refine ⟨3824472480202624969045435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5099296640270166625393913 3824472480202624969045435)
            ·
              refine ⟨5736708720303937453568153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824472480202624969045435 5736708720303937453568153)
              ·
                refine ⟨4302531540227953090176115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5736708720303937453568153 4302531540227953090176115)
                ·
                  refine ⟨6453797310341929635264173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4302531540227953090176115 6453797310341929635264173)
                  ·
                    refine ⟨2420173991378223613224065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6453797310341929635264173 2420173991378223613224065)
                    ·
                      refine ⟨1815130493533667709918049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2420173991378223613224065 1815130493533667709918049)
                      ·
                        rfl

theorem cell23_3534954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_3534954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534954 prefixEnd_3534954 := by exact prefixLift 3534954
  have htrace : WordTrace (prefixWord ++ tailWord_3534954) baseStart_3534954 baseEnd_3534954 := by
    simpa [prefixWord, tailWord_3534954, baseEnd_3534954] using wordTrace_append hprefix tailTrace_3534954
  have hstable : (prefixWord ++ tailWord_3534954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534954).length < 2 ^ (prefixWord ++ tailWord_3534954).sum := by decide
  have hdescent : baseEnd_3534954 < baseStart_3534954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3534984 : List Nat := [2, 1, 3, 4, 1, 2, 2, 2, 2, 2, 2]
def baseStart_3534984 : Nat := 118140960795 + 3534984 * 2 ^ 59
def prefixEnd_3534984 : Nat := 4983230072969 + 3 ^ 40 * 3534984 * 2
def baseEnd_3534984 : Nat := 1815145897953302592542911

theorem tailTrace_3534984 : CollatzResearch.WordTrace tailWord_3534984 prefixEnd_3534984 1815145897953302592542911 := by
  unfold tailWord_3534984
  simp only [CollatzResearch.WordTrace]
  refine ⟨64465729312682085023566003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85954305750242780031421337 64465729312682085023566003)
  ·
    refine ⟨96698593969023127535349005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64465729312682085023566003 96698593969023127535349005)
    ·
      refine ⟨36261972738383672825755877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 96698593969023127535349005 36261972738383672825755877)
      ·
        refine ⟨6799119888446938654829227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36261972738383672825755877 6799119888446938654829227)
        ·
          refine ⟨10198679832670407982243841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6799119888446938654829227 10198679832670407982243841)
          ·
            refine ⟨7649009874502805986682881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10198679832670407982243841 7649009874502805986682881)
            ·
              refine ⟨5736757405877104490012161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7649009874502805986682881 5736757405877104490012161)
              ·
                refine ⟨4302568054407828367509121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5736757405877104490012161 4302568054407828367509121)
                ·
                  refine ⟨3226926040805871275631841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4302568054407828367509121 3226926040805871275631841)
                  ·
                    refine ⟨2420194530604403456723881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3226926040805871275631841 2420194530604403456723881)
                    ·
                      refine ⟨1815145897953302592542911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2420194530604403456723881 1815145897953302592542911)
                      ·
                        rfl

theorem cell23_3534984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_3534984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3534984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3534984 prefixEnd_3534984 := by exact prefixLift 3534984
  have htrace : WordTrace (prefixWord ++ tailWord_3534984) baseStart_3534984 baseEnd_3534984 := by
    simpa [prefixWord, tailWord_3534984, baseEnd_3534984] using wordTrace_append hprefix tailTrace_3534984
  have hstable : (prefixWord ++ tailWord_3534984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3534984).length < 2 ^ (prefixWord ++ tailWord_3534984).sum := by decide
  have hdescent : baseEnd_3534984 < baseStart_3534984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3534984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535000 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 2, 3, 3]
def baseStart_3535000 : Nat := 118140960795 + 3535000 * 2 ^ 59
def prefixEnd_3535000 : Nat := 4983230072969 + 3 ^ 40 * 3535000 * 2
def baseEnd_3535000 : Nat := 1815154113643774529942837

theorem tailTrace_3535000 : CollatzResearch.WordTrace tailWord_3535000 prefixEnd_3535000 1815154113643774529942837 := by
  unfold tailWord_3535000
  simp only [CollatzResearch.WordTrace]
  refine ⟨64466021096653102389857227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85954694795537469853142969 64466021096653102389857227)
  ·
    refine ⟨96699031644979653584785841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64466021096653102389857227 96699031644979653584785841)
    ·
      refine ⟨72524273733734740188589381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 96699031644979653584785841 72524273733734740188589381)
      ·
        refine ⟨13598301325075263785360509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72524273733734740188589381 13598301325075263785360509)
        ·
          refine ⟨5099362996903223919510191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13598301325075263785360509 5099362996903223919510191)
          ·
            refine ⟨7649044495354835879265287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5099362996903223919510191 7649044495354835879265287)
            ·
              refine ⟨11473566743032253818897931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7649044495354835879265287 11473566743032253818897931)
              ·
                refine ⟨17210350114548380728346897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11473566743032253818897931 17210350114548380728346897)
                ·
                  refine ⟨12907762585911285546260173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17210350114548380728346897 12907762585911285546260173)
                  ·
                    refine ⟨4840410969716732079847565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12907762585911285546260173 4840410969716732079847565)
                    ·
                      refine ⟨1815154113643774529942837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4840410969716732079847565 1815154113643774529942837)
                      ·
                        rfl

theorem cell23_3535000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_3535000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535000 prefixEnd_3535000 := by exact prefixLift 3535000
  have htrace : WordTrace (prefixWord ++ tailWord_3535000) baseStart_3535000 baseEnd_3535000 := by
    simpa [prefixWord, tailWord_3535000, baseEnd_3535000] using wordTrace_append hprefix tailTrace_3535000
  have hstable : (prefixWord ++ tailWord_3535000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535000).length < 2 ^ (prefixWord ++ tailWord_3535000).sum := by decide
  have hdescent : baseEnd_3535000 < baseStart_3535000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535023 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 3, 6, 2]
def baseStart_3535023 : Nat := 118140960795 + 3535023 * 2 ^ 59
def prefixEnd_3535023 : Nat := 4983230072969 + 3 ^ 40 * 3535023 * 2
def baseEnd_3535023 : Nat := 1815165923698827939955231

theorem tailTrace_3535023 : CollatzResearch.WordTrace tailWord_3535023 prefixEnd_3535023 1815165923698827939955231 := by
  unfold tailWord_3535023
  simp only [CollatzResearch.WordTrace]
  refine ⟨128932881072222879707801723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85955254048148586471867815 128932881072222879707801723)
  ·
    refine ⟨193399321608334319561702585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 128932881072222879707801723 193399321608334319561702585)
    ·
      refine ⟨145049491206250739671276939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 193399321608334319561702585 145049491206250739671276939)
      ·
        refine ⟨217574236809376109506915409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145049491206250739671276939 217574236809376109506915409)
        ·
          refine ⟨163180677607032082130186557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 217574236809376109506915409 163180677607032082130186557)
          ·
            refine ⟨61192754102637030798819959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 163180677607032082130186557 61192754102637030798819959)
            ·
              refine ⟨91789131153955546198229939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61192754102637030798819959 91789131153955546198229939)
              ·
                refine ⟨137683696730933319297344909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 91789131153955546198229939 137683696730933319297344909)
                ·
                  refine ⟨51631386274099994736504341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 137683696730933319297344909 51631386274099994736504341)
                  ·
                    refine ⟨2420221231598437253273641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 51631386274099994736504341 2420221231598437253273641)
                    ·
                      refine ⟨1815165923698827939955231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2420221231598437253273641 1815165923698827939955231)
                      ·
                        rfl

theorem cell23_3535023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 6, 2].length) (baseStart_3535023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535023 prefixEnd_3535023 := by exact prefixLift 3535023
  have htrace : WordTrace (prefixWord ++ tailWord_3535023) baseStart_3535023 baseEnd_3535023 := by
    simpa [prefixWord, tailWord_3535023, baseEnd_3535023] using wordTrace_append hprefix tailTrace_3535023
  have hstable : (prefixWord ++ tailWord_3535023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535023).length < 2 ^ (prefixWord ++ tailWord_3535023).sum := by decide
  have hdescent : baseEnd_3535023 < baseStart_3535023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535033 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 5, 4]
def baseStart_3535033 : Nat := 118140960795 + 3535033 * 2 ^ 59
def prefixEnd_3535033 : Nat := 4983230072969 + 3 ^ 40 * 3535033 * 2
def baseEnd_3535033 : Nat := 605057019501790966943395

theorem tailTrace_3535033 : CollatzResearch.WordTrace tailWord_3535033 prefixEnd_3535033 605057019501790966943395 := by
  unfold tailWord_3535033
  simp only [CollatzResearch.WordTrace]
  refine ⟨128933245802186651415665753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 85955497201457767610443835 128933245802186651415665753)
  ·
    refine ⟨96699934351639988561749315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128933245802186651415665753 96699934351639988561749315)
    ·
      refine ⟨145049901527459982842623973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96699934351639988561749315 145049901527459982842623973)
      ·
        refine ⟨27196856536398746782991995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 145049901527459982842623973 27196856536398746782991995)
        ·
          refine ⟨40795284804598120174487993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27196856536398746782991995 40795284804598120174487993)
          ·
            refine ⟨30596463603448590130865995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40795284804598120174487993 30596463603448590130865995)
            ·
              refine ⟨45894695405172885196298993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30596463603448590130865995 45894695405172885196298993)
              ·
                refine ⟨34421021553879663897224245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45894695405172885196298993 34421021553879663897224245)
                ·
                  refine ⟨3226970770676218490364773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34421021553879663897224245 3226970770676218490364773)
                  ·
                    refine ⟨605057019501790966943395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3226970770676218490364773 605057019501790966943395)
                    ·
                      rfl

theorem cell23_3535033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 4].length) (baseStart_3535033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535033 prefixEnd_3535033 := by exact prefixLift 3535033
  have htrace : WordTrace (prefixWord ++ tailWord_3535033) baseStart_3535033 baseEnd_3535033 := by
    simpa [prefixWord, tailWord_3535033, baseEnd_3535033] using wordTrace_append hprefix tailTrace_3535033
  have hstable : (prefixWord ++ tailWord_3535033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535033).length < 2 ^ (prefixWord ++ tailWord_3535033).sum := by decide
  have hdescent : baseEnd_3535033 < baseStart_3535033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535040 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 2, 4, 2]
def baseStart_3535040 : Nat := 118140960795 + 3535040 * 2 ^ 59
def prefixEnd_3535040 : Nat := 4983230072969 + 3 ^ 40 * 3535040 * 2
def baseEnd_3535040 : Nat := 1815174652869954373442653

theorem tailTrace_3535040 : CollatzResearch.WordTrace tailWord_3535040 prefixEnd_3535040 1815174652869954373442653 := by
  unfold tailWord_3535040
  simp only [CollatzResearch.WordTrace]
  refine ⟨64466750556580645805585287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 85955667408774194407447049 64466750556580645805585287)
  ·
    refine ⟨96700125834870968708377931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 64466750556580645805585287 96700125834870968708377931)
    ·
      refine ⟨145050188752306453062566897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96700125834870968708377931 145050188752306453062566897)
      ·
        refine ⟨108787641564229839796925173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 145050188752306453062566897 108787641564229839796925173)
        ·
          refine ⟨10198841396646547480961735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108787641564229839796925173 10198841396646547480961735)
          ·
            refine ⟨15298262094969821221442603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10198841396646547480961735 15298262094969821221442603)
            ·
              refine ⟨22947393142454731832163905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15298262094969821221442603 22947393142454731832163905)
              ·
                refine ⟨17210544856841048874122929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22947393142454731832163905 17210544856841048874122929)
                ·
                  refine ⟨12907908642630786655592197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17210544856841048874122929 12907908642630786655592197)
                  ·
                    refine ⟨2420232870493272497923537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12907908642630786655592197 2420232870493272497923537)
                    ·
                      refine ⟨1815174652869954373442653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2420232870493272497923537 1815174652869954373442653)
                      ·
                        rfl

theorem cell23_3535040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 2, 4, 2].length) (baseStart_3535040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535040 prefixEnd_3535040 := by exact prefixLift 3535040
  have htrace : WordTrace (prefixWord ++ tailWord_3535040) baseStart_3535040 baseEnd_3535040 := by
    simpa [prefixWord, tailWord_3535040, baseEnd_3535040] using wordTrace_append hprefix tailTrace_3535040
  have hstable : (prefixWord ++ tailWord_3535040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535040).length < 2 ^ (prefixWord ++ tailWord_3535040).sum := by decide
  have hdescent : baseEnd_3535040 < baseStart_3535040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3535050 : List Nat := [3, 1, 2, 1, 3, 1, 4, 1, 3, 4]
def baseStart_3535050 : Nat := 118140960795 + 3535050 * 2 ^ 59
def prefixEnd_3535050 : Nat := 4983230072969 + 3 ^ 40 * 3535050 * 2
def baseEnd_3535050 : Nat := 605059929225499778105869

theorem tailTrace_3535050 : CollatzResearch.WordTrace tailWord_3535050 prefixEnd_3535050 605059929225499778105869 := by
  unfold tailWord_3535050
  simp only [CollatzResearch.WordTrace]
  refine ⟨32233466460781265829758651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 85955910562083375546023069 32233466460781265829758651)
  ·
    refine ⟨48350199691171898744637977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32233466460781265829758651 48350199691171898744637977)
    ·
      refine ⟨36262649768378924058478483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48350199691171898744637977 36262649768378924058478483)
      ·
        refine ⟨54393974652568386087717725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36262649768378924058478483 54393974652568386087717725)
        ·
          refine ⟨20397740494713144782894147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54393974652568386087717725 20397740494713144782894147)
          ·
            refine ⟨30596610742069717174341221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20397740494713144782894147 30596610742069717174341221)
            ·
              refine ⟨5736864514138071970188979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30596610742069717174341221 5736864514138071970188979)
              ·
                refine ⟨8605296771207107955283469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5736864514138071970188979 8605296771207107955283469)
                ·
                  refine ⟨3226986289202665483231301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8605296771207107955283469 3226986289202665483231301)
                  ·
                    refine ⟨605059929225499778105869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3226986289202665483231301 605059929225499778105869)
                    ·
                      rfl

theorem cell23_3535050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_3535050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3535050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3535050 prefixEnd_3535050 := by exact prefixLift 3535050
  have htrace : WordTrace (prefixWord ++ tailWord_3535050) baseStart_3535050 baseEnd_3535050 := by
    simpa [prefixWord, tailWord_3535050, baseEnd_3535050] using wordTrace_append hprefix tailTrace_3535050
  have hstable : (prefixWord ++ tailWord_3535050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3535050).length < 2 ^ (prefixWord ++ tailWord_3535050).sum := by decide
  have hdescent : baseEnd_3535050 < baseStart_3535050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3535050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
