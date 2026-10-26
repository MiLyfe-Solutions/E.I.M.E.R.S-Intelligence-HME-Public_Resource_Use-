import V185TrunkScan19Chunk042

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_431784 : List Nat := [2, 1, 7, 1, 1, 2, 1, 4]
def baseStart_431784 : Nat := 118140960795 + 431784 * 2 ^ 59
def prefixEnd_431784 : Nat := 4983230072969 + 3 ^ 40 * 431784 * 2
def baseEnd_431784 : Nat := 131385322027285260334381

theorem tailTrace_431784 : CollatzResearch.WordTrace tailWord_431784 prefixEnd_431784 131385322027285260334381 := by
  unfold tailWord_431784
  simp only [CollatzResearch.WordTrace]
  refine ⟨7874228133863892840671203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10498970845151857120894937 7874228133863892840671203)
  ·
    refine ⟨11811342200795839261006805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7874228133863892840671203 11811342200795839261006805)
    ·
      refine ⟨276828332831152482679847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 11811342200795839261006805 276828332831152482679847)
      ·
        refine ⟨415242499246728724019771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276828332831152482679847 415242499246728724019771)
        ·
          refine ⟨622863748870093086029657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415242499246728724019771 622863748870093086029657)
          ·
            refine ⟨467147811652569814522243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622863748870093086029657 467147811652569814522243)
            ·
              refine ⟨700721717478854721783365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467147811652569814522243 700721717478854721783365)
              ·
                refine ⟨131385322027285260334381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 700721717478854721783365 131385322027285260334381)
                ·
                  rfl

theorem cell19_431784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 4].length) (baseStart_431784 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431784 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431784 prefixEnd_431784 := by exact prefixLift 431784
  have htrace : WordTrace (prefixWord ++ tailWord_431784) baseStart_431784 baseEnd_431784 := by
    simpa [prefixWord, tailWord_431784, baseEnd_431784] using wordTrace_append hprefix tailTrace_431784
  have hstable : (prefixWord ++ tailWord_431784).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431784).length < 2 ^ (prefixWord ++ tailWord_431784).sum := by decide
  have hdescent : baseEnd_431784 < baseStart_431784 := by decide
  rcases family_descends (prefixWord ++ tailWord_431784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431792 : List Nat := [2, 1, 1, 1, 2, 1, 7, 4]
def baseStart_431792 : Nat := 118140960795 + 431792 * 2 ^ 59
def prefixEnd_431792 : Nat := 4983230072969 + 3 ^ 40 * 431792 * 2
def baseEnd_431792 : Nat := 131387756305943612156581

theorem tailTrace_431792 : CollatzResearch.WordTrace tailWord_431792 prefixEnd_431792 131387756305943612156581 := by
  unfold tailWord_431792
  simp only [CollatzResearch.WordTrace]
  refine ⟨7874374025849401523816815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10499165367799202031755753 7874374025849401523816815)
  ·
    refine ⟨11811561038774102285725223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7874374025849401523816815 11811561038774102285725223)
    ·
      refine ⟨17717341558161153428587835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11811561038774102285725223 17717341558161153428587835)
      ·
        refine ⟨26576012337241730142881753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17717341558161153428587835 26576012337241730142881753)
        ·
          refine ⟨19932009252931297607161315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26576012337241730142881753 19932009252931297607161315)
          ·
            refine ⟨29898013879396946410741973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19932009252931297607161315 29898013879396946410741973)
            ·
              refine ⟨700734700298365931501765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 29898013879396946410741973 700734700298365931501765)
              ·
                refine ⟨131387756305943612156581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 700734700298365931501765 131387756305943612156581)
                ·
                  rfl

theorem cell19_431792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_431792 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431792 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431792 prefixEnd_431792 := by exact prefixLift 431792
  have htrace : WordTrace (prefixWord ++ tailWord_431792) baseStart_431792 baseEnd_431792 := by
    simpa [prefixWord, tailWord_431792, baseEnd_431792] using wordTrace_append hprefix tailTrace_431792
  have hstable : (prefixWord ++ tailWord_431792).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431792).length < 2 ^ (prefixWord ++ tailWord_431792).sum := by decide
  have hdescent : baseEnd_431792 < baseStart_431792 := by decide
  rcases family_descends (prefixWord ++ tailWord_431792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431828 : List Nat := [2, 4, 1, 3, 1, 2, 6]
def baseStart_431828 : Nat := 118140960795 + 431828 * 2 ^ 59
def prefixEnd_431828 : Nat := 4983230072969 + 3 ^ 40 * 431828 * 2
def baseEnd_431828 : Nat := 43799570186635398452161

theorem tailTrace_431828 : CollatzResearch.WordTrace tailWord_431828 prefixEnd_431828 43799570186635398452161 := by
  unfold tailWord_431828
  simp only [CollatzResearch.WordTrace]
  refine ⟨7875030539784190597972069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10500040719712254130629425 7875030539784190597972069)
  ·
    refine ⟨1476568226209535737119763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7875030539784190597972069 1476568226209535737119763)
    ·
      refine ⟨2214852339314303605679645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1476568226209535737119763 2214852339314303605679645)
      ·
        refine ⟨830569627242863852129867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2214852339314303605679645 830569627242863852129867)
        ·
          refine ⟨1245854440864295778194801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830569627242863852129867 1245854440864295778194801)
          ·
            refine ⟨934390830648221833646101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1245854440864295778194801 934390830648221833646101)
            ·
              refine ⟨43799570186635398452161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 934390830648221833646101 43799570186635398452161)
              ·
                rfl

theorem cell19_431828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 6].length) (baseStart_431828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431828 prefixEnd_431828 := by exact prefixLift 431828
  have htrace : WordTrace (prefixWord ++ tailWord_431828) baseStart_431828 baseEnd_431828 := by
    simpa [prefixWord, tailWord_431828, baseEnd_431828] using wordTrace_append hprefix tailTrace_431828
  have hstable : (prefixWord ++ tailWord_431828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431828).length < 2 ^ (prefixWord ++ tailWord_431828).sum := by decide
  have hdescent : baseEnd_431828 < baseStart_431828 := by decide
  rcases family_descends (prefixWord ++ tailWord_431828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431860 : List Nat := [2, 6, 1, 1, 1, 3, 2, 3]
def baseStart_431860 : Nat := 118140960795 + 431860 * 2 ^ 59
def prefixEnd_431860 : Nat := 4983230072969 + 3 ^ 40 * 431860 * 2
def baseEnd_431860 : Nat := 131408447674539602645285

theorem tailTrace_431860 : CollatzResearch.WordTrace tailWord_431860 prefixEnd_431860 131408447674539602645285 := by
  unfold tailWord_431860
  simp only [CollatzResearch.WordTrace]
  refine ⟨7875614107726225330554517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10500818810301633774072689 7875614107726225330554517)
  ·
    refine ⟨369169411299666812369743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7875614107726225330554517 369169411299666812369743)
    ·
      refine ⟨553754116949500218554615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369169411299666812369743 553754116949500218554615)
      ·
        refine ⟨830631175424250327831923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553754116949500218554615 830631175424250327831923)
        ·
          refine ⟨1245946763136375491747885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830631175424250327831923 1245946763136375491747885)
          ·
            refine ⟨467230036176140809405457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1245946763136375491747885 467230036176140809405457)
            ·
              refine ⟨350422527132105607054093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467230036176140809405457 350422527132105607054093)
              ·
                refine ⟨131408447674539602645285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 350422527132105607054093 131408447674539602645285)
                ·
                  rfl

theorem cell19_431860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_431860 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431860 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431860 prefixEnd_431860 := by exact prefixLift 431860
  have htrace : WordTrace (prefixWord ++ tailWord_431860) baseStart_431860 baseEnd_431860 := by
    simpa [prefixWord, tailWord_431860, baseEnd_431860] using wordTrace_append hprefix tailTrace_431860
  have hstable : (prefixWord ++ tailWord_431860).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431860).length < 2 ^ (prefixWord ++ tailWord_431860).sum := by decide
  have hdescent : baseEnd_431860 < baseStart_431860 := by decide
  rcases family_descends (prefixWord ++ tailWord_431860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431868 : List Nat := [2, 2, 2, 1, 3, 1, 3, 5]
def baseStart_431868 : Nat := 118140960795 + 431868 * 2 ^ 59
def prefixEnd_431868 : Nat := 4983230072969 + 3 ^ 40 * 431868 * 2
def baseEnd_431868 : Nat := 131410881953197954467485

theorem tailTrace_431868 : CollatzResearch.WordTrace tailWord_431868 prefixEnd_431868 131410881953197954467485 := by
  unfold tailWord_431868
  simp only [CollatzResearch.WordTrace]
  refine ⟨7875759999711734013700129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10501013332948978684933505 7875759999711734013700129)
  ·
    refine ⟨5906819999783800510275097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7875759999711734013700129 5906819999783800510275097)
    ·
      refine ⟨4430114999837850382706323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5906819999783800510275097 4430114999837850382706323)
      ·
        refine ⟨6645172499756775574059485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4430114999837850382706323 6645172499756775574059485)
        ·
          refine ⟨2491939687408790840272307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6645172499756775574059485 2491939687408790840272307)
          ·
            refine ⟨3737909531113186260408461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2491939687408790840272307 3737909531113186260408461)
            ·
              refine ⟨1401716074167444847653173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3737909531113186260408461 1401716074167444847653173)
              ·
                refine ⟨131410881953197954467485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1401716074167444847653173 131410881953197954467485)
                ·
                  rfl

theorem cell19_431868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_431868 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431868 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431868 prefixEnd_431868 := by exact prefixLift 431868
  have htrace : WordTrace (prefixWord ++ tailWord_431868) baseStart_431868 baseEnd_431868 := by
    simpa [prefixWord, tailWord_431868, baseEnd_431868] using wordTrace_append hprefix tailTrace_431868
  have hstable : (prefixWord ++ tailWord_431868).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431868).length < 2 ^ (prefixWord ++ tailWord_431868).sum := by decide
  have hdescent : baseEnd_431868 < baseStart_431868 := by decide
  rcases family_descends (prefixWord ++ tailWord_431868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431959 : List Nat := [1, 1, 3, 2, 6, 1, 1, 4]
def baseStart_431959 : Nat := 118140960795 + 431959 * 2 ^ 59
def prefixEnd_431959 : Nat := 4983230072969 + 3 ^ 40 * 431959 * 2
def baseEnd_431959 : Nat := 131438571872936706445015

theorem tailTrace_431959 : CollatzResearch.WordTrace tailWord_431959 prefixEnd_431959 131438571872936706445015 := by
  unfold tailWord_431959
  simp only [CollatzResearch.WordTrace]
  refine ⟨15754839042093790568962931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10503226028062527045975287 15754839042093790568962931)
  ·
    refine ⟨23632258563140685853444397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15754839042093790568962931 23632258563140685853444397)
    ·
      refine ⟨8862096961177757195041649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23632258563140685853444397 8862096961177757195041649)
      ·
        refine ⟨6646572720883317896281237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8862096961177757195041649 6646572720883317896281237)
        ·
          refine ⟨311558096291405526388183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6646572720883317896281237 311558096291405526388183)
          ·
            refine ⟨467337144437108289582275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311558096291405526388183 467337144437108289582275)
            ·
              refine ⟨701005716655662434373413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467337144437108289582275 701005716655662434373413)
              ·
                refine ⟨131438571872936706445015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 701005716655662434373413 131438571872936706445015)
                ·
                  rfl

theorem cell19_431959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 4].length) (baseStart_431959 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431959 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431959 prefixEnd_431959 := by exact prefixLift 431959
  have htrace : WordTrace (prefixWord ++ tailWord_431959) baseStart_431959 baseEnd_431959 := by
    simpa [prefixWord, tailWord_431959, baseEnd_431959] using wordTrace_append hprefix tailTrace_431959
  have hstable : (prefixWord ++ tailWord_431959).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431959).length < 2 ^ (prefixWord ++ tailWord_431959).sum := by decide
  have hdescent : baseEnd_431959 < baseStart_431959 := by decide
  rcases family_descends (prefixWord ++ tailWord_431959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_431980 : List Nat := [2, 2, 1, 1, 4, 3, 3, 3]
def baseStart_431980 : Nat := 118140960795 + 431980 * 2 ^ 59
def prefixEnd_431980 : Nat := 4983230072969 + 3 ^ 40 * 431980 * 2
def baseEnd_431980 : Nat := 131444961854414879978291

theorem tailTrace_431980 : CollatzResearch.WordTrace tailWord_431980 prefixEnd_431980 131444961854414879978291 := by
  unfold tailWord_431980
  simp only [CollatzResearch.WordTrace]
  refine ⟨7877802487508855577738697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10503736650011807436984929 7877802487508855577738697)
  ·
    refine ⟨5908351865631641683304023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7877802487508855577738697 5908351865631641683304023)
    ·
      refine ⟨8862527798447462524956035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5908351865631641683304023 8862527798447462524956035)
      ·
        refine ⟨13293791697671193787434053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8862527798447462524956035 13293791697671193787434053)
        ·
          refine ⟨2492585943313348835143885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13293791697671193787434053 2492585943313348835143885)
          ·
            refine ⟨934719728742505813178957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2492585943313348835143885 934719728742505813178957)
            ·
              refine ⟨350519898278439679942109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 934719728742505813178957 350519898278439679942109)
              ·
                refine ⟨131444961854414879978291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 350519898278439679942109 131444961854414879978291)
                ·
                  rfl

theorem cell19_431980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_431980 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_431980 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_431980 prefixEnd_431980 := by exact prefixLift 431980
  have htrace : WordTrace (prefixWord ++ tailWord_431980) baseStart_431980 baseEnd_431980 := by
    simpa [prefixWord, tailWord_431980, baseEnd_431980] using wordTrace_append hprefix tailTrace_431980
  have hstable : (prefixWord ++ tailWord_431980).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_431980).length < 2 ^ (prefixWord ++ tailWord_431980).sum := by decide
  have hdescent : baseEnd_431980 < baseStart_431980 := by decide
  rcases family_descends (prefixWord ++ tailWord_431980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432033 : List Nat := [1, 2, 3, 4, 3, 1, 2, 3]
def baseStart_432033 : Nat := 118140960795 + 432033 * 2 ^ 59
def prefixEnd_432033 : Nat := 4983230072969 + 3 ^ 40 * 432033 * 2
def baseEnd_432033 : Nat := 131461088950526460800369

theorem tailTrace_432033 : CollatzResearch.WordTrace tailWord_432033 prefixEnd_432033 131461088950526460800369 := by
  unfold tailWord_432033
  simp only [CollatzResearch.WordTrace]
  refine ⟨15757538043825701207156753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10505025362550467471437835 15757538043825701207156753)
  ·
    refine ⟨11818153532869275905367565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15757538043825701207156753 11818153532869275905367565)
    ·
      refine ⟨4431807574825978464512837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11818153532869275905367565 4431807574825978464512837)
      ·
        refine ⟨830963920279870962096157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4431807574825978464512837 830963920279870962096157)
        ·
          refine ⟨311611470104951610786059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 830963920279870962096157 311611470104951610786059)
          ·
            refine ⟨467417205157427416179089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311611470104951610786059 467417205157427416179089)
            ·
              refine ⟨350562903868070562134317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467417205157427416179089 350562903868070562134317)
              ·
                refine ⟨131461088950526460800369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 350562903868070562134317 131461088950526460800369)
                ·
                  rfl

theorem cell19_432033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 3].length) (baseStart_432033 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_432033 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_432033 prefixEnd_432033 := by exact prefixLift 432033
  have htrace : WordTrace (prefixWord ++ tailWord_432033) baseStart_432033 baseEnd_432033 := by
    simpa [prefixWord, tailWord_432033, baseEnd_432033] using wordTrace_append hprefix tailTrace_432033
  have hstable : (prefixWord ++ tailWord_432033).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432033).length < 2 ^ (prefixWord ++ tailWord_432033).sum := by decide
  have hdescent : baseEnd_432033 < baseStart_432033 := by decide
  rcases family_descends (prefixWord ++ tailWord_432033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432052 : List Nat := [2, 5, 2, 1, 3, 1, 5]
def baseStart_432052 : Nat := 118140960795 + 432052 * 2 ^ 59
def prefixEnd_432052 : Nat := 4983230072969 + 3 ^ 40 * 432052 * 2
def baseEnd_432052 : Nat := 43822290120780015459365

theorem tailTrace_432052 : CollatzResearch.WordTrace tailWord_432052 prefixEnd_432052 43822290120780015459365 := by
  unfold tailWord_432052
  simp only [CollatzResearch.WordTrace]
  refine ⟨7879115515378433726049205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10505487353837911634732273 7879115515378433726049205)
  ·
    refine ⟨738667079566728161817113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7879115515378433726049205 738667079566728161817113)
    ·
      refine ⟨554000309675046121362835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 738667079566728161817113 554000309675046121362835)
      ·
        refine ⟨831000464512569182044253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554000309675046121362835 831000464512569182044253)
        ·
          refine ⟨311625174192213443266595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 831000464512569182044253 311625174192213443266595)
          ·
            refine ⟨467437761288320164899893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311625174192213443266595 467437761288320164899893)
            ·
              refine ⟨43822290120780015459365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 467437761288320164899893 43822290120780015459365)
              ·
                rfl

theorem cell19_432052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 5].length) (baseStart_432052 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_432052 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_432052 prefixEnd_432052 := by exact prefixLift 432052
  have htrace : WordTrace (prefixWord ++ tailWord_432052) baseStart_432052 baseEnd_432052 := by
    simpa [prefixWord, tailWord_432052, baseEnd_432052] using wordTrace_append hprefix tailTrace_432052
  have hstable : (prefixWord ++ tailWord_432052).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432052).length < 2 ^ (prefixWord ++ tailWord_432052).sum := by decide
  have hdescent : baseEnd_432052 < baseStart_432052 := by decide
  rcases family_descends (prefixWord ++ tailWord_432052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432229 : List Nat := [1, 3, 1, 3, 2, 4, 5]
def baseStart_432229 : Nat := 118140960795 + 432229 * 2 ^ 59
def prefixEnd_432229 : Nat := 4983230072969 + 3 ^ 40 * 432229 * 2
def baseEnd_432229 : Nat := 43840242925885360148093

theorem tailTrace_432229 : CollatzResearch.WordTrace tailWord_432229 prefixEnd_432229 43840242925885360148093 := by
  unfold tailWord_432229
  simp only [CollatzResearch.WordTrace]
  refine ⟨15764686751115626681291741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10509791167410417787527827 15764686751115626681291741)
  ·
    refine ⟨5911757531668360005484403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15764686751115626681291741 5911757531668360005484403)
    ·
      refine ⟨8867636297502540008226605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5911757531668360005484403 8867636297502540008226605)
      ·
        refine ⟨3325363611563452503084977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8867636297502540008226605 3325363611563452503084977)
        ·
          refine ⟨2494022708672589377313733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3325363611563452503084977 2494022708672589377313733)
          ·
            refine ⟨467629257876110508246325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2494022708672589377313733 467629257876110508246325)
            ·
              refine ⟨43840242925885360148093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 467629257876110508246325 43840242925885360148093)
              ·
                rfl

theorem cell19_432229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 5].length) (baseStart_432229 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_432229 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_432229 prefixEnd_432229 := by exact prefixLift 432229
  have htrace : WordTrace (prefixWord ++ tailWord_432229) baseStart_432229 baseEnd_432229 := by
    simpa [prefixWord, tailWord_432229, baseEnd_432229] using wordTrace_append hprefix tailTrace_432229
  have hstable : (prefixWord ++ tailWord_432229).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432229).length < 2 ^ (prefixWord ++ tailWord_432229).sum := by decide
  have hdescent : baseEnd_432229 < baseStart_432229 := by decide
  rcases family_descends (prefixWord ++ tailWord_432229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432246 : List Nat := [5, 1, 1, 2, 1, 3, 2, 4]
def baseStart_432246 : Nat := 118140960795 + 432246 * 2 ^ 59
def prefixEnd_432246 : Nat := 4983230072969 + 3 ^ 40 * 432246 * 2
def baseEnd_432246 : Nat := 131525901619805078066455

theorem tailTrace_432246 : CollatzResearch.WordTrace tailWord_432246 prefixEnd_432246 131525901619805078066455 := by
  unfold tailWord_432246
  simp only [CollatzResearch.WordTrace]
  refine ⟨985331674503377411541287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10510204528036025723107061 985331674503377411541287)
  ·
    refine ⟨1477997511755066117311931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 985331674503377411541287 1477997511755066117311931)
    ·
      refine ⟨2216996267632599175967897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1477997511755066117311931 2216996267632599175967897)
      ·
        refine ⟨1662747200724449381975923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2216996267632599175967897 1662747200724449381975923)
        ·
          refine ⟨2494120801086674072963885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1662747200724449381975923 2494120801086674072963885)
          ·
            refine ⟨935295300407502777361457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2494120801086674072963885 935295300407502777361457)
            ·
              refine ⟨701471475305627083021093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 935295300407502777361457 701471475305627083021093)
              ·
                refine ⟨131525901619805078066455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 701471475305627083021093 131525901619805078066455)
                ·
                  rfl

theorem cell19_432246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_432246 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_432246 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_432246 prefixEnd_432246 := by exact prefixLift 432246
  have htrace : WordTrace (prefixWord ++ tailWord_432246) baseStart_432246 baseEnd_432246 := by
    simpa [prefixWord, tailWord_432246, baseEnd_432246] using wordTrace_append hprefix tailTrace_432246
  have hstable : (prefixWord ++ tailWord_432246).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432246).length < 2 ^ (prefixWord ++ tailWord_432246).sum := by decide
  have hdescent : baseEnd_432246 < baseStart_432246 := by decide
  rcases family_descends (prefixWord ++ tailWord_432246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432278 : List Nat := [5, 3, 2, 1, 2, 6]
def baseStart_432278 : Nat := 118140960795 + 432278 * 2 ^ 59
def prefixEnd_432278 : Nat := 4983230072969 + 3 ^ 40 * 432278 * 2
def baseEnd_432278 : Nat := 14615070970493165039473

theorem tailTrace_432278 : CollatzResearch.WordTrace tailWord_432278 prefixEnd_432278 14615070970493165039473 := by
  unfold tailWord_432278
  simp only [CollatzResearch.WordTrace]
  refine ⟨985404620496131753114093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10510982618625405366550325 985404620496131753114093)
  ·
    refine ⟨369526732686049407417785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 985404620496131753114093 369526732686049407417785)
    ·
      refine ⟨277145049514537055563339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 369526732686049407417785 277145049514537055563339)
      ·
        refine ⟨415717574271805583345009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277145049514537055563339 415717574271805583345009)
        ·
          refine ⟨311788180703854187508757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415717574271805583345009 311788180703854187508757)
          ·
            refine ⟨14615070970493165039473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 311788180703854187508757 14615070970493165039473)
            ·
              rfl

theorem cell19_432278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 6].length) (baseStart_432278 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_432278 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_432278 prefixEnd_432278 := by exact prefixLift 432278
  have htrace : WordTrace (prefixWord ++ tailWord_432278) baseStart_432278 baseEnd_432278 := by
    simpa [prefixWord, tailWord_432278, baseEnd_432278] using wordTrace_append hprefix tailTrace_432278
  have hstable : (prefixWord ++ tailWord_432278).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432278).length < 2 ^ (prefixWord ++ tailWord_432278).sum := by decide
  have hdescent : baseEnd_432278 < baseStart_432278 := by decide
  rcases family_descends (prefixWord ++ tailWord_432278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432286 : List Nat := [4, 3, 1, 1, 10]
def baseStart_432286 : Nat := 118140960795 + 432286 * 2 ^ 59
def prefixEnd_432286 : Nat := 4983230072969 + 3 ^ 40 * 432286 * 2
def baseEnd_432286 : Nat := 4871780481966549525091

theorem tailTrace_432286 : CollatzResearch.WordTrace tailWord_432286 prefixEnd_432286 4871780481966549525091 := by
  unfold tailWord_432286
  simp only [CollatzResearch.WordTrace]
  refine ⟨1970845713988640677014589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10511177141272750277411141 1970845713988640677014589)
  ·
    refine ⟨739067142745740253880471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1970845713988640677014589 739067142745740253880471)
    ·
      refine ⟨1108600714118610380820707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 739067142745740253880471 1108600714118610380820707)
      ·
        refine ⟨1662901071177915571231061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1108600714118610380820707 1662901071177915571231061)
        ·
          refine ⟨4871780481966549525091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1662901071177915571231061 4871780481966549525091)
          ·
            rfl

theorem cell19_432286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 10].length) (baseStart_432286 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_432286 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_432286 prefixEnd_432286 := by exact prefixLift 432286
  have htrace : WordTrace (prefixWord ++ tailWord_432286) baseStart_432286 baseEnd_432286 := by
    simpa [prefixWord, tailWord_432286, baseEnd_432286] using wordTrace_append hprefix tailTrace_432286
  have hstable : (prefixWord ++ tailWord_432286).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432286).length < 2 ^ (prefixWord ++ tailWord_432286).sum := by decide
  have hdescent : baseEnd_432286 < baseStart_432286 := by decide
  rcases family_descends (prefixWord ++ tailWord_432286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432288 : List Nat := [2, 1, 1, 4, 2, 9]
def baseStart_432288 : Nat := 118140960795 + 432288 * 2 ^ 59
def prefixEnd_432288 : Nat := 4983230072969 + 3 ^ 40 * 432288 * 2
def baseEnd_432288 : Nat := 14615409064751269459223

theorem tailTrace_432288 : CollatzResearch.WordTrace tailWord_432288 prefixEnd_432288 14615409064751269459223 := by
  unfold tailWord_432288
  simp only [CollatzResearch.WordTrace]
  refine ⟨7883419328950939878844759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10511225771934586505126345 7883419328950939878844759)
  ·
    refine ⟨11825128993426409818267139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7883419328950939878844759 11825128993426409818267139)
    ·
      refine ⟨17737693490139614727400709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11825128993426409818267139 17737693490139614727400709)
      ·
        refine ⟨3325817529401177761387633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17737693490139614727400709 3325817529401177761387633)
        ·
          refine ⟨2494363147050883321040725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3325817529401177761387633 2494363147050883321040725)
          ·
            refine ⟨14615409064751269459223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2494363147050883321040725 14615409064751269459223)
            ·
              rfl

theorem cell19_432288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 9].length) (baseStart_432288 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_432288 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_432288 prefixEnd_432288 := by exact prefixLift 432288
  have htrace : WordTrace (prefixWord ++ tailWord_432288) baseStart_432288 baseEnd_432288 := by
    simpa [prefixWord, tailWord_432288, baseEnd_432288] using wordTrace_append hprefix tailTrace_432288
  have hstable : (prefixWord ++ tailWord_432288).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432288).length < 2 ^ (prefixWord ++ tailWord_432288).sum := by decide
  have hdescent : baseEnd_432288 < baseStart_432288 := by decide
  rcases family_descends (prefixWord ++ tailWord_432288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432364 : List Nat := [2, 2, 1, 1, 2, 3, 2, 6]
def baseStart_432364 : Nat := 118140960795 + 432364 * 2 ^ 59
def prefixEnd_432364 : Nat := 4983230072969 + 3 ^ 40 * 432364 * 2
def baseEnd_432364 : Nat := 131561807230015767443911

theorem tailTrace_432364 : CollatzResearch.WordTrace tailWord_432364 prefixEnd_432364 131561807230015767443911 := by
  unfold tailWord_432364
  simp only [CollatzResearch.WordTrace]
  refine ⟨7884805302813272368728073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10513073737084363158304097 7884805302813272368728073)
  ·
    refine ⟨5913603977109954276546055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7884805302813272368728073 5913603977109954276546055)
    ·
      refine ⟨8870405965664931414819083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5913603977109954276546055 8870405965664931414819083)
      ·
        refine ⟨13305608948497397122228625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8870405965664931414819083 13305608948497397122228625)
        ·
          refine ⟨9979206711373047841671469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13305608948497397122228625 9979206711373047841671469)
          ·
            refine ⟨3742202516764892940626801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9979206711373047841671469 3742202516764892940626801)
            ·
              refine ⟨2806651887573669705470101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3742202516764892940626801 2806651887573669705470101)
              ·
                refine ⟨131561807230015767443911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2806651887573669705470101 131561807230015767443911)
                ·
                  rfl

theorem cell19_432364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_432364 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_432364 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_432364 prefixEnd_432364 := by exact prefixLift 432364
  have htrace : WordTrace (prefixWord ++ tailWord_432364) baseStart_432364 baseEnd_432364 := by
    simpa [prefixWord, tailWord_432364, baseEnd_432364] using wordTrace_append hprefix tailTrace_432364
  have hstable : (prefixWord ++ tailWord_432364).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432364).length < 2 ^ (prefixWord ++ tailWord_432364).sum := by decide
  have hdescent : baseEnd_432364 < baseStart_432364 := by decide
  rcases family_descends (prefixWord ++ tailWord_432364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432383 : List Nat := [1, 1, 2, 2, 1, 4, 3, 5]
def baseStart_432383 : Nat := 118140960795 + 432383 * 2 ^ 59
def prefixEnd_432383 : Nat := 4983230072969 + 3 ^ 40 * 432383 * 2
def baseEnd_432383 : Nat := 131567588641829353021637

theorem tailTrace_432383 : CollatzResearch.WordTrace tailWord_432383 prefixEnd_432383 131567588641829353021637 := by
  unfold tailWord_432383
  simp only [CollatzResearch.WordTrace]
  refine ⟨15770303592557710982397803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10513535728371807321598535 15770303592557710982397803)
  ·
    refine ⟨23655455388836566473596705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15770303592557710982397803 23655455388836566473596705)
    ·
      refine ⟨17741591541627424855197529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23655455388836566473596705 17741591541627424855197529)
      ·
        refine ⟨13306193656220568641398147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17741591541627424855197529 13306193656220568641398147)
        ·
          refine ⟨19959290484330852962097221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13306193656220568641398147 19959290484330852962097221)
          ·
            refine ⟨3742366965812034930393229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19959290484330852962097221 3742366965812034930393229)
            ·
              refine ⟨1403387612179513098897461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3742366965812034930393229 1403387612179513098897461)
              ·
                refine ⟨131567588641829353021637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1403387612179513098897461 131567588641829353021637)
                ·
                  rfl

theorem cell19_432383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_432383 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_432383 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_432383 prefixEnd_432383 := by exact prefixLift 432383
  have htrace : WordTrace (prefixWord ++ tailWord_432383) baseStart_432383 baseEnd_432383 := by
    simpa [prefixWord, tailWord_432383, baseEnd_432383] using wordTrace_append hprefix tailTrace_432383
  have hstable : (prefixWord ++ tailWord_432383).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432383).length < 2 ^ (prefixWord ++ tailWord_432383).sum := by decide
  have hdescent : baseEnd_432383 < baseStart_432383 := by decide
  rcases family_descends (prefixWord ++ tailWord_432383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432440 : List Nat := [2, 1, 2, 1, 3, 1, 4, 5]
def baseStart_432440 : Nat := 118140960795 + 432440 * 2 ^ 59
def prefixEnd_432440 : Nat := 4983230072969 + 3 ^ 40 * 432440 * 2
def baseEnd_432440 : Nat := 131584932877270109754815

theorem tailTrace_432440 : CollatzResearch.WordTrace tailWord_432440 prefixEnd_432440 131584932877270109754815 := by
  unfold tailWord_432440
  simp only [CollatzResearch.WordTrace]
  refine ⟨7886191276675604858611387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10514921702234139811481849 7886191276675604858611387)
  ·
    refine ⟨11829286915013407287917081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7886191276675604858611387 11829286915013407287917081)
    ·
      refine ⟨8871965186260055465937811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11829286915013407287917081 8871965186260055465937811)
      ·
        refine ⟨13307947779390083198906717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8871965186260055465937811 13307947779390083198906717)
        ·
          refine ⟨4990480417271281199590019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13307947779390083198906717 4990480417271281199590019)
          ·
            refine ⟨7485720625906921799385029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4990480417271281199590019 7485720625906921799385029)
            ·
              refine ⟨1403572617357547837384693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7485720625906921799385029 1403572617357547837384693)
              ·
                refine ⟨131584932877270109754815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1403572617357547837384693 131584932877270109754815)
                ·
                  rfl

theorem cell19_432440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_432440 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_432440 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_432440 prefixEnd_432440 := by exact prefixLift 432440
  have htrace : WordTrace (prefixWord ++ tailWord_432440) baseStart_432440 baseEnd_432440 := by
    simpa [prefixWord, tailWord_432440, baseEnd_432440] using wordTrace_append hprefix tailTrace_432440
  have hstable : (prefixWord ++ tailWord_432440).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432440).length < 2 ^ (prefixWord ++ tailWord_432440).sum := by decide
  have hdescent : baseEnd_432440 < baseStart_432440 := by decide
  rcases family_descends (prefixWord ++ tailWord_432440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432516 : List Nat := [2, 3, 2, 1, 1, 2, 8]
def baseStart_432516 : Nat := 118140960795 + 432516 * 2 ^ 59
def prefixEnd_432516 : Nat := 4983230072969 + 3 ^ 40 * 432516 * 2
def baseEnd_432516 : Nat := 43869352841508150688573

theorem tailTrace_432516 : CollatzResearch.WordTrace tailWord_432516 prefixEnd_432516 43869352841508150688573 := by
  unfold tailWord_432516
  simp only [CollatzResearch.WordTrace]
  refine ⟨7887577250537937348494701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10516769667383916464659601 7887577250537937348494701)
  ·
    refine ⟨2957841468951726505685513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7887577250537937348494701 2957841468951726505685513)
    ·
      refine ⟨2218381101713794879264135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2957841468951726505685513 2218381101713794879264135)
      ·
        refine ⟨3327571652570692318896203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2218381101713794879264135 3327571652570692318896203)
        ·
          refine ⟨4991357478856038478344305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3327571652570692318896203 4991357478856038478344305)
          ·
            refine ⟨3743518109142028858758229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4991357478856038478344305 3743518109142028858758229)
            ·
              refine ⟨43869352841508150688573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3743518109142028858758229 43869352841508150688573)
              ·
                rfl

theorem cell19_432516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 8].length) (baseStart_432516 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_432516 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_432516 prefixEnd_432516 := by exact prefixLift 432516
  have htrace : WordTrace (prefixWord ++ tailWord_432516) baseStart_432516 baseEnd_432516 := by
    simpa [prefixWord, tailWord_432516, baseEnd_432516] using wordTrace_append hprefix tailTrace_432516
  have hstable : (prefixWord ++ tailWord_432516).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432516).length < 2 ^ (prefixWord ++ tailWord_432516).sum := by decide
  have hdescent : baseEnd_432516 < baseStart_432516 := by decide
  rcases family_descends (prefixWord ++ tailWord_432516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432573 : List Nat := [1, 4, 1, 2, 2, 2, 7]
def baseStart_432573 : Nat := 118140960795 + 432573 * 2 ^ 59
def prefixEnd_432573 : Nat := 4983230072969 + 3 ^ 40 * 432573 * 2
def baseEnd_432573 : Nat := 43875134253321736266299

theorem tailTrace_432573 : CollatzResearch.WordTrace tailWord_432573 prefixEnd_432573 43875134253321736266299 := by
  unfold tailWord_432573
  simp only [CollatzResearch.WordTrace]
  refine ⟨15777233461869373431814373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10518155641246248954542915 15777233461869373431814373)
  ·
    refine ⟨2958231274100507518465195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15777233461869373431814373 2958231274100507518465195)
    ·
      refine ⟨4437346911150761277697793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2958231274100507518465195 4437346911150761277697793)
      ·
        refine ⟨3328010183363070958273345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4437346911150761277697793 3328010183363070958273345)
        ·
          refine ⟨2496007637522303218705009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3328010183363070958273345 2496007637522303218705009)
          ·
            refine ⟨1872005728141727414028757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2496007637522303218705009 1872005728141727414028757)
            ·
              refine ⟨43875134253321736266299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1872005728141727414028757 43875134253321736266299)
              ·
                rfl

theorem cell19_432573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 7].length) (baseStart_432573 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_432573 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_432573 prefixEnd_432573 := by exact prefixLift 432573
  have htrace : WordTrace (prefixWord ++ tailWord_432573) baseStart_432573 baseEnd_432573 := by
    simpa [prefixWord, tailWord_432573, baseEnd_432573] using wordTrace_append hprefix tailTrace_432573
  have hstable : (prefixWord ++ tailWord_432573).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432573).length < 2 ^ (prefixWord ++ tailWord_432573).sum := by decide
  have hdescent : baseEnd_432573 < baseStart_432573 := by decide
  rcases family_descends (prefixWord ++ tailWord_432573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432738 : List Nat := [3, 3, 2, 3, 2, 1, 5]
def baseStart_432738 : Nat := 118140960795 + 432738 * 2 ^ 59
def prefixEnd_432738 : Nat := 4983230072969 + 3 ^ 40 * 432738 * 2
def baseEnd_432738 : Nat := 43891869919097905043927

theorem tailTrace_432738 : CollatzResearch.WordTrace tailWord_432738 prefixEnd_432738 43891869919097905043927 := by
  unfold tailWord_432738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3945812876567901652892717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10522167670847737741047245 3945812876567901652892717)
  ·
    refine ⟨1479679828712963119834769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3945812876567901652892717 1479679828712963119834769)
    ·
      refine ⟨1109759871534722339876077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1479679828712963119834769 1109759871534722339876077)
      ·
        refine ⟨416159951825520877453529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1109759871534722339876077 416159951825520877453529)
        ·
          refine ⟨312119963869140658090147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416159951825520877453529 312119963869140658090147)
          ·
            refine ⟨468179945803710987135221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312119963869140658090147 468179945803710987135221)
            ·
              refine ⟨43891869919097905043927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 468179945803710987135221 43891869919097905043927)
              ·
                rfl

theorem cell19_432738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 5].length) (baseStart_432738 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_432738 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_432738 prefixEnd_432738 := by exact prefixLift 432738
  have htrace : WordTrace (prefixWord ++ tailWord_432738) baseStart_432738 baseEnd_432738 := by
    simpa [prefixWord, tailWord_432738, baseEnd_432738] using wordTrace_append hprefix tailTrace_432738
  have hstable : (prefixWord ++ tailWord_432738).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432738).length < 2 ^ (prefixWord ++ tailWord_432738).sum := by decide
  have hdescent : baseEnd_432738 < baseStart_432738 := by decide
  rcases family_descends (prefixWord ++ tailWord_432738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432782 : List Nat := [4, 1, 1, 3, 1, 1, 1, 7]
def baseStart_432782 : Nat := 118140960795 + 432782 * 2 ^ 59
def prefixEnd_432782 : Nat := 4983230072969 + 3 ^ 40 * 432782 * 2
def baseEnd_432782 : Nat := 131688998289914650153883

theorem tailTrace_432782 : CollatzResearch.WordTrace tailWord_432782 prefixEnd_432782 131688998289914650153883 := by
  unfold tailWord_432782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1973107039764025265771575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10523237545408134750781733 1973107039764025265771575)
  ·
    refine ⟨2959660559646037898657363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1973107039764025265771575 2959660559646037898657363)
    ·
      refine ⟨4439490839469056847986045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2959660559646037898657363 4439490839469056847986045)
      ·
        refine ⟨1664809064800896317994767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4439490839469056847986045 1664809064800896317994767)
        ·
          refine ⟨2497213597201344476992151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1664809064800896317994767 2497213597201344476992151)
          ·
            refine ⟨3745820395802016715488227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497213597201344476992151 3745820395802016715488227)
            ·
              refine ⟨5618730593703025073232341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3745820395802016715488227 5618730593703025073232341)
              ·
                refine ⟨131688998289914650153883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5618730593703025073232341 131688998289914650153883)
                ·
                  rfl

theorem cell19_432782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_432782 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_432782 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_432782 prefixEnd_432782 := by exact prefixLift 432782
  have htrace : WordTrace (prefixWord ++ tailWord_432782) baseStart_432782 baseEnd_432782 := by
    simpa [prefixWord, tailWord_432782, baseEnd_432782] using wordTrace_append hprefix tailTrace_432782
  have hstable : (prefixWord ++ tailWord_432782).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432782).length < 2 ^ (prefixWord ++ tailWord_432782).sum := by decide
  have hdescent : baseEnd_432782 < baseStart_432782 := by decide
  rcases family_descends (prefixWord ++ tailWord_432782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432801 : List Nat := [1, 2, 3, 3, 3, 7]
def baseStart_432801 : Nat := 118140960795 + 432801 * 2 ^ 59
def prefixEnd_432801 : Nat := 4983230072969 + 3 ^ 40 * 432801 * 2
def baseEnd_432801 : Nat := 14632753300192026192401

theorem tailTrace_432801 : CollatzResearch.WordTrace tailWord_432801 prefixEnd_432801 14632753300192026192401 := by
  unfold tailWord_432801
  simp only [CollatzResearch.WordTrace]
  refine ⟨15785549305043368371114257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10523699536695578914076171 15785549305043368371114257)
  ·
    refine ⟨11839161978782526278335693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15785549305043368371114257 11839161978782526278335693)
    ·
      refine ⟨4439685742043447354375885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11839161978782526278335693 4439685742043447354375885)
      ·
        refine ⟨1664882153266292757890957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4439685742043447354375885 1664882153266292757890957)
        ·
          refine ⟨624330807474859784209109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1664882153266292757890957 624330807474859784209109)
          ·
            refine ⟨14632753300192026192401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 624330807474859784209109 14632753300192026192401)
            ·
              rfl

theorem cell19_432801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 7].length) (baseStart_432801 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_432801 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_432801 prefixEnd_432801 := by exact prefixLift 432801
  have htrace : WordTrace (prefixWord ++ tailWord_432801) baseStart_432801 baseEnd_432801 := by
    simpa [prefixWord, tailWord_432801, baseEnd_432801] using wordTrace_append hprefix tailTrace_432801
  have hstable : (prefixWord ++ tailWord_432801).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432801).length < 2 ^ (prefixWord ++ tailWord_432801).sum := by decide
  have hdescent : baseEnd_432801 < baseStart_432801 := by decide
  rcases family_descends (prefixWord ++ tailWord_432801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432833 : List Nat := [1, 2, 6, 2, 1, 1, 3, 3]
def baseStart_432833 : Nat := 118140960795 + 432833 * 2 ^ 59
def prefixEnd_432833 : Nat := 4983230072969 + 3 ^ 40 * 432833 * 2
def baseEnd_432833 : Nat := 131704516816361643020411

theorem tailTrace_432833 : CollatzResearch.WordTrace tailWord_432833 prefixEnd_432833 131704516816361643020411 := by
  unfold tailWord_432833
  simp only [CollatzResearch.WordTrace]
  refine ⟨15786716440927437836279153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10524477627284958557519435 15786716440927437836279153)
  ·
    refine ⟨11840037330695578377209365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15786716440927437836279153 11840037330695578377209365)
    ·
      refine ⟨555001749876355236431689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11840037330695578377209365 555001749876355236431689)
      ·
        refine ⟨416251312407266427323767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 555001749876355236431689 416251312407266427323767)
        ·
          refine ⟨624376968610899640985651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416251312407266427323767 624376968610899640985651)
          ·
            refine ⟨936565452916349461478477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624376968610899640985651 936565452916349461478477)
            ·
              refine ⟨351212044843631048054429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 936565452916349461478477 351212044843631048054429)
              ·
                refine ⟨131704516816361643020411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351212044843631048054429 131704516816361643020411)
                ·
                  rfl

theorem cell19_432833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 3].length) (baseStart_432833 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_432833 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_432833 prefixEnd_432833 := by exact prefixLift 432833
  have htrace : WordTrace (prefixWord ++ tailWord_432833) baseStart_432833 baseEnd_432833 := by
    simpa [prefixWord, tailWord_432833, baseEnd_432833] using wordTrace_append hprefix tailTrace_432833
  have hstable : (prefixWord ++ tailWord_432833).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432833).length < 2 ^ (prefixWord ++ tailWord_432833).sum := by decide
  have hdescent : baseEnd_432833 < baseStart_432833 := by decide
  rcases family_descends (prefixWord ++ tailWord_432833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432877 : List Nat := [1, 5, 1, 2, 1, 1, 2, 6]
def baseStart_432877 : Nat := 118140960795 + 432877 * 2 ^ 59
def prefixEnd_432877 : Nat := 4983230072969 + 3 ^ 40 * 432877 * 2
def baseEnd_432877 : Nat := 131717905348982578042513

theorem tailTrace_432877 : CollatzResearch.WordTrace tailWord_432877 prefixEnd_432877 131717905348982578042513 := by
  unfold tailWord_432877
  simp only [CollatzResearch.WordTrace]
  refine ⟨15788321252768033350880885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10525547501845355567253923 15788321252768033350880885)
  ·
    refine ⟨1480155117447003126645083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15788321252768033350880885 1480155117447003126645083)
    ·
      refine ⟨2220232676170504689967625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1480155117447003126645083 2220232676170504689967625)
      ·
        refine ⟨1665174507127878517475719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2220232676170504689967625 1665174507127878517475719)
        ·
          refine ⟨2497761760691817776213579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1665174507127878517475719 2497761760691817776213579)
          ·
            refine ⟨3746642641037726664320369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497761760691817776213579 3746642641037726664320369)
            ·
              refine ⟨2809981980778294998240277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3746642641037726664320369 2809981980778294998240277)
              ·
                refine ⟨131717905348982578042513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2809981980778294998240277 131717905348982578042513)
                ·
                  rfl

theorem cell19_432877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_432877 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_432877 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_432877 prefixEnd_432877 := by exact prefixLift 432877
  have htrace : WordTrace (prefixWord ++ tailWord_432877) baseStart_432877 baseEnd_432877 := by
    simpa [prefixWord, tailWord_432877, baseEnd_432877] using wordTrace_append hprefix tailTrace_432877
  have hstable : (prefixWord ++ tailWord_432877).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432877).length < 2 ^ (prefixWord ++ tailWord_432877).sum := by decide
  have hdescent : baseEnd_432877 < baseStart_432877 := by decide
  rcases family_descends (prefixWord ++ tailWord_432877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432894 : List Nat := [4, 2, 2, 1, 2, 2, 1, 5]
def baseStart_432894 : Nat := 118140960795 + 432894 * 2 ^ 59
def prefixEnd_432894 : Nat := 4983230072969 + 3 ^ 40 * 432894 * 2
def baseEnd_432894 : Nat := 131723078191131575664689

theorem tailTrace_432894 : CollatzResearch.WordTrace tailWord_432894 prefixEnd_432894 131723078191131575664689 := by
  unfold tailWord_432894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1973617661713305656781217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10525960862470963502833157 1973617661713305656781217)
  ·
    refine ⟨1480213246284979242585913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1973617661713305656781217 1480213246284979242585913)
    ·
      refine ⟨1110159934713734431939435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1480213246284979242585913 1110159934713734431939435)
      ·
        refine ⟨1665239902070601647909153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1110159934713734431939435 1665239902070601647909153)
        ·
          refine ⟨1248929926552951235931865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1665239902070601647909153 1248929926552951235931865)
          ·
            refine ⟨936697444914713426948899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1248929926552951235931865 936697444914713426948899)
            ·
              refine ⟨1405046167372070140423349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936697444914713426948899 1405046167372070140423349)
              ·
                refine ⟨131723078191131575664689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1405046167372070140423349 131723078191131575664689)
                ·
                  rfl

theorem cell19_432894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_432894 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_432894 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_432894 prefixEnd_432894 := by exact prefixLift 432894
  have htrace : WordTrace (prefixWord ++ tailWord_432894) baseStart_432894 baseEnd_432894 := by
    simpa [prefixWord, tailWord_432894, baseEnd_432894] using wordTrace_append hprefix tailTrace_432894
  have hstable : (prefixWord ++ tailWord_432894).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432894).length < 2 ^ (prefixWord ++ tailWord_432894).sum := by decide
  have hdescent : baseEnd_432894 < baseStart_432894 := by decide
  rcases family_descends (prefixWord ++ tailWord_432894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432932 : List Nat := [2, 3, 1, 3, 3, 1, 2, 4]
def baseStart_432932 : Nat := 118140960795 + 432932 * 2 ^ 59
def prefixEnd_432932 : Nat := 4983230072969 + 3 ^ 40 * 432932 * 2
def baseEnd_432932 : Nat := 131734641014758746820141

theorem tailTrace_432932 : CollatzResearch.WordTrace tailWord_432932 prefixEnd_432932 131734641014758746820141 := by
  unfold tailWord_432932
  simp only [CollatzResearch.WordTrace]
  refine ⟨7895163633784388872066525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10526884845045851829422033 7895163633784388872066525)
  ·
    refine ⟨2960686362669145827024947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7895163633784388872066525 2960686362669145827024947)
    ·
      refine ⟨4441029544003718740537421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2960686362669145827024947 4441029544003718740537421)
      ·
        refine ⟨1665386079001394527701533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4441029544003718740537421 1665386079001394527701533)
        ·
          refine ⟨624519779625522947888075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1665386079001394527701533 624519779625522947888075)
          ·
            refine ⟨936779669438284421832113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624519779625522947888075 936779669438284421832113)
            ·
              refine ⟨702584752078713316374085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 936779669438284421832113 702584752078713316374085)
              ·
                refine ⟨131734641014758746820141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 702584752078713316374085 131734641014758746820141)
                ·
                  rfl

theorem cell19_432932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_432932 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_432932 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_432932 prefixEnd_432932 := by exact prefixLift 432932
  have htrace : WordTrace (prefixWord ++ tailWord_432932) baseStart_432932 baseEnd_432932 := by
    simpa [prefixWord, tailWord_432932, baseEnd_432932] using wordTrace_append hprefix tailTrace_432932
  have hstable : (prefixWord ++ tailWord_432932).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432932).length < 2 ^ (prefixWord ++ tailWord_432932).sum := by decide
  have hdescent : baseEnd_432932 < baseStart_432932 := by decide
  rcases family_descends (prefixWord ++ tailWord_432932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_432993 : List Nat := [1, 2, 3, 1, 1, 1, 2, 8]
def baseStart_432993 : Nat := 118140960795 + 432993 * 2 ^ 59
def prefixEnd_432993 : Nat := 4983230072969 + 3 ^ 40 * 432993 * 2
def baseEnd_432993 : Nat := 131753202389528679464419

theorem tailTrace_432993 : CollatzResearch.WordTrace tailWord_432993 prefixEnd_432993 131753202389528679464419 := by
  unfold tailWord_432993
  simp only [CollatzResearch.WordTrace]
  refine ⟨15792552120347785162103633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10528368080231856774735755 15792552120347785162103633)
  ·
    refine ⟨11844414090260838871577725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15792552120347785162103633 11844414090260838871577725)
    ·
      refine ⟨4441655283847814576841647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11844414090260838871577725 4441655283847814576841647)
      ·
        refine ⟨6662482925771721865262471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4441655283847814576841647 6662482925771721865262471)
        ·
          refine ⟨9993724388657582797893707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6662482925771721865262471 9993724388657582797893707)
          ·
            refine ⟨14990586582986374196840561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9993724388657582797893707 14990586582986374196840561)
            ·
              refine ⟨11242939937239780647630421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14990586582986374196840561 11242939937239780647630421)
              ·
                refine ⟨131753202389528679464419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11242939937239780647630421 131753202389528679464419)
                ·
                  rfl

theorem cell19_432993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_432993 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_432993 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_432993 prefixEnd_432993 := by exact prefixLift 432993
  have htrace : WordTrace (prefixWord ++ tailWord_432993) baseStart_432993 baseEnd_432993 := by
    simpa [prefixWord, tailWord_432993, baseEnd_432993] using wordTrace_append hprefix tailTrace_432993
  have hstable : (prefixWord ++ tailWord_432993).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_432993).length < 2 ^ (prefixWord ++ tailWord_432993).sum := by decide
  have hdescent : baseEnd_432993 < baseStart_432993 := by decide
  rcases family_descends (prefixWord ++ tailWord_432993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433006 : List Nat := [4, 1, 2, 3, 2, 1, 3, 3]
def baseStart_433006 : Nat := 118140960795 + 433006 * 2 ^ 59
def prefixEnd_433006 : Nat := 4983230072969 + 3 ^ 40 * 433006 * 2
def baseEnd_433006 : Nat := 131757158092348501175495

theorem tailTrace_433006 : CollatzResearch.WordTrace tailWord_433006 prefixEnd_433006 131757158092348501175495 := by
  unfold tailWord_433006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1974128283662586047790859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10528684179533792254884581 1974128283662586047790859)
  ·
    refine ⟨2961192425493879071686289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1974128283662586047790859 2961192425493879071686289)
    ·
      refine ⟨2220894319120409303764717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2961192425493879071686289 2220894319120409303764717)
      ·
        refine ⟨832835369670153488911769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2220894319120409303764717 832835369670153488911769)
        ·
          refine ⟨624626527252615116683827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 832835369670153488911769 624626527252615116683827)
          ·
            refine ⟨936939790878922675025741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624626527252615116683827 936939790878922675025741)
            ·
              refine ⟨351352421579596003134653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 936939790878922675025741 351352421579596003134653)
              ·
                refine ⟨131757158092348501175495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351352421579596003134653 131757158092348501175495)
                ·
                  rfl

theorem cell19_433006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_433006 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433006 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433006 prefixEnd_433006 := by exact prefixLift 433006
  have htrace : WordTrace (prefixWord ++ tailWord_433006) baseStart_433006 baseEnd_433006 := by
    simpa [prefixWord, tailWord_433006, baseEnd_433006] using wordTrace_append hprefix tailTrace_433006
  have hstable : (prefixWord ++ tailWord_433006).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433006).length < 2 ^ (prefixWord ++ tailWord_433006).sum := by decide
  have hdescent : baseEnd_433006 < baseStart_433006 := by decide
  rcases family_descends (prefixWord ++ tailWord_433006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433063 : List Nat := [1, 1, 6, 1, 3, 2, 2, 3]
def baseStart_433063 : Nat := 118140960795 + 433063 * 2 ^ 59
def prefixEnd_433063 : Nat := 4983230072969 + 3 ^ 40 * 433063 * 2
def baseEnd_433063 : Nat := 131774502327789257908673

theorem tailTrace_433063 : CollatzResearch.WordTrace tailWord_433063 prefixEnd_433063 131774502327789257908673 := by
  unfold tailWord_433063
  simp only [CollatzResearch.WordTrace]
  refine ⟨15795105230094187117151843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10530070153396124744767895 15795105230094187117151843)
  ·
    refine ⟨23692657845141280675727765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15795105230094187117151843 23692657845141280675727765)
    ·
      refine ⟨1110593336490997531674739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23692657845141280675727765 1110593336490997531674739)
      ·
        refine ⟨1665890004736496297512109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1110593336490997531674739 1665890004736496297512109)
        ·
          refine ⟨624708751776186111567041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1665890004736496297512109 624708751776186111567041)
          ·
            refine ⟨468531563832139583675281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 624708751776186111567041 468531563832139583675281)
            ·
              refine ⟨351398672874104687756461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468531563832139583675281 351398672874104687756461)
              ·
                refine ⟨131774502327789257908673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351398672874104687756461 131774502327789257908673)
                ·
                  rfl

theorem cell19_433063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 3].length) (baseStart_433063 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433063 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433063 prefixEnd_433063 := by exact prefixLift 433063
  have htrace : WordTrace (prefixWord ++ tailWord_433063) baseStart_433063 baseEnd_433063 := by
    simpa [prefixWord, tailWord_433063, baseEnd_433063] using wordTrace_append hprefix tailTrace_433063
  have hstable : (prefixWord ++ tailWord_433063).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433063).length < 2 ^ (prefixWord ++ tailWord_433063).sum := by decide
  have hdescent : baseEnd_433063 < baseStart_433063 := by decide
  rcases family_descends (prefixWord ++ tailWord_433063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433078 : List Nat := [5, 1, 4, 1, 2, 1, 5]
def baseStart_433078 : Nat := 118140960795 + 433078 * 2 ^ 59
def prefixEnd_433078 : Nat := 4983230072969 + 3 ^ 40 * 433078 * 2
def baseEnd_433078 : Nat := 43926355533424555858433

theorem tailTrace_433078 : CollatzResearch.WordTrace tailWord_433078 prefixEnd_433078 43926355533424555858433 := by
  unfold tailWord_433078
  simp only [CollatzResearch.WordTrace]
  refine ⟨987228270314990292434243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10530434883359896452631925 987228270314990292434243)
  ·
    refine ⟨1480842405472485438651365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 987228270314990292434243 1480842405472485438651365)
    ·
      refine ⟨277657951026091019747131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1480842405472485438651365 277657951026091019747131)
      ·
        refine ⟨416486926539136529620697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277657951026091019747131 416486926539136529620697)
        ·
          refine ⟨312365194904352397215523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416486926539136529620697 312365194904352397215523)
          ·
            refine ⟨468547792356528595823285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312365194904352397215523 468547792356528595823285)
            ·
              refine ⟨43926355533424555858433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 468547792356528595823285 43926355533424555858433)
              ·
                rfl

theorem cell19_433078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 5].length) (baseStart_433078 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433078 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433078 prefixEnd_433078 := by exact prefixLift 433078
  have htrace : WordTrace (prefixWord ++ tailWord_433078) baseStart_433078 baseEnd_433078 := by
    simpa [prefixWord, tailWord_433078, baseEnd_433078] using wordTrace_append hprefix tailTrace_433078
  have hstable : (prefixWord ++ tailWord_433078).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433078).length < 2 ^ (prefixWord ++ tailWord_433078).sum := by decide
  have hdescent : baseEnd_433078 < baseStart_433078 := by decide
  rcases family_descends (prefixWord ++ tailWord_433078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433088 : List Nat := [2, 1, 1, 2, 3, 3, 7]
def baseStart_433088 : Nat := 118140960795 + 433088 * 2 ^ 59
def prefixEnd_433088 : Nat := 4983230072969 + 3 ^ 40 * 433088 * 2
def baseEnd_433088 : Nat := 43927369816198869117683

theorem tailTrace_433088 : CollatzResearch.WordTrace tailWord_433088 prefixEnd_433088 43927369816198869117683 := by
  unfold tailWord_433088
  simp only [CollatzResearch.WordTrace]
  refine ⟨7898008527501808193405959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10530678036669077591207945 7898008527501808193405959)
  ·
    refine ⟨11847012791252712290108939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7898008527501808193405959 11847012791252712290108939)
    ·
      refine ⟨17770519186879068435163409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11847012791252712290108939 17770519186879068435163409)
      ·
        refine ⟨13327889390159301326372557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17770519186879068435163409 13327889390159301326372557)
        ·
          refine ⟨4997958521309737997389709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13327889390159301326372557 4997958521309737997389709)
          ·
            refine ⟨1874234445491151749021141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4997958521309737997389709 1874234445491151749021141)
            ·
              refine ⟨43927369816198869117683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1874234445491151749021141 43927369816198869117683)
              ·
                rfl

theorem cell19_433088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 7].length) (baseStart_433088 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433088 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433088 prefixEnd_433088 := by exact prefixLift 433088
  have htrace : WordTrace (prefixWord ++ tailWord_433088) baseStart_433088 baseEnd_433088 := by
    simpa [prefixWord, tailWord_433088, baseEnd_433088] using wordTrace_append hprefix tailTrace_433088
  have hstable : (prefixWord ++ tailWord_433088).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433088).length < 2 ^ (prefixWord ++ tailWord_433088).sum := by decide
  have hdescent : baseEnd_433088 < baseStart_433088 := by decide
  rcases family_descends (prefixWord ++ tailWord_433088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433122 : List Nat := [3, 3, 3, 1, 1, 1, 2, 5]
def baseStart_433122 : Nat := 118140960795 + 433122 * 2 ^ 59
def prefixEnd_433122 : Nat := 4983230072969 + 3 ^ 40 * 433122 * 2
def baseEnd_433122 : Nat := 131792455132894602597401

theorem tailTrace_433122 : CollatzResearch.WordTrace tailWord_433122 prefixEnd_433122 131792455132894602597401 := by
  unfold tailWord_433122
  simp only [CollatzResearch.WordTrace]
  refine ⟨3949314284220110048387405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10531504757920293462366413 3949314284220110048387405)
  ·
    refine ⟨1480992856582541268145277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3949314284220110048387405 1480992856582541268145277)
    ·
      refine ⟨555372321218452975554479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1480992856582541268145277 555372321218452975554479)
      ·
        refine ⟨833058481827679463331719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555372321218452975554479 833058481827679463331719)
        ·
          refine ⟨1249587722741519194997579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833058481827679463331719 1249587722741519194997579)
          ·
            refine ⟨1874381584112278792496369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1249587722741519194997579 1874381584112278792496369)
            ·
              refine ⟨1405786188084209094372277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1874381584112278792496369 1405786188084209094372277)
              ·
                refine ⟨131792455132894602597401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1405786188084209094372277 131792455132894602597401)
                ·
                  rfl

theorem cell19_433122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_433122 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433122 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433122 prefixEnd_433122 := by exact prefixLift 433122
  have htrace : WordTrace (prefixWord ++ tailWord_433122) baseStart_433122 baseEnd_433122 := by
    simpa [prefixWord, tailWord_433122, baseEnd_433122] using wordTrace_append hprefix tailTrace_433122
  have hstable : (prefixWord ++ tailWord_433122).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433122).length < 2 ^ (prefixWord ++ tailWord_433122).sum := by decide
  have hdescent : baseEnd_433122 < baseStart_433122 := by decide
  rcases family_descends (prefixWord ++ tailWord_433122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433141 : List Nat := [1, 3, 5, 2, 1, 7]
def baseStart_433141 : Nat := 118140960795 + 433141 * 2 ^ 59
def prefixEnd_433141 : Nat := 4983230072969 + 3 ^ 40 * 433141 * 2
def baseEnd_433141 : Nat := 14644248504967576463903

theorem tailTrace_433141 : CollatzResearch.WordTrace tailWord_433141 prefixEnd_433141 14644248504967576463903 := by
  unfold tailWord_433141
  simp only [CollatzResearch.WordTrace]
  refine ⟨15797950123811606438491277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10531966749207737625660851 15797950123811606438491277)
  ·
    refine ⟨5924231296429352414434229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15797950123811606438491277 5924231296429352414434229)
    ·
      refine ⟨555396684040251788853209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5924231296429352414434229 555396684040251788853209)
      ·
        refine ⟨416547513030188841639907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 555396684040251788853209 416547513030188841639907)
        ·
          refine ⟨624821269545283262459861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416547513030188841639907 624821269545283262459861)
          ·
            refine ⟨14644248504967576463903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 624821269545283262459861 14644248504967576463903)
            ·
              rfl

theorem cell19_433141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 7].length) (baseStart_433141 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433141 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433141 prefixEnd_433141 := by exact prefixLift 433141
  have htrace : WordTrace (prefixWord ++ tailWord_433141) baseStart_433141 baseEnd_433141 := by
    simpa [prefixWord, tailWord_433141, baseEnd_433141] using wordTrace_append hprefix tailTrace_433141
  have hstable : (prefixWord ++ tailWord_433141).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433141).length < 2 ^ (prefixWord ++ tailWord_433141).sum := by decide
  have hdescent : baseEnd_433141 < baseStart_433141 := by decide
  rcases family_descends (prefixWord ++ tailWord_433141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433162 : List Nat := [3, 1, 2, 2, 3, 1, 3, 4]
def baseStart_433162 : Nat := 118140960795 + 433162 * 2 ^ 59
def prefixEnd_433162 : Nat := 4983230072969 + 3 ^ 40 * 433162 * 2
def baseEnd_433162 : Nat := 131804626526186361708403

theorem tailTrace_433162 : CollatzResearch.WordTrace tailWord_433162 prefixEnd_433162 131804626526186361708403 := by
  unfold tailWord_433162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3949679014183881756251435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10532477371157018016670493 3949679014183881756251435)
  ·
    refine ⟨5924518521275822634377153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3949679014183881756251435 5924518521275822634377153)
    ·
      refine ⟨4443388890956866975782865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5924518521275822634377153 4443388890956866975782865)
      ·
        refine ⟨3332541668217650231837149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4443388890956866975782865 3332541668217650231837149)
        ·
          refine ⟨1249703125581618836938931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3332541668217650231837149 1249703125581618836938931)
          ·
            refine ⟨1874554688372428255408397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1249703125581618836938931 1874554688372428255408397)
            ·
              refine ⟨702958008139660595778149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1874554688372428255408397 702958008139660595778149)
              ·
                refine ⟨131804626526186361708403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 702958008139660595778149 131804626526186361708403)
                ·
                  rfl

theorem cell19_433162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_433162 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433162 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433162 prefixEnd_433162 := by exact prefixLift 433162
  have htrace : WordTrace (prefixWord ++ tailWord_433162) baseStart_433162 baseEnd_433162 := by
    simpa [prefixWord, tailWord_433162, baseEnd_433162] using wordTrace_append hprefix tailTrace_433162
  have hstable : (prefixWord ++ tailWord_433162).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433162).length < 2 ^ (prefixWord ++ tailWord_433162).sum := by decide
  have hdescent : baseEnd_433162 < baseStart_433162 := by decide
  rcases family_descends (prefixWord ++ tailWord_433162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433202 : List Nat := [3, 2, 1, 1, 2, 2, 8]
def baseStart_433202 : Nat := 118140960795 + 433202 * 2 ^ 59
def prefixEnd_433202 : Nat := 4983230072969 + 3 ^ 40 * 433202 * 2
def baseEnd_433202 : Nat := 43938932639826040273135

theorem tailTrace_433202 : CollatzResearch.WordTrace tailWord_433202 prefixEnd_433202 43938932639826040273135 := by
  unfold tailWord_433202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3950043744147653464115465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10533449984393742570974573 3950043744147653464115465)
  ·
    refine ⟨2962532808110740098086599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3950043744147653464115465 2962532808110740098086599)
    ·
      refine ⟨4443799212166110147129899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2962532808110740098086599 4443799212166110147129899)
      ·
        refine ⟨6665698818249165220694849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4443799212166110147129899 6665698818249165220694849)
        ·
          refine ⟨4999274113686873915521137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6665698818249165220694849 4999274113686873915521137)
          ·
            refine ⟨3749455585265155436640853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4999274113686873915521137 3749455585265155436640853)
            ·
              refine ⟨43938932639826040273135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3749455585265155436640853 43938932639826040273135)
              ·
                rfl

theorem cell19_433202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 8].length) (baseStart_433202 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433202 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433202 prefixEnd_433202 := by exact prefixLift 433202
  have htrace : WordTrace (prefixWord ++ tailWord_433202) baseStart_433202 baseEnd_433202 := by
    simpa [prefixWord, tailWord_433202, baseEnd_433202] using wordTrace_append hprefix tailTrace_433202
  have hstable : (prefixWord ++ tailWord_433202).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433202).length < 2 ^ (prefixWord ++ tailWord_433202).sum := by decide
  have hdescent : baseEnd_433202 < baseStart_433202 := by decide
  rcases family_descends (prefixWord ++ tailWord_433202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433240 : List Nat := [2, 1, 2, 2, 1, 3, 3, 5]
def baseStart_433240 : Nat := 118140960795 + 433240 * 2 ^ 59
def prefixEnd_433240 : Nat := 4983230072969 + 3 ^ 40 * 433240 * 2
def baseEnd_433240 : Nat := 131828360743105291974857

theorem tailTrace_433240 : CollatzResearch.WordTrace tailWord_433240 prefixEnd_433240 131828360743105291974857 := by
  unfold tailWord_433240
  simp only [CollatzResearch.WordTrace]
  refine ⟨7900780475226473173172587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10534373966968630897563449 7900780475226473173172587)
  ·
    refine ⟨11851170712839709759758881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7900780475226473173172587 11851170712839709759758881)
    ·
      refine ⟨8888378034629782319819161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11851170712839709759758881 8888378034629782319819161)
      ·
        refine ⟨6666283525972336739864371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8888378034629782319819161 6666283525972336739864371)
        ·
          refine ⟨9999425288958505109796557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6666283525972336739864371 9999425288958505109796557)
          ·
            refine ⟨3749784483359439416173709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9999425288958505109796557 3749784483359439416173709)
            ·
              refine ⟨1406169181259789781065141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3749784483359439416173709 1406169181259789781065141)
              ·
                refine ⟨131828360743105291974857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1406169181259789781065141 131828360743105291974857)
                ·
                  rfl

theorem cell19_433240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_433240 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433240 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433240 prefixEnd_433240 := by exact prefixLift 433240
  have htrace : WordTrace (prefixWord ++ tailWord_433240) baseStart_433240 baseEnd_433240 := by
    simpa [prefixWord, tailWord_433240, baseEnd_433240] using wordTrace_append hprefix tailTrace_433240
  have hstable : (prefixWord ++ tailWord_433240).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433240).length < 2 ^ (prefixWord ++ tailWord_433240).sum := by decide
  have hdescent : baseEnd_433240 < baseStart_433240 := by decide
  rcases family_descends (prefixWord ++ tailWord_433240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433314 : List Nat := [3, 3, 1, 3, 2, 7]
def baseStart_433314 : Nat := 118140960795 + 433314 * 2 ^ 59
def prefixEnd_433314 : Nat := 4983230072969 + 3 ^ 40 * 433314 * 2
def baseEnd_433314 : Nat := 14650097535632782925579

theorem tailTrace_433314 : CollatzResearch.WordTrace tailWord_433314 prefixEnd_433314 14650097535632782925579 := by
  unfold tailWord_433314
  simp only [CollatzResearch.WordTrace]
  refine ⟨3951064988046214246134749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10536173301456571323025997 3951064988046214246134749)
  ·
    refine ⟨1481649370517330342300531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3951064988046214246134749 1481649370517330342300531)
    ·
      refine ⟨2222474055775995513450797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1481649370517330342300531 2222474055775995513450797)
      ·
        refine ⟨833427770915998317544049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2222474055775995513450797 833427770915998317544049)
        ·
          refine ⟨625070828186998738158037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 833427770915998317544049 625070828186998738158037)
          ·
            refine ⟨14650097535632782925579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 625070828186998738158037 14650097535632782925579)
            ·
              rfl

theorem cell19_433314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 7].length) (baseStart_433314 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433314 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433314 prefixEnd_433314 := by exact prefixLift 433314
  have htrace : WordTrace (prefixWord ++ tailWord_433314) baseStart_433314 baseEnd_433314 := by
    simpa [prefixWord, tailWord_433314, baseEnd_433314] using wordTrace_append hprefix tailTrace_433314
  have hstable : (prefixWord ++ tailWord_433314).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433314).length < 2 ^ (prefixWord ++ tailWord_433314).sum := by decide
  have hdescent : baseEnd_433314 < baseStart_433314 := by decide
  rcases family_descends (prefixWord ++ tailWord_433314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433316 : List Nat := [2, 3, 1, 2, 3, 8]
def baseStart_433316 : Nat := 118140960795 + 433316 * 2 ^ 59
def prefixEnd_433316 : Nat := 4983230072969 + 3 ^ 40 * 433316 * 2
def baseEnd_433316 : Nat := 14650165154484403809529

theorem tailTrace_433316 : CollatzResearch.WordTrace tailWord_433316 prefixEnd_433316 14650165154484403809529 := by
  unfold tailWord_433316
  simp only [CollatzResearch.WordTrace]
  refine ⟨7902166449088805663055901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10536221932118407550741201 7902166449088805663055901)
  ·
    refine ⟨2963312418408302123645963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7902166449088805663055901 2963312418408302123645963)
    ·
      refine ⟨4444968627612453185468945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2963312418408302123645963 4444968627612453185468945)
      ·
        refine ⟨3333726470709339889101709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4444968627612453185468945 3333726470709339889101709)
        ·
          refine ⟨1250147426516002458413141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3333726470709339889101709 1250147426516002458413141)
          ·
            refine ⟨14650165154484403809529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1250147426516002458413141 14650165154484403809529)
            ·
              rfl

theorem cell19_433316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 8].length) (baseStart_433316 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433316 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433316 prefixEnd_433316 := by exact prefixLift 433316
  have htrace : WordTrace (prefixWord ++ tailWord_433316) baseStart_433316 baseEnd_433316 := by
    simpa [prefixWord, tailWord_433316, baseEnd_433316] using wordTrace_append hprefix tailTrace_433316
  have hstable : (prefixWord ++ tailWord_433316).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433316).length < 2 ^ (prefixWord ++ tailWord_433316).sum := by decide
  have hdescent : baseEnd_433316 < baseStart_433316 := by decide
  rcases family_descends (prefixWord ++ tailWord_433316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433346 : List Nat := [3, 5, 1, 1, 2, 1, 3, 3]
def baseStart_433346 : Nat := 118140960795 + 433346 * 2 ^ 59
def prefixEnd_433346 : Nat := 4983230072969 + 3 ^ 40 * 433346 * 2
def baseEnd_433346 : Nat := 131860614935328453619013

theorem tailTrace_433346 : CollatzResearch.WordTrace tailWord_433346 prefixEnd_433346 131860614935328453619013 := by
  unfold tailWord_433346
  simp only [CollatzResearch.WordTrace]
  refine ⟨3951356772017231612425973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10536951392045950966469261 3951356772017231612425973)
  ·
    refine ⟨370439697376615463664935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3951356772017231612425973 370439697376615463664935)
    ·
      refine ⟨555659546064923195497403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 370439697376615463664935 555659546064923195497403)
      ·
        refine ⟨833489319097384793246105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555659546064923195497403 833489319097384793246105)
        ·
          refine ⟨625116989323038594934579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 833489319097384793246105 625116989323038594934579)
          ·
            refine ⟨937675483984557892401869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625116989323038594934579 937675483984557892401869)
            ·
              refine ⟨351628306494209209650701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 937675483984557892401869 351628306494209209650701)
              ·
                refine ⟨131860614935328453619013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351628306494209209650701 131860614935328453619013)
                ·
                  rfl

theorem cell19_433346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_433346 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433346 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433346 prefixEnd_433346 := by exact prefixLift 433346
  have htrace : WordTrace (prefixWord ++ tailWord_433346) baseStart_433346 baseEnd_433346 := by
    simpa [prefixWord, tailWord_433346, baseEnd_433346] using wordTrace_append hprefix tailTrace_433346
  have hstable : (prefixWord ++ tailWord_433346).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433346).length < 2 ^ (prefixWord ++ tailWord_433346).sum := by decide
  have hdescent : baseEnd_433346 < baseStart_433346 := by decide
  rcases family_descends (prefixWord ++ tailWord_433346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433409 : List Nat := [1, 2, 4, 1, 1, 3, 4, 3]
def baseStart_433409 : Nat := 118140960795 + 433409 * 2 ^ 59
def prefixEnd_433409 : Nat := 4983230072969 + 3 ^ 40 * 433409 * 2
def baseEnd_433409 : Nat := 131879784879762974218841

theorem tailTrace_433409 : CollatzResearch.WordTrace tailWord_433409 prefixEnd_433409 131879784879762974218841 := by
  unfold tailWord_433409
  simp only [CollatzResearch.WordTrace]
  refine ⟨15807724886840688209247281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10538483257893792139498187 15807724886840688209247281)
  ·
    refine ⟨11855793665130516156935461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15807724886840688209247281 11855793665130516156935461)
    ·
      refine ⟨2222961312211971779425399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11855793665130516156935461 2222961312211971779425399)
      ·
        refine ⟨3334441968317957669138099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2222961312211971779425399 3334441968317957669138099)
        ·
          refine ⟨5001662952476936503707149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3334441968317957669138099 5001662952476936503707149)
          ·
            refine ⟨1875623607178851188890181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5001662952476936503707149 1875623607178851188890181)
            ·
              refine ⟨351679426346034597916909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1875623607178851188890181 351679426346034597916909)
              ·
                refine ⟨131879784879762974218841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351679426346034597916909 131879784879762974218841)
                ·
                  rfl

theorem cell19_433409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 3].length) (baseStart_433409 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433409 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433409 prefixEnd_433409 := by exact prefixLift 433409
  have htrace : WordTrace (prefixWord ++ tailWord_433409) baseStart_433409 baseEnd_433409 := by
    simpa [prefixWord, tailWord_433409, baseEnd_433409] using wordTrace_append hprefix tailTrace_433409
  have hstable : (prefixWord ++ tailWord_433409).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433409).length < 2 ^ (prefixWord ++ tailWord_433409).sum := by decide
  have hdescent : baseEnd_433409 < baseStart_433409 := by decide
  rcases family_descends (prefixWord ++ tailWord_433409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433411 : List Nat := [1, 1, 1, 3, 2, 5, 1, 5]
def baseStart_433411 : Nat := 118140960795 + 433411 * 2 ^ 59
def prefixEnd_433411 : Nat := 4983230072969 + 3 ^ 40 * 433411 * 2
def baseEnd_433411 : Nat := 131880393449427562174391

theorem tailTrace_433411 : CollatzResearch.WordTrace tailWord_433411 prefixEnd_433411 131880393449427562174391 := by
  unfold tailWord_433411
  simp only [CollatzResearch.WordTrace]
  refine ⟨15807797832833442550820087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10538531888555628367213391 15807797832833442550820087)
  ·
    refine ⟨23711696749250163826230131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15807797832833442550820087 23711696749250163826230131)
    ·
      refine ⟨35567545123875245739345197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23711696749250163826230131 35567545123875245739345197)
      ·
        refine ⟨13337829421453217152254449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35567545123875245739345197 13337829421453217152254449)
        ·
          refine ⟨10003372066089912864190837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13337829421453217152254449 10003372066089912864190837)
          ·
            refine ⟨937816131195929331017891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10003372066089912864190837 937816131195929331017891)
            ·
              refine ⟨1406724196793893996526837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937816131195929331017891 1406724196793893996526837)
              ·
                refine ⟨131880393449427562174391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1406724196793893996526837 131880393449427562174391)
                ·
                  rfl

theorem cell19_433411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_433411 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433411 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433411 prefixEnd_433411 := by exact prefixLift 433411
  have htrace : WordTrace (prefixWord ++ tailWord_433411) baseStart_433411 baseEnd_433411 := by
    simpa [prefixWord, tailWord_433411, baseEnd_433411] using wordTrace_append hprefix tailTrace_433411
  have hstable : (prefixWord ++ tailWord_433411).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433411).length < 2 ^ (prefixWord ++ tailWord_433411).sum := by decide
  have hdescent : baseEnd_433411 < baseStart_433411 := by decide
  rcases family_descends (prefixWord ++ tailWord_433411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433468 : List Nat := [2, 2, 2, 2, 1, 3, 2, 5]
def baseStart_433468 : Nat := 118140960795 + 433468 * 2 ^ 59
def prefixEnd_433468 : Nat := 4983230072969 + 3 ^ 40 * 433468 * 2
def baseEnd_433468 : Nat := 131897737684868318907569

theorem tailTrace_433468 : CollatzResearch.WordTrace tailWord_433468 prefixEnd_433468 131897737684868318907569 := by
  unfold tailWord_433468
  simp only [CollatzResearch.WordTrace]
  refine ⟨7904938396813470642822529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10539917862417960857096705 7904938396813470642822529)
  ·
    refine ⟨5928703797610102982116897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7904938396813470642822529 5928703797610102982116897)
    ·
      refine ⟨4446527848207577236587673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5928703797610102982116897 4446527848207577236587673)
      ·
        refine ⟨3334895886155682927440755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4446527848207577236587673 3334895886155682927440755)
        ·
          refine ⟨5002343829233524391161133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3334895886155682927440755 5002343829233524391161133)
          ·
            refine ⟨1875878935962571646685425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5002343829233524391161133 1875878935962571646685425)
            ·
              refine ⟨1406909201971928735014069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1875878935962571646685425 1406909201971928735014069)
              ·
                refine ⟨131897737684868318907569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1406909201971928735014069 131897737684868318907569)
                ·
                  rfl

theorem cell19_433468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_433468 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433468 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433468 prefixEnd_433468 := by exact prefixLift 433468
  have htrace : WordTrace (prefixWord ++ tailWord_433468) baseStart_433468 baseEnd_433468 := by
    simpa [prefixWord, tailWord_433468, baseEnd_433468] using wordTrace_append hprefix tailTrace_433468
  have hstable : (prefixWord ++ tailWord_433468).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433468).length < 2 ^ (prefixWord ++ tailWord_433468).sum := by decide
  have hdescent : baseEnd_433468 < baseStart_433468 := by decide
  rcases family_descends (prefixWord ++ tailWord_433468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433485 : List Nat := [1, 6, 1, 3, 8]
def baseStart_433485 : Nat := 118140960795 + 433485 * 2 ^ 59
def prefixEnd_433485 : Nat := 4983230072969 + 3 ^ 40 * 433485 * 2
def baseEnd_433485 : Nat := 4885292982482122834435

theorem tailTrace_433485 : CollatzResearch.WordTrace tailWord_433485 prefixEnd_433485 4885292982482122834435 := by
  unfold tailWord_433485
  simp only [CollatzResearch.WordTrace]
  refine ⟨15810496834565353189013909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10540331223043568792675939 15810496834565353189013909)
  ·
    refine ⟨741117039120250930735027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15810496834565353189013909 741117039120250930735027)
    ·
      refine ⟨1111675558680376396102541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 741117039120250930735027 1111675558680376396102541)
      ·
        refine ⟨416878334505141148538453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1111675558680376396102541 416878334505141148538453)
        ·
          refine ⟨4885292982482122834435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 416878334505141148538453 4885292982482122834435)
          ·
            rfl

theorem cell19_433485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 8].length) (baseStart_433485 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433485 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433485 prefixEnd_433485 := by exact prefixLift 433485
  have htrace : WordTrace (prefixWord ++ tailWord_433485) baseStart_433485 baseEnd_433485 := by
    simpa [prefixWord, tailWord_433485, baseEnd_433485] using wordTrace_append hprefix tailTrace_433485
  have hstable : (prefixWord ++ tailWord_433485).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433485).length < 2 ^ (prefixWord ++ tailWord_433485).sum := by decide
  have hdescent : baseEnd_433485 < baseStart_433485 := by decide
  rcases family_descends (prefixWord ++ tailWord_433485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433504 : List Nat := [2, 1, 1, 3, 4, 3, 1, 4]
def baseStart_433504 : Nat := 118140960795 + 433504 * 2 ^ 59
def prefixEnd_433504 : Nat := 4983230072969 + 3 ^ 40 * 433504 * 2
def baseEnd_433504 : Nat := 131908691938830902107471

theorem tailTrace_433504 : CollatzResearch.WordTrace tailWord_433504 prefixEnd_433504 131908691938830902107471 := by
  unfold tailWord_433504
  simp only [CollatzResearch.WordTrace]
  refine ⟨7905594910748259716977783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10540793214331012955970377 7905594910748259716977783)
  ·
    refine ⟨11858392366122389575466675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7905594910748259716977783 11858392366122389575466675)
    ·
      refine ⟨17787588549183584363200013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11858392366122389575466675 17787588549183584363200013)
      ·
        refine ⟨6670345705943844136200005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17787588549183584363200013 6670345705943844136200005)
        ·
          refine ⟨1250689819864470775537501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6670345705943844136200005 1250689819864470775537501)
          ·
            refine ⟨469008682449176540826563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1250689819864470775537501 469008682449176540826563)
            ·
              refine ⟨703513023673764811239845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469008682449176540826563 703513023673764811239845)
              ·
                refine ⟨131908691938830902107471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 703513023673764811239845 131908691938830902107471)
                ·
                  rfl

theorem cell19_433504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_433504 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433504 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433504 prefixEnd_433504 := by exact prefixLift 433504
  have htrace : WordTrace (prefixWord ++ tailWord_433504) baseStart_433504 baseEnd_433504 := by
    simpa [prefixWord, tailWord_433504, baseEnd_433504] using wordTrace_append hprefix tailTrace_433504
  have hstable : (prefixWord ++ tailWord_433504).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433504).length < 2 ^ (prefixWord ++ tailWord_433504).sum := by decide
  have hdescent : baseEnd_433504 < baseStart_433504 := by decide
  rcases family_descends (prefixWord ++ tailWord_433504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433544 : List Nat := [2, 1, 3, 3, 1, 3, 6]
def baseStart_433544 : Nat := 118140960795 + 433544 * 2 ^ 59
def prefixEnd_433544 : Nat := 4983230072969 + 3 ^ 40 * 433544 * 2
def baseEnd_433544 : Nat := 43973621110707553739491

theorem tailTrace_433544 : CollatzResearch.WordTrace tailWord_433544 prefixEnd_433544 43973621110707553739491 := by
  unfold tailWord_433544
  simp only [CollatzResearch.WordTrace]
  refine ⟨7906324370675803132705843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10541765827567737510274457 7906324370675803132705843)
  ·
    refine ⟨11859486556013704699058765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7906324370675803132705843 11859486556013704699058765)
    ·
      refine ⟨4447307458505139262147037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11859486556013704699058765 4447307458505139262147037)
      ·
        refine ⟨1667740296939427223305139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4447307458505139262147037 1667740296939427223305139)
        ·
          refine ⟨2501610445409140834957709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1667740296939427223305139 2501610445409140834957709)
          ·
            refine ⟨938103917028427813109141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2501610445409140834957709 938103917028427813109141)
            ·
              refine ⟨43973621110707553739491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 938103917028427813109141 43973621110707553739491)
              ·
                rfl

theorem cell19_433544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 6].length) (baseStart_433544 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433544 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433544 prefixEnd_433544 := by exact prefixLift 433544
  have htrace : WordTrace (prefixWord ++ tailWord_433544) baseStart_433544 baseEnd_433544 := by
    simpa [prefixWord, tailWord_433544, baseEnd_433544] using wordTrace_append hprefix tailTrace_433544
  have hstable : (prefixWord ++ tailWord_433544).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433544).length < 2 ^ (prefixWord ++ tailWord_433544).sum := by decide
  have hdescent : baseEnd_433544 < baseStart_433544 := by decide
  rcases family_descends (prefixWord ++ tailWord_433544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433576 : List Nat := [2, 1, 6, 1, 2, 2, 2, 3]
def baseStart_433576 : Nat := 118140960795 + 433576 * 2 ^ 59
def prefixEnd_433576 : Nat := 4983230072969 + 3 ^ 40 * 433576 * 2
def baseEnd_433576 : Nat := 131930600446756068507275

theorem tailTrace_433576 : CollatzResearch.WordTrace tailWord_433576 prefixEnd_433576 131930600446756068507275 := by
  unfold tailWord_433576
  simp only [CollatzResearch.WordTrace]
  refine ⟨7906907938617837865288291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10542543918157117153717721 7906907938617837865288291)
  ·
    refine ⟨11860361907926756797932437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7906907938617837865288291 11860361907926756797932437)
    ·
      refine ⟨555954464434066724903083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11860361907926756797932437 555954464434066724903083)
      ·
        refine ⟨833931696651100087354625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555954464434066724903083 833931696651100087354625)
        ·
          refine ⟨625448772488325065515969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 833931696651100087354625 625448772488325065515969)
          ·
            refine ⟨469086579366243799136977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 625448772488325065515969 469086579366243799136977)
            ·
              refine ⟨351814934524682849352733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469086579366243799136977 351814934524682849352733)
              ·
                refine ⟨131930600446756068507275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351814934524682849352733 131930600446756068507275)
                ·
                  rfl

theorem cell19_433576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_433576 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433576 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433576 prefixEnd_433576 := by exact prefixLift 433576
  have htrace : WordTrace (prefixWord ++ tailWord_433576) baseStart_433576 baseEnd_433576 := by
    simpa [prefixWord, tailWord_433576, baseEnd_433576] using wordTrace_append hprefix tailTrace_433576
  have hstable : (prefixWord ++ tailWord_433576).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433576).length < 2 ^ (prefixWord ++ tailWord_433576).sum := by decide
  have hdescent : baseEnd_433576 < baseStart_433576 := by decide
  rcases family_descends (prefixWord ++ tailWord_433576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433603 : List Nat := [1, 1, 1, 3, 1, 1, 11]
def baseStart_433603 : Nat := 118140960795 + 433603 * 2 ^ 59
def prefixEnd_433603 : Nat := 4983230072969 + 3 ^ 40 * 433603 * 2
def baseEnd_433603 : Nat := 43979605379076001969067

theorem tailTrace_433603 : CollatzResearch.WordTrace tailWord_433603 prefixEnd_433603 43979605379076001969067 := by
  unfold tailWord_433603
  simp only [CollatzResearch.WordTrace]
  refine ⟨15814800648137859341809463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10543200432091906227872975 15814800648137859341809463)
  ·
    refine ⟨23722200972206789012714195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15814800648137859341809463 23722200972206789012714195)
    ·
      refine ⟨35583301458310183519071293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23722200972206789012714195 35583301458310183519071293)
      ·
        refine ⟨13343738046866318819651735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35583301458310183519071293 13343738046866318819651735)
        ·
          refine ⟨20015607070299478229477603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13343738046866318819651735 20015607070299478229477603)
          ·
            refine ⟨30023410605449217344216405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20015607070299478229477603 30023410605449217344216405)
            ·
              refine ⟨43979605379076001969067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 30023410605449217344216405 43979605379076001969067)
              ·
                rfl

theorem cell19_433603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 11].length) (baseStart_433603 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433603 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433603 prefixEnd_433603 := by exact prefixLift 433603
  have htrace : WordTrace (prefixWord ++ tailWord_433603) baseStart_433603 baseEnd_433603 := by
    simpa [prefixWord, tailWord_433603, baseEnd_433603] using wordTrace_append hprefix tailTrace_433603
  have hstable : (prefixWord ++ tailWord_433603).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433603).length < 2 ^ (prefixWord ++ tailWord_433603).sum := by decide
  have hdescent : baseEnd_433603 < baseStart_433603 := by decide
  rcases family_descends (prefixWord ++ tailWord_433603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433639 : List Nat := [1, 1, 5, 2, 1, 2, 2, 5]
def baseStart_433639 : Nat := 118140960795 + 433639 * 2 ^ 59
def prefixEnd_433639 : Nat := 4983230072969 + 3 ^ 40 * 433639 * 2
def baseEnd_433639 : Nat := 131949770391190589107103

theorem tailTrace_433639 : CollatzResearch.WordTrace tailWord_433639 prefixEnd_433639 131949770391190589107103 := by
  unfold tailWord_433639
  simp only [CollatzResearch.WordTrace]
  refine ⟨15816113676007437490119971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10544075784004958326746647 15816113676007437490119971)
  ·
    refine ⟨23724170514011156235179957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15816113676007437490119971 23724170514011156235179957)
    ·
      refine ⟨2224140985688545897048121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23724170514011156235179957 2224140985688545897048121)
      ·
        refine ⟨1668105739266409422786091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2224140985688545897048121 1668105739266409422786091)
        ·
          refine ⟨2502158608899614134179137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1668105739266409422786091 2502158608899614134179137)
          ·
            refine ⟨1876618956674710600634353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2502158608899614134179137 1876618956674710600634353)
            ·
              refine ⟨1407464217506032950475765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1876618956674710600634353 1407464217506032950475765)
              ·
                refine ⟨131949770391190589107103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1407464217506032950475765 131949770391190589107103)
                ·
                  rfl

theorem cell19_433639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_433639 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433639 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433639 prefixEnd_433639 := by exact prefixLift 433639
  have htrace : WordTrace (prefixWord ++ tailWord_433639) baseStart_433639 baseEnd_433639 := by
    simpa [prefixWord, tailWord_433639, baseEnd_433639] using wordTrace_append hprefix tailTrace_433639
  have hstable : (prefixWord ++ tailWord_433639).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433639).length < 2 ^ (prefixWord ++ tailWord_433639).sum := by decide
  have hdescent : baseEnd_433639 < baseStart_433639 := by decide
  rcases family_descends (prefixWord ++ tailWord_433639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433675 : List Nat := [1, 1, 1, 1, 8, 2, 1, 4]
def baseStart_433675 : Nat := 118140960795 + 433675 * 2 ^ 59
def prefixEnd_433675 : Nat := 4983230072969 + 3 ^ 40 * 433675 * 2
def baseEnd_433675 : Nat := 131960724645153172307005

theorem tailTrace_433675 : CollatzResearch.WordTrace tailWord_433675 prefixEnd_433675 131960724645153172307005 := by
  unfold tailWord_433675
  simp only [CollatzResearch.WordTrace]
  refine ⟨15817426703877015638430479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10544951135918010425620319 15817426703877015638430479)
  ·
    refine ⟨23726140055815523457645719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15817426703877015638430479 23726140055815523457645719)
    ·
      refine ⟨35589210083723285186468579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23726140055815523457645719 35589210083723285186468579)
      ·
        refine ⟨53383815125584927779702869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35589210083723285186468579 53383815125584927779702869)
        ·
          refine ⟨625591583502948372418393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 53383815125584927779702869 625591583502948372418393)
          ·
            refine ⟨469193687627211279313795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 625591583502948372418393 469193687627211279313795)
            ·
              refine ⟨703790531440816918970693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469193687627211279313795 703790531440816918970693)
              ·
                refine ⟨131960724645153172307005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 703790531440816918970693 131960724645153172307005)
                ·
                  rfl

theorem cell19_433675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 4].length) (baseStart_433675 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433675 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433675 prefixEnd_433675 := by exact prefixLift 433675
  have htrace : WordTrace (prefixWord ++ tailWord_433675) baseStart_433675 baseEnd_433675 := by
    simpa [prefixWord, tailWord_433675, baseEnd_433675] using wordTrace_append hprefix tailTrace_433675
  have hstable : (prefixWord ++ tailWord_433675).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433675).length < 2 ^ (prefixWord ++ tailWord_433675).sum := by decide
  have hdescent : baseEnd_433675 < baseStart_433675 := by decide
  rcases family_descends (prefixWord ++ tailWord_433675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433751 : List Nat := [1, 1, 3, 2, 2, 5, 2, 3]
def baseStart_433751 : Nat := 118140960795 + 433751 * 2 ^ 59
def prefixEnd_433751 : Nat := 4983230072969 + 3 ^ 40 * 433751 * 2
def baseEnd_433751 : Nat := 131983850292407514617909

theorem tailTrace_433751 : CollatzResearch.WordTrace tailWord_433751 prefixEnd_433751 131983850292407514617909 := by
  unfold tailWord_433751
  simp only [CollatzResearch.WordTrace]
  refine ⟨15820198651601680618197107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10546799101067787078798071 15820198651601680618197107)
  ·
    refine ⟨23730297977402520927295661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15820198651601680618197107 23730297977402520927295661)
    ·
      refine ⟨8898861741525945347735873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23730297977402520927295661 8898861741525945347735873)
      ·
        refine ⟨6674146306144459010801905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8898861741525945347735873 6674146306144459010801905)
        ·
          refine ⟨5005609729608344258101429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6674146306144459010801905 5005609729608344258101429)
          ·
            refine ⟨469275912150782274197009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5005609729608344258101429 469275912150782274197009)
            ·
              refine ⟨351956934113086705647757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469275912150782274197009 351956934113086705647757)
              ·
                refine ⟨131983850292407514617909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 351956934113086705647757 131983850292407514617909)
                ·
                  rfl

theorem cell19_433751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 3].length) (baseStart_433751 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433751 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433751 prefixEnd_433751 := by exact prefixLift 433751
  have htrace : WordTrace (prefixWord ++ tailWord_433751) baseStart_433751 baseEnd_433751 := by
    simpa [prefixWord, tailWord_433751, baseEnd_433751] using wordTrace_append hprefix tailTrace_433751
  have hstable : (prefixWord ++ tailWord_433751).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433751).length < 2 ^ (prefixWord ++ tailWord_433751).sum := by decide
  have hdescent : baseEnd_433751 < baseStart_433751 := by decide
  rcases family_descends (prefixWord ++ tailWord_433751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433831 : List Nat := [1, 1, 6, 11]
def baseStart_433831 : Nat := 118140960795 + 433831 * 2 ^ 59
def prefixEnd_433831 : Nat := 4983230072969 + 3 ^ 40 * 433831 * 2
def baseEnd_433831 : Nat := 1629730778752975714073

theorem tailTrace_433831 : CollatzResearch.WordTrace tailWord_433831 prefixEnd_433831 1629730778752975714073 := by
  unfold tailWord_433831
  simp only [CollatzResearch.WordTrace]
  refine ⟨15823116491311854281109347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10548744327541236187406231 15823116491311854281109347)
  ·
    refine ⟨23734674736967781421664021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15823116491311854281109347 23734674736967781421664021)
    ·
      refine ⟨1112562878295364754140501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23734674736967781421664021 1112562878295364754140501)
      ·
        refine ⟨1629730778752975714073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1112562878295364754140501 1629730778752975714073)
        ·
          rfl

theorem cell19_433831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 11].length) (baseStart_433831 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433831 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433831 prefixEnd_433831 := by exact prefixLift 433831
  have htrace : WordTrace (prefixWord ++ tailWord_433831) baseStart_433831 baseEnd_433831 := by
    simpa [prefixWord, tailWord_433831, baseEnd_433831] using wordTrace_append hprefix tailTrace_433831
  have hstable : (prefixWord ++ tailWord_433831).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433831).length < 2 ^ (prefixWord ++ tailWord_433831).sum := by decide
  have hdescent : baseEnd_433831 < baseStart_433831 := by decide
  rcases family_descends (prefixWord ++ tailWord_433831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433884 : List Nat := [2, 2, 5, 1, 2, 1, 6]
def baseStart_433884 : Nat := 118140960795 + 433884 * 2 ^ 59
def prefixEnd_433884 : Nat := 4983230072969 + 3 ^ 40 * 433884 * 2
def baseEnd_433884 : Nat := 44008106725034204553997

theorem tailTrace_433884 : CollatzResearch.WordTrace tailWord_433884 prefixEnd_433884 44008106725034204553997 := by
  unfold tailWord_433884
  simp only [CollatzResearch.WordTrace]
  refine ⟨7912524780059922166394353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10550033040079896221859137 7912524780059922166394353)
  ·
    refine ⟨5934393585044941624795765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7912524780059922166394353 5934393585044941624795765)
    ·
      refine ⟨556349398597963277324603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5934393585044941624795765 556349398597963277324603)
      ·
        refine ⟨834524097896944915986905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556349398597963277324603 834524097896944915986905)
        ·
          refine ⟨625893073422708686990179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 834524097896944915986905 625893073422708686990179)
          ·
            refine ⟨938839610134063030485269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625893073422708686990179 938839610134063030485269)
            ·
              refine ⟨44008106725034204553997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 938839610134063030485269 44008106725034204553997)
              ·
                rfl

theorem cell19_433884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 6].length) (baseStart_433884 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433884 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433884 prefixEnd_433884 := by exact prefixLift 433884
  have htrace : WordTrace (prefixWord ++ tailWord_433884) baseStart_433884 baseEnd_433884 := by
    simpa [prefixWord, tailWord_433884, baseEnd_433884] using wordTrace_append hprefix tailTrace_433884
  have hstable : (prefixWord ++ tailWord_433884).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433884).length < 2 ^ (prefixWord ++ tailWord_433884).sum := by decide
  have hdescent : baseEnd_433884 < baseStart_433884 := by decide
  rcases family_descends (prefixWord ++ tailWord_433884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433918 : List Nat := [4, 2, 2, 1, 4, 1, 2, 3]
def baseStart_433918 : Nat := 118140960795 + 433918 * 2 ^ 59
def prefixEnd_433918 : Nat := 4983230072969 + 3 ^ 40 * 433918 * 2
def baseEnd_433918 : Nat := 132034665859400608906343

theorem tailTrace_433918 : CollatzResearch.WordTrace tailWord_433918 prefixEnd_433918 132034665859400608906343 := by
  unfold tailWord_433918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1978286205249583517440801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10550859761331112093017605 1978286205249583517440801)
  ·
    refine ⟨1483714653937187638080601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1978286205249583517440801 1483714653937187638080601)
    ·
      refine ⟨1112785990452890728560451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1483714653937187638080601 1112785990452890728560451)
      ·
        refine ⟨1669178985679336092840677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1112785990452890728560451 1669178985679336092840677)
        ·
          refine ⟨312971059814875517407627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1669178985679336092840677 312971059814875517407627)
          ·
            refine ⟨469456589722313276111441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312971059814875517407627 469456589722313276111441)
            ·
              refine ⟨352092442291734957083581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469456589722313276111441 352092442291734957083581)
              ·
                refine ⟨132034665859400608906343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352092442291734957083581 132034665859400608906343)
                ·
                  rfl

theorem cell19_433918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_433918 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433918 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433918 prefixEnd_433918 := by exact prefixLift 433918
  have htrace : WordTrace (prefixWord ++ tailWord_433918) baseStart_433918 baseEnd_433918 := by
    simpa [prefixWord, tailWord_433918, baseEnd_433918] using wordTrace_append hprefix tailTrace_433918
  have hstable : (prefixWord ++ tailWord_433918).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433918).length < 2 ^ (prefixWord ++ tailWord_433918).sum := by decide
  have hdescent : baseEnd_433918 < baseStart_433918 := by decide
  rcases family_descends (prefixWord ++ tailWord_433918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433924 : List Nat := [2, 3, 2, 2, 1, 3, 1, 5]
def baseStart_433924 : Nat := 118140960795 + 433924 * 2 ^ 59
def prefixEnd_433924 : Nat := 4983230072969 + 3 ^ 40 * 433924 * 2
def baseEnd_433924 : Nat := 132036491568394372772993

theorem tailTrace_433924 : CollatzResearch.WordTrace tailWord_433924 prefixEnd_433924 132036491568394372772993 := by
  unfold tailWord_433924
  simp only [CollatzResearch.WordTrace]
  refine ⟨7913254239987465582122413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10551005653316620776163217 7913254239987465582122413)
  ·
    refine ⟨2967470339995299593295905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7913254239987465582122413 2967470339995299593295905)
    ·
      refine ⟨2225602754996474694971929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2967470339995299593295905 2225602754996474694971929)
      ·
        refine ⟨1669202066247356021228947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2225602754996474694971929 1669202066247356021228947)
        ·
          refine ⟨2503803099371034031843421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1669202066247356021228947 2503803099371034031843421)
          ·
            refine ⟨938926162264137761941283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2503803099371034031843421 938926162264137761941283)
            ·
              refine ⟨1408389243396206642911925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938926162264137761941283 1408389243396206642911925)
              ·
                refine ⟨132036491568394372772993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1408389243396206642911925 132036491568394372772993)
                ·
                  rfl

theorem cell19_433924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_433924 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433924 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433924 prefixEnd_433924 := by exact prefixLift 433924
  have htrace : WordTrace (prefixWord ++ tailWord_433924) baseStart_433924 baseEnd_433924 := by
    simpa [prefixWord, tailWord_433924, baseEnd_433924] using wordTrace_append hprefix tailTrace_433924
  have hstable : (prefixWord ++ tailWord_433924).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433924).length < 2 ^ (prefixWord ++ tailWord_433924).sum := by decide
  have hdescent : baseEnd_433924 < baseStart_433924 := by decide
  rcases family_descends (prefixWord ++ tailWord_433924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433943 : List Nat := [1, 1, 3, 4, 2, 3, 5]
def baseStart_433943 : Nat := 118140960795 + 433943 * 2 ^ 59
def prefixEnd_433943 : Nat := 4983230072969 + 3 ^ 40 * 433943 * 2
def baseEnd_433943 : Nat := 44014090993402652783573

theorem tailTrace_433943 : CollatzResearch.WordTrace tailWord_433943 prefixEnd_433943 44014090993402652783573 := by
  unfold tailWord_433943
  simp only [CollatzResearch.WordTrace]
  refine ⟨15827201466906097409186483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10551467644604064939457655 15827201466906097409186483)
  ·
    refine ⟨23740802200359146113779725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15827201466906097409186483 23740802200359146113779725)
    ·
      refine ⟨8902800825134679792667397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23740802200359146113779725 8902800825134679792667397)
      ·
        refine ⟨1669275154712752461125137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8902800825134679792667397 1669275154712752461125137)
        ·
          refine ⟨1251956366034564345843853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1669275154712752461125137 1251956366034564345843853)
          ·
            refine ⟨469483637262961629691445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1251956366034564345843853 469483637262961629691445)
            ·
              refine ⟨44014090993402652783573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 469483637262961629691445 44014090993402652783573)
              ·
                rfl

theorem cell19_433943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 5].length) (baseStart_433943 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433943 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433943 prefixEnd_433943 := by exact prefixLift 433943
  have htrace : WordTrace (prefixWord ++ tailWord_433943) baseStart_433943 baseEnd_433943 := by
    simpa [prefixWord, tailWord_433943, baseEnd_433943] using wordTrace_append hprefix tailTrace_433943
  have hstable : (prefixWord ++ tailWord_433943).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433943).length < 2 ^ (prefixWord ++ tailWord_433943).sum := by decide
  have hdescent : baseEnd_433943 < baseStart_433943 := by decide
  rcases family_descends (prefixWord ++ tailWord_433943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433964 : List Nat := [2, 2, 1, 1, 1, 5, 1, 6]
def baseStart_433964 : Nat := 118140960795 + 433964 * 2 ^ 59
def prefixEnd_433964 : Nat := 4983230072969 + 3 ^ 40 * 433964 * 2
def baseEnd_433964 : Nat := 132048662961686131883995

theorem tailTrace_433964 : CollatzResearch.WordTrace tailWord_433964 prefixEnd_433964 132048662961686131883995 := by
  unfold tailWord_433964
  simp only [CollatzResearch.WordTrace]
  refine ⟨7913983699915008997850473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10551978266553345330467297 7913983699915008997850473)
  ·
    refine ⟨5935487774936256748387855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7913983699915008997850473 5935487774936256748387855)
    ·
      refine ⟨8903231662404385122581783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5935487774936256748387855 8903231662404385122581783)
      ·
        refine ⟨13354847493606577683872675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8903231662404385122581783 13354847493606577683872675)
        ·
          refine ⟨20032271240409866525809013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13354847493606577683872675 20032271240409866525809013)
          ·
            refine ⟨1878025428788424986794595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20032271240409866525809013 1878025428788424986794595)
            ·
              refine ⟨2817038143182637480191893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1878025428788424986794595 2817038143182637480191893)
              ·
                refine ⟨132048662961686131883995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2817038143182637480191893 132048662961686131883995)
                ·
                  rfl

theorem cell19_433964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_433964 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433964 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433964 prefixEnd_433964 := by exact prefixLift 433964
  have htrace : WordTrace (prefixWord ++ tailWord_433964) baseStart_433964 baseEnd_433964 := by
    simpa [prefixWord, tailWord_433964, baseEnd_433964] using wordTrace_append hprefix tailTrace_433964
  have hstable : (prefixWord ++ tailWord_433964).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433964).length < 2 ^ (prefixWord ++ tailWord_433964).sum := by decide
  have hdescent : baseEnd_433964 < baseStart_433964 := by decide
  rcases family_descends (prefixWord ++ tailWord_433964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_433981 : List Nat := [1, 4, 1, 4, 1, 1, 2, 5]
def baseStart_433981 : Nat := 118140960795 + 433981 * 2 ^ 59
def prefixEnd_433981 : Nat := 4983230072969 + 3 ^ 40 * 433981 * 2
def baseEnd_433981 : Nat := 132053835803835129506171

theorem tailTrace_433981 : CollatzResearch.WordTrace tailWord_433981 prefixEnd_433981 132053835803835129506171 := by
  unfold tailWord_433981
  simp only [CollatzResearch.WordTrace]
  refine ⟨15828587440768429899069797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10552391627178953266046531 15828587440768429899069797)
  ·
    refine ⟨2967860145144080606075587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15828587440768429899069797 2967860145144080606075587)
    ·
      refine ⟨4451790217716120909113381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2967860145144080606075587 4451790217716120909113381)
      ·
        refine ⟨834710665821772670458759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4451790217716120909113381 834710665821772670458759)
        ·
          refine ⟨1252065998732659005688139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834710665821772670458759 1252065998732659005688139)
          ·
            refine ⟨1878098998098988508532209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252065998732659005688139 1878098998098988508532209)
            ·
              refine ⟨1408574248574241381399157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1878098998098988508532209 1408574248574241381399157)
              ·
                refine ⟨132053835803835129506171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1408574248574241381399157 132053835803835129506171)
                ·
                  rfl

theorem cell19_433981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 5].length) (baseStart_433981 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_433981 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_433981 prefixEnd_433981 := by exact prefixLift 433981
  have htrace : WordTrace (prefixWord ++ tailWord_433981) baseStart_433981 baseEnd_433981 := by
    simpa [prefixWord, tailWord_433981, baseEnd_433981] using wordTrace_append hprefix tailTrace_433981
  have hstable : (prefixWord ++ tailWord_433981).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_433981).length < 2 ^ (prefixWord ++ tailWord_433981).sum := by decide
  have hdescent : baseEnd_433981 < baseStart_433981 := by decide
  rcases family_descends (prefixWord ++ tailWord_433981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434002 : List Nat := [3, 2, 2, 1, 1, 10]
def baseStart_434002 : Nat := 118140960795 + 434002 * 2 ^ 59
def prefixEnd_434002 : Nat := 4983230072969 + 3 ^ 40 * 434002 * 2
def baseEnd_434002 : Nat := 14673358420590367004383

theorem tailTrace_434002 : CollatzResearch.WordTrace tailWord_434002 prefixEnd_434002 14673358420590367004383 := by
  unfold tailWord_434002
  simp only [CollatzResearch.WordTrace]
  refine ⟨3957338343423087621396065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10552902249128233657056173 3957338343423087621396065)
  ·
    refine ⟨2968003757567315716047049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3957338343423087621396065 2968003757567315716047049)
    ·
      refine ⟨2226002818175486787035287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2968003757567315716047049 2226002818175486787035287)
      ·
        refine ⟨3339004227263230180552931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2226002818175486787035287 3339004227263230180552931)
        ·
          refine ⟨5008506340894845270829397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3339004227263230180552931 5008506340894845270829397)
          ·
            refine ⟨14673358420590367004383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5008506340894845270829397 14673358420590367004383)
            ·
              rfl

theorem cell19_434002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 10].length) (baseStart_434002 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434002 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434002 prefixEnd_434002 := by exact prefixLift 434002
  have htrace : WordTrace (prefixWord ++ tailWord_434002) baseStart_434002 baseEnd_434002 := by
    simpa [prefixWord, tailWord_434002, baseEnd_434002] using wordTrace_append hprefix tailTrace_434002
  have hstable : (prefixWord ++ tailWord_434002).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434002).length < 2 ^ (prefixWord ++ tailWord_434002).sum := by decide
  have hdescent : baseEnd_434002 < baseStart_434002 := by decide
  rcases family_descends (prefixWord ++ tailWord_434002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434133 : List Nat := [1, 3, 2, 3, 2, 2, 2, 4]
def baseStart_434133 : Nat := 118140960795 + 434133 * 2 ^ 59
def prefixEnd_434133 : Nat := 4983230072969 + 3 ^ 40 * 434133 * 2
def baseEnd_434133 : Nat := 132100087098343814127979

theorem tailTrace_434133 : CollatzResearch.WordTrace tailWord_434133 prefixEnd_434133 132100087098343814127979 := by
  unfold tailWord_434133
  simp only [CollatzResearch.WordTrace]
  refine ⟨15834131336217759858603053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10556087557478506572402035 15834131336217759858603053)
  ·
    refine ⟨5937799251081659946976145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15834131336217759858603053 5937799251081659946976145)
    ·
      refine ⟨4453349438311244960232109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5937799251081659946976145 4453349438311244960232109)
      ·
        refine ⟨1670006039366716860087041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4453349438311244960232109 1670006039366716860087041)
        ·
          refine ⟨1252504529525037645065281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1670006039366716860087041 1252504529525037645065281)
          ·
            refine ⟨939378397143778233798961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1252504529525037645065281 939378397143778233798961)
            ·
              refine ⟨704533797857833675349221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 939378397143778233798961 704533797857833675349221)
              ·
                refine ⟨132100087098343814127979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 704533797857833675349221 132100087098343814127979)
                ·
                  rfl

theorem cell19_434133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 4].length) (baseStart_434133 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434133 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434133 prefixEnd_434133 := by exact prefixLift 434133
  have htrace : WordTrace (prefixWord ++ tailWord_434133) baseStart_434133 baseEnd_434133 := by
    simpa [prefixWord, tailWord_434133, baseEnd_434133] using wordTrace_append hprefix tailTrace_434133
  have hstable : (prefixWord ++ tailWord_434133).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434133).length < 2 ^ (prefixWord ++ tailWord_434133).sum := by decide
  have hdescent : baseEnd_434133 < baseStart_434133 := by decide
  rcases family_descends (prefixWord ++ tailWord_434133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434135 : List Nat := [1, 1, 3, 2, 1, 1, 6, 4]
def baseStart_434135 : Nat := 118140960795 + 434135 * 2 ^ 59
def prefixEnd_434135 : Nat := 4983230072969 + 3 ^ 40 * 434135 * 2
def baseEnd_434135 : Nat := 132100695668008402083529

theorem tailTrace_434135 : CollatzResearch.WordTrace tailWord_434135 prefixEnd_434135 132100695668008402083529 := by
  unfold tailWord_434135
  simp only [CollatzResearch.WordTrace]
  refine ⟨15834204282210514200175859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10556136188140342800117239 15834204282210514200175859)
  ·
    refine ⟨23751306423315771300263789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15834204282210514200175859 23751306423315771300263789)
    ·
      refine ⟨8906739908743414237598921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23751306423315771300263789 8906739908743414237598921)
      ·
        refine ⟨6680054931557560678199191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8906739908743414237598921 6680054931557560678199191)
        ·
          refine ⟨10020082397336341017298787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6680054931557560678199191 10020082397336341017298787)
          ·
            refine ⟨15030123596004511525948181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10020082397336341017298787 15030123596004511525948181)
            ·
              refine ⟨704537043562711477778821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15030123596004511525948181 704537043562711477778821)
              ·
                refine ⟨132100695668008402083529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 704537043562711477778821 132100695668008402083529)
                ·
                  rfl

theorem cell19_434135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_434135 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434135 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434135 prefixEnd_434135 := by exact prefixLift 434135
  have htrace : WordTrace (prefixWord ++ tailWord_434135) baseStart_434135 baseEnd_434135 := by
    simpa [prefixWord, tailWord_434135, baseEnd_434135] using wordTrace_append hprefix tailTrace_434135
  have hstable : (prefixWord ++ tailWord_434135).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434135).length < 2 ^ (prefixWord ++ tailWord_434135).sum := by decide
  have hdescent : baseEnd_434135 < baseStart_434135 := by decide
  rcases family_descends (prefixWord ++ tailWord_434135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434154 : List Nat := [3, 1, 3, 1, 2, 1, 1, 7]
def baseStart_434154 : Nat := 118140960795 + 434154 * 2 ^ 59
def prefixEnd_434154 : Nat := 4983230072969 + 3 ^ 40 * 434154 * 2
def baseEnd_434154 : Nat := 132106477079821987661255

theorem tailTrace_434154 : CollatzResearch.WordTrace tailWord_434154 prefixEnd_434154 132106477079821987661255 := by
  unfold tailWord_434154
  simp only [CollatzResearch.WordTrace]
  refine ⟨3958724317285420111279379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10556598179427786963411677 3958724317285420111279379)
  ·
    refine ⟨5938086475928130166919069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3958724317285420111279379 5938086475928130166919069)
    ·
      refine ⟨2226782428473048812594651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5938086475928130166919069 2226782428473048812594651)
      ·
        refine ⟨3340173642709573218891977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2226782428473048812594651 3340173642709573218891977)
        ·
          refine ⟨2505130232032179914168983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3340173642709573218891977 2505130232032179914168983)
          ·
            refine ⟨3757695348048269871253475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505130232032179914168983 3757695348048269871253475)
            ·
              refine ⟨5636543022072404806880213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3757695348048269871253475 5636543022072404806880213)
              ·
                refine ⟨132106477079821987661255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5636543022072404806880213 132106477079821987661255)
                ·
                  rfl

theorem cell19_434154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_434154 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434154 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434154 prefixEnd_434154 := by exact prefixLift 434154
  have htrace : WordTrace (prefixWord ++ tailWord_434154) baseStart_434154 baseEnd_434154 := by
    simpa [prefixWord, tailWord_434154, baseEnd_434154] using wordTrace_append hprefix tailTrace_434154
  have hstable : (prefixWord ++ tailWord_434154).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434154).length < 2 ^ (prefixWord ++ tailWord_434154).sum := by decide
  have hdescent : baseEnd_434154 < baseStart_434154 := by decide
  rcases family_descends (prefixWord ++ tailWord_434154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434182 : List Nat := [6, 2, 1, 2, 1, 2, 1, 4]
def baseStart_434182 : Nat := 118140960795 + 434182 * 2 ^ 59
def prefixEnd_434182 : Nat := 4983230072969 + 3 ^ 40 * 434182 * 2
def baseEnd_434182 : Nat := 132114997055126219038957

theorem tailTrace_434182 : CollatzResearch.WordTrace tailWord_434182 prefixEnd_434182 132114997055126219038957 := by
  unfold tailWord_434182
  simp only [CollatzResearch.WordTrace]
  refine ⟨494872453532507538348025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10557279008693494151424533 494872453532507538348025)
  ·
    refine ⟨371154340149380653761019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 494872453532507538348025 371154340149380653761019)
    ·
      refine ⟨556731510224070980641529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371154340149380653761019 556731510224070980641529)
      ·
        refine ⟨417548632668053235481147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 556731510224070980641529 417548632668053235481147)
        ·
          refine ⟨626322949002079853221721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417548632668053235481147 626322949002079853221721)
          ·
            refine ⟨469742211751559889916291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 626322949002079853221721 469742211751559889916291)
            ·
              refine ⟨704613317627339834874437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469742211751559889916291 704613317627339834874437)
              ·
                refine ⟨132114997055126219038957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 704613317627339834874437 132114997055126219038957)
                ·
                  rfl

theorem cell19_434182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_434182 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434182 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434182 prefixEnd_434182 := by exact prefixLift 434182
  have htrace : WordTrace (prefixWord ++ tailWord_434182) baseStart_434182 baseEnd_434182 := by
    simpa [prefixWord, tailWord_434182, baseEnd_434182] using wordTrace_append hprefix tailTrace_434182
  have hstable : (prefixWord ++ tailWord_434182).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434182).length < 2 ^ (prefixWord ++ tailWord_434182).sum := by decide
  have hdescent : baseEnd_434182 < baseStart_434182 := by decide
  rcases family_descends (prefixWord ++ tailWord_434182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434262 : List Nat := [5, 2, 2, 1, 1, 1, 4, 3]
def baseStart_434262 : Nat := 118140960795 + 434262 * 2 ^ 59
def prefixEnd_434262 : Nat := 4983230072969 + 3 ^ 40 * 434262 * 2
def baseEnd_434262 : Nat := 132139339841709737260961

theorem tailTrace_434262 : CollatzResearch.WordTrace tailWord_434262 prefixEnd_434262 132139339841709737260961 := by
  unfold tailWord_434262
  simp only [CollatzResearch.WordTrace]
  refine ⟨989927272046900930628065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10559224235166943260032693 989927272046900930628065)
  ·
    refine ⟨742445454035175697971049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 989927272046900930628065 742445454035175697971049)
    ·
      refine ⟨556834090526381773478287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 742445454035175697971049 556834090526381773478287)
      ·
        refine ⟨835251135789572660217431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556834090526381773478287 835251135789572660217431)
        ·
          refine ⟨1252876703684358990326147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835251135789572660217431 1252876703684358990326147)
          ·
            refine ⟨1879315055526538485489221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252876703684358990326147 1879315055526538485489221)
            ·
              refine ⟨352371572911225966029229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1879315055526538485489221 352371572911225966029229)
              ·
                refine ⟨132139339841709737260961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352371572911225966029229 132139339841709737260961)
                ·
                  rfl

theorem cell19_434262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_434262 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434262 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434262 prefixEnd_434262 := by exact prefixLift 434262
  have htrace : WordTrace (prefixWord ++ tailWord_434262) baseStart_434262 baseEnd_434262 := by
    simpa [prefixWord, tailWord_434262, baseEnd_434262] using wordTrace_append hprefix tailTrace_434262
  have hstable : (prefixWord ++ tailWord_434262).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434262).length < 2 ^ (prefixWord ++ tailWord_434262).sum := by decide
  have hdescent : baseEnd_434262 < baseStart_434262 := by decide
  rcases family_descends (prefixWord ++ tailWord_434262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434287 : List Nat := [1, 1, 2, 1, 3, 6, 5]
def baseStart_434287 : Nat := 118140960795 + 434287 * 2 ^ 59
def prefixEnd_434287 : Nat := 4983230072969 + 3 ^ 40 * 434287 * 2
def baseEnd_434287 : Nat := 44048982320839028901779

theorem tailTrace_434287 : CollatzResearch.WordTrace tailWord_434287 prefixEnd_434287 44048982320839028901779 := by
  unfold tailWord_434287
  simp only [CollatzResearch.WordTrace]
  refine ⟨15839748177659844159709115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10559832118439896106472743 15839748177659844159709115)
  ·
    refine ⟨23759622266489766239563673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15839748177659844159709115 23759622266489766239563673)
    ·
      refine ⟨17819716699867324679672755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23759622266489766239563673 17819716699867324679672755)
      ·
        refine ⟨26729575049800987019509133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17819716699867324679672755 26729575049800987019509133)
        ·
          refine ⟨10023590643675370132315925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26729575049800987019509133 10023590643675370132315925)
          ·
            refine ⟨469855811422282974952309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10023590643675370132315925 469855811422282974952309)
            ·
              refine ⟨44048982320839028901779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 469855811422282974952309 44048982320839028901779)
              ·
                rfl

theorem cell19_434287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 5].length) (baseStart_434287 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434287 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434287 prefixEnd_434287 := by exact prefixLift 434287
  have htrace : WordTrace (prefixWord ++ tailWord_434287) baseStart_434287 baseEnd_434287 := by
    simpa [prefixWord, tailWord_434287, baseEnd_434287] using wordTrace_append hprefix tailTrace_434287
  have hstable : (prefixWord ++ tailWord_434287).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434287).length < 2 ^ (prefixWord ++ tailWord_434287).sum := by decide
  have hdescent : baseEnd_434287 < baseStart_434287 := by decide
  rcases family_descends (prefixWord ++ tailWord_434287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434357 : List Nat := [1, 3, 3, 4, 2, 1, 1, 4]
def baseStart_434357 : Nat := 118140960795 + 434357 * 2 ^ 59
def prefixEnd_434357 : Nat := 4983230072969 + 3 ^ 40 * 434357 * 2
def baseEnd_434357 : Nat := 132168246900777665149591

theorem tailTrace_434357 : CollatzResearch.WordTrace tailWord_434357 prefixEnd_434357 132168246900777665149591 := by
  unfold tailWord_434357
  simp only [CollatzResearch.WordTrace]
  refine ⟨15842301287406246114757325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10561534191604164076504883 15842301287406246114757325)
  ·
    refine ⟨5940862982777342293033997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15842301287406246114757325 5940862982777342293033997)
    ·
      refine ⟨2227823618541503359887749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5940862982777342293033997 2227823618541503359887749)
      ·
        refine ⟨417716928476531879978953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2227823618541503359887749 417716928476531879978953)
        ·
          refine ⟨313287696357398909984215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417716928476531879978953 313287696357398909984215)
          ·
            refine ⟨469931544536098364976323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313287696357398909984215 469931544536098364976323)
            ·
              refine ⟨704897316804147547464485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469931544536098364976323 704897316804147547464485)
              ·
                refine ⟨132168246900777665149591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 704897316804147547464485 132168246900777665149591)
                ·
                  rfl

theorem cell19_434357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 4].length) (baseStart_434357 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434357 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434357 prefixEnd_434357 := by exact prefixLift 434357
  have htrace : WordTrace (prefixWord ++ tailWord_434357) baseStart_434357 baseEnd_434357 := by
    simpa [prefixWord, tailWord_434357, baseEnd_434357] using wordTrace_append hprefix tailTrace_434357
  have hstable : (prefixWord ++ tailWord_434357).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434357).length < 2 ^ (prefixWord ++ tailWord_434357).sum := by decide
  have hdescent : baseEnd_434357 < baseStart_434357 := by decide
  rcases family_descends (prefixWord ++ tailWord_434357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434471 : List Nat := [1, 1, 8, 1, 1, 1, 2, 4]
def baseStart_434471 : Nat := 118140960795 + 434471 * 2 ^ 59
def prefixEnd_434471 : Nat := 4983230072969 + 3 ^ 40 * 434471 * 2
def baseEnd_434471 : Nat := 132202935371659178615947

theorem tailTrace_434471 : CollatzResearch.WordTrace tailWord_434471 prefixEnd_434471 132202935371659178615947 := by
  unfold tailWord_434471
  simp only [CollatzResearch.WordTrace]
  refine ⟨15846459208993243584407267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10564306139328829056271511 15846459208993243584407267)
  ·
    refine ⟨23769688813489865376610901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15846459208993243584407267 23769688813489865376610901)
    ·
      refine ⟨278551040783084359882159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 23769688813489865376610901 278551040783084359882159)
      ·
        refine ⟨417826561174626539823239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278551040783084359882159 417826561174626539823239)
        ·
          refine ⟨626739841761939809734859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417826561174626539823239 626739841761939809734859)
          ·
            refine ⟨940109762642909714602289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626739841761939809734859 940109762642909714602289)
            ·
              refine ⟨705082321982182285951717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 940109762642909714602289 705082321982182285951717)
              ·
                refine ⟨132202935371659178615947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 705082321982182285951717 132202935371659178615947)
                ·
                  rfl

theorem cell19_434471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 4].length) (baseStart_434471 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434471 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434471 prefixEnd_434471 := by exact prefixLift 434471
  have htrace : WordTrace (prefixWord ++ tailWord_434471) baseStart_434471 baseEnd_434471 := by
    simpa [prefixWord, tailWord_434471, baseEnd_434471] using wordTrace_append hprefix tailTrace_434471
  have hstable : (prefixWord ++ tailWord_434471).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434471).length < 2 ^ (prefixWord ++ tailWord_434471).sum := by decide
  have hdescent : baseEnd_434471 < baseStart_434471 := by decide
  rcases family_descends (prefixWord ++ tailWord_434471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434479 : List Nat := [1, 1, 2, 1, 2, 1, 5, 6]
def baseStart_434479 : Nat := 118140960795 + 434479 * 2 ^ 59
def prefixEnd_434479 : Nat := 4983230072969 + 3 ^ 40 * 434479 * 2
def baseEnd_434479 : Nat := 132205369650317530438147

theorem tailTrace_434479 : CollatzResearch.WordTrace tailWord_434479 prefixEnd_434479 132205369650317530438147 := by
  unfold tailWord_434479
  simp only [CollatzResearch.WordTrace]
  refine ⟨15846750992964260950698491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10564500661976173967132327 15846750992964260950698491)
  ·
    refine ⟨23770126489446391426047737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15846750992964260950698491 23770126489446391426047737)
    ·
      refine ⟨17827594867084793569535803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23770126489446391426047737 17827594867084793569535803)
      ·
        refine ⟨26741392300627190354303705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17827594867084793569535803 26741392300627190354303705)
        ·
          refine ⟨20056044225470392765727779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26741392300627190354303705 20056044225470392765727779)
          ·
            refine ⟨30084066338205589148591669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20056044225470392765727779 30084066338205589148591669)
            ·
              refine ⟨2820381219206773982680469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30084066338205589148591669 2820381219206773982680469)
              ·
                refine ⟨132205369650317530438147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2820381219206773982680469 132205369650317530438147)
                ·
                  rfl

theorem cell19_434479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 6].length) (baseStart_434479 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434479 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434479 prefixEnd_434479 := by exact prefixLift 434479
  have htrace : WordTrace (prefixWord ++ tailWord_434479) baseStart_434479 baseEnd_434479 := by
    simpa [prefixWord, tailWord_434479, baseEnd_434479] using wordTrace_append hprefix tailTrace_434479
  have hstable : (prefixWord ++ tailWord_434479).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434479).length < 2 ^ (prefixWord ++ tailWord_434479).sum := by decide
  have hdescent : baseEnd_434479 < baseStart_434479 := by decide
  rcases family_descends (prefixWord ++ tailWord_434479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434517 : List Nat := [1, 3, 2, 2, 11]
def baseStart_434517 : Nat := 118140960795 + 434517 * 2 ^ 59
def prefixEnd_434517 : Nat := 4983230072969 + 3 ^ 40 * 434517 * 2
def baseEnd_434517 : Nat := 4896923424960914873837

theorem tailTrace_434517 : CollatzResearch.WordTrace tailWord_434517 prefixEnd_434517 4896923424960914873837 := by
  unfold tailWord_434517
  simp only [CollatzResearch.WordTrace]
  refine ⟨15848136966826593440581805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10565424644551062293721203 15848136966826593440581805)
  ·
    refine ⟨5943051362559972540218177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15848136966826593440581805 5943051362559972540218177)
    ·
      refine ⟨4457288521919979405163633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5943051362559972540218177 4457288521919979405163633)
      ·
        refine ⟨3342966391439984553872725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4457288521919979405163633 3342966391439984553872725)
        ·
          refine ⟨4896923424960914873837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3342966391439984553872725 4896923424960914873837)
          ·
            rfl

theorem cell19_434517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 11].length) (baseStart_434517 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434517 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434517 prefixEnd_434517 := by exact prefixLift 434517
  have htrace : WordTrace (prefixWord ++ tailWord_434517) baseStart_434517 baseEnd_434517 := by
    simpa [prefixWord, tailWord_434517, baseEnd_434517] using wordTrace_append hprefix tailTrace_434517
  have hstable : (prefixWord ++ tailWord_434517).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434517).length < 2 ^ (prefixWord ++ tailWord_434517).sum := by decide
  have hdescent : baseEnd_434517 < baseStart_434517 := by decide
  rcases family_descends (prefixWord ++ tailWord_434517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434570 : List Nat := [3, 1, 2, 5, 1, 1, 6]
def baseStart_434570 : Nat := 118140960795 + 434570 * 2 ^ 59
def prefixEnd_434570 : Nat := 4983230072969 + 3 ^ 40 * 434570 * 2
def baseEnd_434570 : Nat := 44077686523352094138559

theorem tailTrace_434570 : CollatzResearch.WordTrace tailWord_434570 prefixEnd_434570 44077686523352094138559 := by
  unfold tailWord_434570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3962517508908645873065291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10566713357089722328174109 3962517508908645873065291)
  ·
    refine ⟨5943776263362968809597937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3962517508908645873065291 5943776263362968809597937)
    ·
      refine ⟨4457832197522226607198453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5943776263362968809597937 4457832197522226607198453)
      ·
        refine ⟨417921768517708744424855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4457832197522226607198453 417921768517708744424855)
        ·
          refine ⟨626882652776563116637283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417921768517708744424855 626882652776563116637283)
          ·
            refine ⟨940323979164844674955925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626882652776563116637283 940323979164844674955925)
            ·
              refine ⟨44077686523352094138559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 940323979164844674955925 44077686523352094138559)
              ·
                rfl

theorem cell19_434570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 6].length) (baseStart_434570 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434570 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434570 prefixEnd_434570 := by exact prefixLift 434570
  have htrace : WordTrace (prefixWord ++ tailWord_434570) baseStart_434570 baseEnd_434570 := by
    simpa [prefixWord, tailWord_434570, baseEnd_434570] using wordTrace_append hprefix tailTrace_434570
  have hstable : (prefixWord ++ tailWord_434570).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434570).length < 2 ^ (prefixWord ++ tailWord_434570).sum := by decide
  have hdescent : baseEnd_434570 < baseStart_434570 := by decide
  rcases family_descends (prefixWord ++ tailWord_434570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434602 : List Nat := [3, 1, 6, 1, 1, 2, 2, 3]
def baseStart_434602 : Nat := 118140960795 + 434602 * 2 ^ 59
def prefixEnd_434602 : Nat := 4983230072969 + 3 ^ 40 * 434602 * 2
def baseEnd_434602 : Nat := 132242796684689689704479

theorem tailTrace_434602 : CollatzResearch.WordTrace tailWord_434602 prefixEnd_434602 132242796684689689704479 := by
  unfold tailWord_434602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3962809292879663239356515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10567491447679101971617373 3962809292879663239356515)
  ·
    refine ⟨5944213939319494859034773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3962809292879663239356515 5944213939319494859034773)
    ·
      refine ⟨278635028405601321517255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5944213939319494859034773 278635028405601321517255)
      ·
        refine ⟨417952542608401982275883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278635028405601321517255 417952542608401982275883)
        ·
          refine ⟨626928813912602973413825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417952542608401982275883 626928813912602973413825)
          ·
            refine ⟨470196610434452230060369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 626928813912602973413825 470196610434452230060369)
            ·
              refine ⟨352647457825839172545277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470196610434452230060369 352647457825839172545277)
              ·
                refine ⟨132242796684689689704479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352647457825839172545277 132242796684689689704479)
                ·
                  rfl

theorem cell19_434602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_434602 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434602 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434602 prefixEnd_434602 := by exact prefixLift 434602
  have htrace : WordTrace (prefixWord ++ tailWord_434602) baseStart_434602 baseEnd_434602 := by
    simpa [prefixWord, tailWord_434602, baseEnd_434602] using wordTrace_append hprefix tailTrace_434602
  have hstable : (prefixWord ++ tailWord_434602).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434602).length < 2 ^ (prefixWord ++ tailWord_434602).sum := by decide
  have hdescent : baseEnd_434602 < baseStart_434602 := by decide
  rcases family_descends (prefixWord ++ tailWord_434602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434631 : List Nat := [1, 1, 4, 1, 1, 4, 7]
def baseStart_434631 : Nat := 118140960795 + 434631 * 2 ^ 59
def prefixEnd_434631 : Nat := 4983230072969 + 3 ^ 40 * 434631 * 2
def baseEnd_434631 : Nat := 44083873648275405019985

theorem tailTrace_434631 : CollatzResearch.WordTrace tailWord_434631 prefixEnd_434631 44083873648275405019985 := by
  unfold tailWord_434631
  simp only [CollatzResearch.WordTrace]
  refine ⟨15852294888413590910231747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10568196592275727273487831 15852294888413590910231747)
  ·
    refine ⟨23778442332620386365347621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15852294888413590910231747 23778442332620386365347621)
    ·
      refine ⟨4458457937366322443502679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23778442332620386365347621 4458457937366322443502679)
      ·
        refine ⟨6687686906049483665254019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4458457937366322443502679 6687686906049483665254019)
        ·
          refine ⟨10031530359074225497881029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6687686906049483665254019 10031530359074225497881029)
          ·
            refine ⟨1880911942326417280852693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10031530359074225497881029 1880911942326417280852693)
            ·
              refine ⟨44083873648275405019985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1880911942326417280852693 44083873648275405019985)
              ·
                rfl

theorem cell19_434631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 7].length) (baseStart_434631 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434631 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434631 prefixEnd_434631 := by exact prefixLift 434631
  have htrace : WordTrace (prefixWord ++ tailWord_434631) baseStart_434631 baseEnd_434631 := by
    simpa [prefixWord, tailWord_434631, baseEnd_434631] using wordTrace_append hprefix tailTrace_434631
  have hstable : (prefixWord ++ tailWord_434631).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434631).length < 2 ^ (prefixWord ++ tailWord_434631).sum := by decide
  have hdescent : baseEnd_434631 < baseStart_434631 := by decide
  rcases family_descends (prefixWord ++ tailWord_434631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434646 : List Nat := [5, 2, 1, 1, 1, 1, 4, 4]
def baseStart_434646 : Nat := 118140960795 + 434646 * 2 ^ 59
def prefixEnd_434646 : Nat := 4983230072969 + 3 ^ 40 * 434646 * 2
def baseEnd_434646 : Nat := 132256185217310624726581

theorem tailTrace_434646 : CollatzResearch.WordTrace tailWord_434646 prefixEnd_434646 132256185217310624726581 := by
  unfold tailWord_434646
  simp only [CollatzResearch.WordTrace]
  refine ⟨990802623959953029501737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10568561322239498981351861 990802623959953029501737)
  ·
    refine ⟨743101967969964772126303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 990802623959953029501737 743101967969964772126303)
    ·
      refine ⟨1114652951954947158189455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 743101967969964772126303 1114652951954947158189455)
      ·
        refine ⟨1671979427932420737284183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1114652951954947158189455 1671979427932420737284183)
        ·
          refine ⟨2507969141898631105926275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671979427932420737284183 2507969141898631105926275)
          ·
            refine ⟨3761953712847946658889413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2507969141898631105926275 3761953712847946658889413)
            ·
              refine ⟨705366321158989998541765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3761953712847946658889413 705366321158989998541765)
              ·
                refine ⟨132256185217310624726581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 705366321158989998541765 132256185217310624726581)
                ·
                  rfl

theorem cell19_434646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_434646 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434646 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434646 prefixEnd_434646 := by exact prefixLift 434646
  have htrace : WordTrace (prefixWord ++ tailWord_434646) baseStart_434646 baseEnd_434646 := by
    simpa [prefixWord, tailWord_434646, baseEnd_434646] using wordTrace_append hprefix tailTrace_434646
  have hstable : (prefixWord ++ tailWord_434646).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434646).length < 2 ^ (prefixWord ++ tailWord_434646).sum := by decide
  have hdescent : baseEnd_434646 < baseStart_434646 := by decide
  rcases family_descends (prefixWord ++ tailWord_434646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434701 : List Nat := [1, 7, 1, 1, 1, 1, 3, 4]
def baseStart_434701 : Nat := 118140960795 + 434701 * 2 ^ 59
def prefixEnd_434701 : Nat := 4983230072969 + 3 ^ 40 * 434701 * 2
def baseEnd_434701 : Nat := 132272920883086793504209

theorem tailTrace_434701 : CollatzResearch.WordTrace tailWord_434701 prefixEnd_434701 132272920883086793504209 := by
  unfold tailWord_434701
  simp only [CollatzResearch.WordTrace]
  refine ⟨15854847998159992865279957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10569898665439995243519971 15854847998159992865279957)
  ·
    refine ⟨371597999956874832779999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 15854847998159992865279957 371597999956874832779999)
    ·
      refine ⟨557396999935312249169999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 371597999956874832779999 557396999935312249169999)
      ·
        refine ⟨836095499902968373754999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557396999935312249169999 836095499902968373754999)
        ·
          refine ⟨1254143249854452560632499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836095499902968373754999 1254143249854452560632499)
          ·
            refine ⟨1881214874781678840948749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254143249854452560632499 1881214874781678840948749)
            ·
              refine ⟨705455578043129565355781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1881214874781678840948749 705455578043129565355781)
              ·
                refine ⟨132272920883086793504209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 705455578043129565355781 132272920883086793504209)
                ·
                  rfl

theorem cell19_434701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 4].length) (baseStart_434701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434701 prefixEnd_434701 := by exact prefixLift 434701
  have htrace : WordTrace (prefixWord ++ tailWord_434701) baseStart_434701 baseEnd_434701 := by
    simpa [prefixWord, tailWord_434701, baseEnd_434701] using wordTrace_append hprefix tailTrace_434701
  have hstable : (prefixWord ++ tailWord_434701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434701).length < 2 ^ (prefixWord ++ tailWord_434701).sum := by decide
  have hdescent : baseEnd_434701 < baseStart_434701 := by decide
  rcases family_descends (prefixWord ++ tailWord_434701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434745 : List Nat := [1, 2, 1, 5, 1, 1, 8]
def baseStart_434745 : Nat := 118140960795 + 434745 * 2 ^ 59
def prefixEnd_434745 : Nat := 4983230072969 + 3 ^ 40 * 434745 * 2
def baseEnd_434745 : Nat := 44095436471902576175437

theorem tailTrace_434745 : CollatzResearch.WordTrace tailWord_434745 prefixEnd_434745 44095436471902576175437 := by
  unfold tailWord_434745
  simp only [CollatzResearch.WordTrace]
  refine ⟨15856452810000588379881689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10570968540000392253254459 15856452810000588379881689)
  ·
    refine ⟨11892339607500441284911267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15856452810000588379881689 11892339607500441284911267)
    ·
      refine ⟨17838509411250661927366901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11892339607500441284911267 17838509411250661927366901)
      ·
        refine ⟨1672360257304749555690647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17838509411250661927366901 1672360257304749555690647)
        ·
          refine ⟨2508540385957124333535971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1672360257304749555690647 2508540385957124333535971)
          ·
            refine ⟨3762810578935686500303957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508540385957124333535971 3762810578935686500303957)
            ·
              refine ⟨44095436471902576175437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3762810578935686500303957 44095436471902576175437)
              ·
                rfl

theorem cell19_434745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 8].length) (baseStart_434745 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434745 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434745 prefixEnd_434745 := by exact prefixLift 434745
  have htrace : WordTrace (prefixWord ++ tailWord_434745) baseStart_434745 baseEnd_434745 := by
    simpa [prefixWord, tailWord_434745, baseEnd_434745] using wordTrace_append hprefix tailTrace_434745
  have hstable : (prefixWord ++ tailWord_434745).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434745).length < 2 ^ (prefixWord ++ tailWord_434745).sum := by decide
  have hdescent : baseEnd_434745 < baseStart_434745 := by decide
  rcases family_descends (prefixWord ++ tailWord_434745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434764 : List Nat := [2, 2, 1, 3, 1, 2, 2, 6]
def baseStart_434764 : Nat := 118140960795 + 434764 * 2 ^ 59
def prefixEnd_434764 : Nat := 4983230072969 + 3 ^ 40 * 434764 * 2
def baseEnd_434764 : Nat := 132292090827521314104037

theorem tailTrace_434764 : CollatzResearch.WordTrace tailWord_434764 prefixEnd_434764 132292090827521314104037 := by
  unfold tailWord_434764
  simp only [CollatzResearch.WordTrace]
  refine ⟨7928572898465877312411673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10571430531287836416548897 7928572898465877312411673)
  ·
    refine ⟨5946429673849407984308755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7928572898465877312411673 5946429673849407984308755)
    ·
      refine ⟨8919644510774111976463133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5946429673849407984308755 8919644510774111976463133)
      ·
        refine ⟨3344866691540291991173675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8919644510774111976463133 3344866691540291991173675)
        ·
          refine ⟨5017300037310437986760513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3344866691540291991173675 5017300037310437986760513)
          ·
            refine ⟨3762975027982828490070385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5017300037310437986760513 3762975027982828490070385)
            ·
              refine ⟨2822231270987121367552789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3762975027982828490070385 2822231270987121367552789)
              ·
                refine ⟨132292090827521314104037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2822231270987121367552789 132292090827521314104037)
                ·
                  rfl

theorem cell19_434764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_434764 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434764 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434764 prefixEnd_434764 := by exact prefixLift 434764
  have htrace : WordTrace (prefixWord ++ tailWord_434764) baseStart_434764 baseEnd_434764 := by
    simpa [prefixWord, tailWord_434764, baseEnd_434764] using wordTrace_append hprefix tailTrace_434764
  have hstable : (prefixWord ++ tailWord_434764).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434764).length < 2 ^ (prefixWord ++ tailWord_434764).sum := by decide
  have hdescent : baseEnd_434764 < baseStart_434764 := by decide
  rcases family_descends (prefixWord ++ tailWord_434764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434800 : List Nat := [2, 1, 1, 1, 7, 2, 5]
def baseStart_434800 : Nat := 118140960795 + 434800 * 2 ^ 59
def prefixEnd_434800 : Nat := 4983230072969 + 3 ^ 40 * 434800 * 2
def baseEnd_434800 : Nat := 44101015027161299101313

theorem tailTrace_434800 : CollatzResearch.WordTrace tailWord_434800 prefixEnd_434800 44101015027161299101313 := by
  unfold tailWord_434800
  simp only [CollatzResearch.WordTrace]
  refine ⟨7929229412400666386566927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10572305883200888515422569 7929229412400666386566927)
  ·
    refine ⟨11893844118600999579850391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7929229412400666386566927 11893844118600999579850391)
    ·
      refine ⟨17840766177901499369775587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11893844118600999579850391 17840766177901499369775587)
      ·
        refine ⟨26761149266852249054663381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17840766177901499369775587 26761149266852249054663381)
        ·
          refine ⟨627214435941849587218673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 26761149266852249054663381 627214435941849587218673)
          ·
            refine ⟨470410826956387190414005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 627214435941849587218673 470410826956387190414005)
            ·
              refine ⟨44101015027161299101313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 470410826956387190414005 44101015027161299101313)
              ·
                rfl

theorem cell19_434800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 5].length) (baseStart_434800 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434800 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434800 prefixEnd_434800 := by exact prefixLift 434800
  have htrace : WordTrace (prefixWord ++ tailWord_434800) baseStart_434800 baseEnd_434800 := by
    simpa [prefixWord, tailWord_434800, baseEnd_434800] using wordTrace_append hprefix tailTrace_434800
  have hstable : (prefixWord ++ tailWord_434800).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434800).length < 2 ^ (prefixWord ++ tailWord_434800).sum := by decide
  have hdescent : baseEnd_434800 < baseStart_434800 := by decide
  rcases family_descends (prefixWord ++ tailWord_434800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434821 : List Nat := [1, 3, 1, 1, 4, 2, 1, 6]
def baseStart_434821 : Nat := 118140960795 + 434821 * 2 ^ 59
def prefixEnd_434821 : Nat := 4983230072969 + 3 ^ 40 * 434821 * 2
def baseEnd_434821 : Nat := 132309435062962070837215

theorem tailTrace_434821 : CollatzResearch.WordTrace tailWord_434821 prefixEnd_434821 132309435062962070837215 := by
  unfold tailWord_434821
  simp only [CollatzResearch.WordTrace]
  refine ⟨15859224757725253359648317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10572816505150168906432211 15859224757725253359648317)
  ·
    refine ⟨5947209284146970009868119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15859224757725253359648317 5947209284146970009868119)
    ·
      refine ⟨8920813926220455014802179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5947209284146970009868119 8920813926220455014802179)
      ·
        refine ⟨13381220889330682522203269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8920813926220455014802179 13381220889330682522203269)
        ·
          refine ⟨2508978916749502972913113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13381220889330682522203269 2508978916749502972913113)
          ·
            refine ⟨1881734187562127229684835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2508978916749502972913113 1881734187562127229684835)
            ·
              refine ⟨2822601281343190844527253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881734187562127229684835 2822601281343190844527253)
              ·
                refine ⟨132309435062962070837215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2822601281343190844527253 132309435062962070837215)
                ·
                  rfl

theorem cell19_434821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 6].length) (baseStart_434821 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434821 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434821 prefixEnd_434821 := by exact prefixLift 434821
  have htrace : WordTrace (prefixWord ++ tailWord_434821) baseStart_434821 baseEnd_434821 := by
    simpa [prefixWord, tailWord_434821, baseEnd_434821] using wordTrace_append hprefix tailTrace_434821
  have hstable : (prefixWord ++ tailWord_434821).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434821).length < 2 ^ (prefixWord ++ tailWord_434821).sum := by decide
  have hdescent : baseEnd_434821 < baseStart_434821 := by decide
  rcases family_descends (prefixWord ++ tailWord_434821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434840 : List Nat := [2, 1, 2, 4, 1, 1, 1, 7]
def baseStart_434840 : Nat := 118140960795 + 434840 * 2 ^ 59
def prefixEnd_434840 : Nat := 4983230072969 + 3 ^ 40 * 434840 * 2
def baseEnd_434840 : Nat := 132315216474775656414941

theorem tailTrace_434840 : CollatzResearch.WordTrace tailWord_434840 prefixEnd_434840 132315216474775656414941 := by
  unfold tailWord_434840
  simp only [CollatzResearch.WordTrace]
  refine ⟨7929958872328209802294987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10573278496437613069726649 7929958872328209802294987)
  ·
    refine ⟨11894938308492314703442481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7929958872328209802294987 11894938308492314703442481)
    ·
      refine ⟨8921203731369236027581861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11894938308492314703442481 8921203731369236027581861)
      ·
        refine ⟨1672725699631731755171599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8921203731369236027581861 1672725699631731755171599)
        ·
          refine ⟨2509088549447597632757399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1672725699631731755171599 2509088549447597632757399)
          ·
            refine ⟨3763632824171396449136099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2509088549447597632757399 3763632824171396449136099)
            ·
              refine ⟨5645449236257094673704149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3763632824171396449136099 5645449236257094673704149)
              ·
                refine ⟨132315216474775656414941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5645449236257094673704149 132315216474775656414941)
                ·
                  rfl

theorem cell19_434840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_434840 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434840 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434840 prefixEnd_434840 := by exact prefixLift 434840
  have htrace : WordTrace (prefixWord ++ tailWord_434840) baseStart_434840 baseEnd_434840 := by
    simpa [prefixWord, tailWord_434840, baseEnd_434840] using wordTrace_append hprefix tailTrace_434840
  have hstable : (prefixWord ++ tailWord_434840).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434840).length < 2 ^ (prefixWord ++ tailWord_434840).sum := by decide
  have hdescent : baseEnd_434840 < baseStart_434840 := by decide
  rcases family_descends (prefixWord ++ tailWord_434840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434855 : List Nat := [1, 1, 6, 3, 2, 6]
def baseStart_434855 : Nat := 118140960795 + 434855 * 2 ^ 59
def prefixEnd_434855 : Nat := 4983230072969 + 3 ^ 40 * 434855 * 2
def baseEnd_434855 : Nat := 14702197860806674009063

theorem tailTrace_434855 : CollatzResearch.WordTrace tailWord_434855 prefixEnd_434855 14702197860806674009063 := by
  unfold tailWord_434855
  simp only [CollatzResearch.WordTrace]
  refine ⟨15860464839602077166386019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10573643226401384777590679 15860464839602077166386019)
  ·
    refine ⟨23790697259403115749579029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15860464839602077166386019 23790697259403115749579029)
    ·
      refine ⟨1115188934034521050761517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23790697259403115749579029 1115188934034521050761517)
      ·
        refine ⟨418195850262945394035569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1115188934034521050761517 418195850262945394035569)
        ·
          refine ⟨313646887697209045526677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418195850262945394035569 313646887697209045526677)
          ·
            refine ⟨14702197860806674009063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 313646887697209045526677 14702197860806674009063)
            ·
              rfl

theorem cell19_434855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 6].length) (baseStart_434855 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434855 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434855 prefixEnd_434855 := by exact prefixLift 434855
  have htrace : WordTrace (prefixWord ++ tailWord_434855) baseStart_434855 baseEnd_434855 := by
    simpa [prefixWord, tailWord_434855, baseEnd_434855] using wordTrace_append hprefix tailTrace_434855
  have hstable : (prefixWord ++ tailWord_434855).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434855).length < 2 ^ (prefixWord ++ tailWord_434855).sum := by decide
  have hdescent : baseEnd_434855 < baseStart_434855 := by decide
  rcases family_descends (prefixWord ++ tailWord_434855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434870 : List Nat := [5, 1, 3, 1, 3, 1, 1, 4]
def baseStart_434870 : Nat := 118140960795 + 434870 * 2 ^ 59
def prefixEnd_434870 : Nat := 4983230072969 + 3 ^ 40 * 434870 * 2
def baseEnd_434870 : Nat := 132324345019744475748193

theorem tailTrace_434870 : CollatzResearch.WordTrace tailWord_434870 prefixEnd_434870 132324345019744475748193 := by
  unfold tailWord_434870
  simp only [CollatzResearch.WordTrace]
  refine ⟨991313245909233420511379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10574007956365156485454709 991313245909233420511379)
  ·
    refine ⟨1486969868863850130767069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 991313245909233420511379 1486969868863850130767069)
    ·
      refine ⟨557613700823943799037651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1486969868863850130767069 557613700823943799037651)
      ·
        refine ⟨836420551235915698556477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557613700823943799037651 836420551235915698556477)
        ·
          refine ⟨313657706713468386958679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 836420551235915698556477 313657706713468386958679)
          ·
            refine ⟨470486560070202580438019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313657706713468386958679 470486560070202580438019)
            ·
              refine ⟨705729840105303870657029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470486560070202580438019 705729840105303870657029)
              ·
                refine ⟨132324345019744475748193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 705729840105303870657029 132324345019744475748193)
                ·
                  rfl

theorem cell19_434870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_434870 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434870 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434870 prefixEnd_434870 := by exact prefixLift 434870
  have htrace : WordTrace (prefixWord ++ tailWord_434870) baseStart_434870 baseEnd_434870 := by
    simpa [prefixWord, tailWord_434870, baseEnd_434870] using wordTrace_append hprefix tailTrace_434870
  have hstable : (prefixWord ++ tailWord_434870).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434870).length < 2 ^ (prefixWord ++ tailWord_434870).sum := by decide
  have hdescent : baseEnd_434870 < baseStart_434870 := by decide
  rcases family_descends (prefixWord ++ tailWord_434870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434916 : List Nat := [2, 3, 1, 1, 1, 5, 6]
def baseStart_434916 : Nat := 118140960795 + 434916 * 2 ^ 59
def prefixEnd_434916 : Nat := 4983230072969 + 3 ^ 40 * 434916 * 2
def baseEnd_434916 : Nat := 44112780707343332908615

theorem tailTrace_434916 : CollatzResearch.WordTrace tailWord_434916 prefixEnd_434916 44112780707343332908615 := by
  unfold tailWord_434916
  simp only [CollatzResearch.WordTrace]
  refine ⟨7931344846190542292178301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10575126461587389722904401 7931344846190542292178301)
  ·
    refine ⟨2974254317321453359566863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7931344846190542292178301 2974254317321453359566863)
    ·
      refine ⟨4461381475982180039350295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2974254317321453359566863 4461381475982180039350295)
      ·
        refine ⟨6692072213973270059025443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4461381475982180039350295 6692072213973270059025443)
        ·
          refine ⟨10038108320959905088538165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6692072213973270059025443 10038108320959905088538165)
          ·
            refine ⟨941072655089991102050453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10038108320959905088538165 941072655089991102050453)
            ·
              refine ⟨44112780707343332908615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 941072655089991102050453 44112780707343332908615)
              ·
                rfl

theorem cell19_434916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 6].length) (baseStart_434916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434916 prefixEnd_434916 := by exact prefixLift 434916
  have htrace : WordTrace (prefixWord ++ tailWord_434916) baseStart_434916 baseEnd_434916 := by
    simpa [prefixWord, tailWord_434916, baseEnd_434916] using wordTrace_append hprefix tailTrace_434916
  have hstable : (prefixWord ++ tailWord_434916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434916).length < 2 ^ (prefixWord ++ tailWord_434916).sum := by decide
  have hdescent : baseEnd_434916 < baseStart_434916 := by decide
  rcases family_descends (prefixWord ++ tailWord_434916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434952 : List Nat := [2, 1, 3, 2, 2, 2, 4, 3]
def baseStart_434952 : Nat := 118140960795 + 434952 * 2 ^ 59
def prefixEnd_434952 : Nat := 4983230072969 + 3 ^ 40 * 434952 * 2
def baseEnd_434952 : Nat := 132349296375992581925747

theorem tailTrace_434952 : CollatzResearch.WordTrace tailWord_434952 prefixEnd_434952 132349296375992581925747 := by
  unfold tailWord_434952
  simp only [CollatzResearch.WordTrace]
  refine ⟨7932001360125331366333555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10576001813500441821778073 7932001360125331366333555)
  ·
    refine ⟨11898002040187997049500333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7932001360125331366333555 11898002040187997049500333)
    ·
      refine ⟨4461750765070498893562625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11898002040187997049500333 4461750765070498893562625)
      ·
        refine ⟨3346313073802874170171969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4461750765070498893562625 3346313073802874170171969)
        ·
          refine ⟨2509734805352155627628977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3346313073802874170171969 2509734805352155627628977)
          ·
            refine ⟨1882301104014116720721733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2509734805352155627628977 1882301104014116720721733)
            ·
              refine ⟨352931457002646885135325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1882301104014116720721733 352931457002646885135325)
              ·
                refine ⟨132349296375992581925747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352931457002646885135325 132349296375992581925747)
                ·
                  rfl

theorem cell19_434952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_434952 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434952 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434952 prefixEnd_434952 := by exact prefixLift 434952
  have htrace : WordTrace (prefixWord ++ tailWord_434952) baseStart_434952 baseEnd_434952 := by
    simpa [prefixWord, tailWord_434952, baseEnd_434952] using wordTrace_append hprefix tailTrace_434952
  have hstable : (prefixWord ++ tailWord_434952).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434952).length < 2 ^ (prefixWord ++ tailWord_434952).sum := by decide
  have hdescent : baseEnd_434952 < baseStart_434952 := by decide
  rcases family_descends (prefixWord ++ tailWord_434952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434954 : List Nat := [3, 1, 2, 2, 1, 2, 3, 5]
def baseStart_434954 : Nat := 118140960795 + 434954 * 2 ^ 59
def prefixEnd_434954 : Nat := 4983230072969 + 3 ^ 40 * 434954 * 2
def baseEnd_434954 : Nat := 132349904945657169881297

theorem tailTrace_434954 : CollatzResearch.WordTrace tailWord_434954 prefixEnd_434954 132349904945657169881297 := by
  unfold tailWord_434954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3966018916560854268559979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10576050444162278049493277 3966018916560854268559979)
  ·
    refine ⟨5949028374841281402839969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3966018916560854268559979 5949028374841281402839969)
    ·
      refine ⟨4461771281130961052129977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5949028374841281402839969 4461771281130961052129977)
      ·
        refine ⟨3346328460848220789097483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4461771281130961052129977 3346328460848220789097483)
        ·
          refine ⟨5019492691272331183646225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3346328460848220789097483 5019492691272331183646225)
          ·
            refine ⟨3764619518454248387734669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5019492691272331183646225 3764619518454248387734669)
            ·
              refine ⟨1411732319420343145400501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3764619518454248387734669 1411732319420343145400501)
              ·
                refine ⟨132349904945657169881297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1411732319420343145400501 132349904945657169881297)
                ·
                  rfl

theorem cell19_434954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_434954 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434954 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434954 prefixEnd_434954 := by exact prefixLift 434954
  have htrace : WordTrace (prefixWord ++ tailWord_434954) baseStart_434954 baseEnd_434954 := by
    simpa [prefixWord, tailWord_434954, baseEnd_434954] using wordTrace_append hprefix tailTrace_434954
  have hstable : (prefixWord ++ tailWord_434954).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434954).length < 2 ^ (prefixWord ++ tailWord_434954).sum := by decide
  have hdescent : baseEnd_434954 < baseStart_434954 := by decide
  rcases family_descends (prefixWord ++ tailWord_434954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_434990 : List Nat := [4, 1, 3, 2, 1, 1, 1, 6]
def baseStart_434990 : Nat := 118140960795 + 434990 * 2 ^ 59
def prefixEnd_434990 : Nat := 4983230072969 + 3 ^ 40 * 434990 * 2
def baseEnd_434990 : Nat := 132360859199619753081199

theorem tailTrace_434990 : CollatzResearch.WordTrace tailWord_434990 prefixEnd_434990 132360859199619753081199 := by
  unfold tailWord_434990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1983173586764124402818803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10576925796075330148366949 1983173586764124402818803)
  ·
    refine ⟨2974760380146186604228205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1983173586764124402818803 2974760380146186604228205)
    ·
      refine ⟨1115535142554819976585577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2974760380146186604228205 1115535142554819976585577)
      ·
        refine ⟨836651356916114982439183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1115535142554819976585577 836651356916114982439183)
        ·
          refine ⟨1254977035374172473658775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836651356916114982439183 1254977035374172473658775)
          ·
            refine ⟨1882465553061258710488163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254977035374172473658775 1882465553061258710488163)
            ·
              refine ⟨2823698329591888065732245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882465553061258710488163 2823698329591888065732245)
              ·
                refine ⟨132360859199619753081199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2823698329591888065732245 132360859199619753081199)
                ·
                  rfl

theorem cell19_434990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_434990 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_434990 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_434990 prefixEnd_434990 := by exact prefixLift 434990
  have htrace : WordTrace (prefixWord ++ tailWord_434990) baseStart_434990 baseEnd_434990 := by
    simpa [prefixWord, tailWord_434990, baseEnd_434990] using wordTrace_append hprefix tailTrace_434990
  have hstable : (prefixWord ++ tailWord_434990).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_434990).length < 2 ^ (prefixWord ++ tailWord_434990).sum := by decide
  have hdescent : baseEnd_434990 < baseStart_434990 := by decide
  rcases family_descends (prefixWord ++ tailWord_434990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435028 : List Nat := [2, 4, 1, 1, 5, 6]
def baseStart_435028 : Nat := 118140960795 + 435028 * 2 ^ 59
def prefixEnd_435028 : Nat := 4983230072969 + 3 ^ 40 * 435028 * 2
def baseEnd_435028 : Nat := 14708046891471880470739

theorem tailTrace_435028 : CollatzResearch.WordTrace tailWord_435028 prefixEnd_435028 14708046891471880470739 := by
  unfold tailWord_435028
  simp only [CollatzResearch.WordTrace]
  refine ⟨7933387333987663856216869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10577849778650218474955825 7933387333987663856216869)
  ·
    refine ⟨1487510125122686973040663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7933387333987663856216869 1487510125122686973040663)
    ·
      refine ⟨2231265187684030459560995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1487510125122686973040663 2231265187684030459560995)
      ·
        refine ⟨3346897781526045689341493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2231265187684030459560995 3346897781526045689341493)
        ·
          refine ⟨313771667018066783375765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3346897781526045689341493 313771667018066783375765)
          ·
            refine ⟨14708046891471880470739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 313771667018066783375765 14708046891471880470739)
            ·
              rfl

theorem cell19_435028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 6].length) (baseStart_435028 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435028 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435028 prefixEnd_435028 := by exact prefixLift 435028
  have htrace : WordTrace (prefixWord ++ tailWord_435028) baseStart_435028 baseEnd_435028 := by
    simpa [prefixWord, tailWord_435028, baseEnd_435028] using wordTrace_append hprefix tailTrace_435028
  have hstable : (prefixWord ++ tailWord_435028).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435028).length < 2 ^ (prefixWord ++ tailWord_435028).sum := by decide
  have hdescent : baseEnd_435028 < baseStart_435028 := by decide
  rcases family_descends (prefixWord ++ tailWord_435028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435030 : List Nat := [5, 2, 12]
def baseStart_435030 : Nat := 118140960795 + 435030 * 2 ^ 59
def prefixEnd_435030 : Nat := 4983230072969 + 3 ^ 40 * 435030 * 2
def baseEnd_435030 : Nat := 544744981863833383507

theorem tailTrace_435030 : CollatzResearch.WordTrace tailWord_435030 prefixEnd_435030 544744981863833383507 := by
  unfold tailWord_435030
  simp only [CollatzResearch.WordTrace]
  refine ⟨991677975873005128375409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10577898409312054702671029 991677975873005128375409)
  ·
    refine ⟨743758481904753846281557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 991677975873005128375409 743758481904753846281557)
    ·
      refine ⟨544744981863833383507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 12 743758481904753846281557 544744981863833383507)
      ·
        rfl

theorem cell19_435030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 12].length) (baseStart_435030 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435030 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435030 prefixEnd_435030 := by exact prefixLift 435030
  have htrace : WordTrace (prefixWord ++ tailWord_435030) baseStart_435030 baseEnd_435030 := by
    simpa [prefixWord, tailWord_435030, baseEnd_435030] using wordTrace_append hprefix tailTrace_435030
  have hstable : (prefixWord ++ tailWord_435030).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435030).length < 2 ^ (prefixWord ++ tailWord_435030).sum := by decide
  have hdescent : baseEnd_435030 < baseStart_435030 := by decide
  rcases family_descends (prefixWord ++ tailWord_435030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435047 : List Nat := [1, 1, 5, 1, 2, 4, 1, 4]
def baseStart_435047 : Nat := 118140960795 + 435047 * 2 ^ 59
def prefixEnd_435047 : Nat := 4983230072969 + 3 ^ 40 * 435047 * 2
def baseEnd_435047 : Nat := 132378203435060509814377

theorem tailTrace_435047 : CollatzResearch.WordTrace tailWord_435047 prefixEnd_435047 132378203435060509814377 := by
  unfold tailWord_435047
  simp only [CollatzResearch.WordTrace]
  refine ⟨15867467654906493957375395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10578311769937662638250263 15867467654906493957375395)
  ·
    refine ⟨23801201482359740936063093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15867467654906493957375395 23801201482359740936063093)
    ·
      refine ⟨2231362638971225712755915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23801201482359740936063093 2231362638971225712755915)
      ·
        refine ⟨3347043958456838569133873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2231362638971225712755915 3347043958456838569133873)
        ·
          refine ⟨2510282968842628926850405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3347043958456838569133873 2510282968842628926850405)
          ·
            refine ⟨470678056657992923784451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2510282968842628926850405 470678056657992923784451)
            ·
              refine ⟨706017084986989385676677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470678056657992923784451 706017084986989385676677)
              ·
                refine ⟨132378203435060509814377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 706017084986989385676677 132378203435060509814377)
                ·
                  rfl

theorem cell19_435047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 4].length) (baseStart_435047 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435047 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435047 prefixEnd_435047 := by exact prefixLift 435047
  have htrace : WordTrace (prefixWord ++ tailWord_435047) baseStart_435047 baseEnd_435047 := by
    simpa [prefixWord, tailWord_435047, baseEnd_435047] using wordTrace_append hprefix tailTrace_435047
  have hstable : (prefixWord ++ tailWord_435047).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435047).length < 2 ^ (prefixWord ++ tailWord_435047).sum := by decide
  have hdescent : baseEnd_435047 < baseStart_435047 := by decide
  rcases family_descends (prefixWord ++ tailWord_435047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435117 : List Nat := [1, 5, 2, 3, 2, 1, 2, 3]
def baseStart_435117 : Nat := 118140960795 + 435117 * 2 ^ 59
def prefixEnd_435117 : Nat := 4983230072969 + 3 ^ 40 * 435117 * 2
def baseEnd_435117 : Nat := 132399503373321088258631

theorem tailTrace_435117 : CollatzResearch.WordTrace tailWord_435117 prefixEnd_435117 132399503373321088258631 := by
  unfold tailWord_435117
  simp only [CollatzResearch.WordTrace]
  refine ⟨15870020764652895912423605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10580013843101930608282403 15870020764652895912423605)
  ·
    refine ⟨1487814446686208991789713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15870020764652895912423605 1487814446686208991789713)
    ·
      refine ⟨1115860835014656743842285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1487814446686208991789713 1115860835014656743842285)
      ·
        refine ⟨418447813130496278940857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1115860835014656743842285 418447813130496278940857)
        ·
          refine ⟨313835859847872209205643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 418447813130496278940857 313835859847872209205643)
          ·
            refine ⟨470753789771808313808465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313835859847872209205643 470753789771808313808465)
            ·
              refine ⟨353065342328856235356349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470753789771808313808465 353065342328856235356349)
              ·
                refine ⟨132399503373321088258631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353065342328856235356349 132399503373321088258631)
                ·
                  rfl

theorem cell19_435117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 2, 3].length) (baseStart_435117 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435117 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435117 prefixEnd_435117 := by exact prefixLift 435117
  have htrace : WordTrace (prefixWord ++ tailWord_435117) baseStart_435117 baseEnd_435117 := by
    simpa [prefixWord, tailWord_435117, baseEnd_435117] using wordTrace_append hprefix tailTrace_435117
  have hstable : (prefixWord ++ tailWord_435117).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435117).length < 2 ^ (prefixWord ++ tailWord_435117).sum := by decide
  have hdescent : baseEnd_435117 < baseStart_435117 := by decide
  rcases family_descends (prefixWord ++ tailWord_435117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435121 : List Nat := [1, 2, 2, 4, 3, 2, 2, 3]
def baseStart_435121 : Nat := 118140960795 + 435121 * 2 ^ 59
def prefixEnd_435121 : Nat := 4983230072969 + 3 ^ 40 * 435121 * 2
def baseEnd_435121 : Nat := 132400720512650264169731

theorem tailTrace_435121 : CollatzResearch.WordTrace tailWord_435121 prefixEnd_435121 132400720512650264169731 := by
  unfold tailWord_435121
  simp only [CollatzResearch.WordTrace]
  refine ⟨15870166656638404595569217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10580111104425603063712811 15870166656638404595569217)
  ·
    refine ⟨11902624992478803446676913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15870166656638404595569217 11902624992478803446676913)
    ·
      refine ⟨8926968744359102585007685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11902624992478803446676913 8926968744359102585007685)
      ·
        refine ⟨1673806639567331734688941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8926968744359102585007685 1673806639567331734688941)
        ·
          refine ⟨627677489837749400508353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1673806639567331734688941 627677489837749400508353)
          ·
            refine ⟨470758117378312050381265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 627677489837749400508353 470758117378312050381265)
            ·
              refine ⟨353068588033734037785949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470758117378312050381265 353068588033734037785949)
              ·
                refine ⟨132400720512650264169731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353068588033734037785949 132400720512650264169731)
                ·
                  rfl

theorem cell19_435121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 3].length) (baseStart_435121 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435121 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435121 prefixEnd_435121 := by exact prefixLift 435121
  have htrace : WordTrace (prefixWord ++ tailWord_435121) baseStart_435121 baseEnd_435121 := by
    simpa [prefixWord, tailWord_435121, baseEnd_435121] using wordTrace_append hprefix tailTrace_435121
  have hstable : (prefixWord ++ tailWord_435121).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435121).length < 2 ^ (prefixWord ++ tailWord_435121).sum := by decide
  have hdescent : baseEnd_435121 < baseStart_435121 := by decide
  rcases family_descends (prefixWord ++ tailWord_435121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435125 : List Nat := [1, 3, 3, 2, 1, 1, 3, 5]
def baseStart_435125 : Nat := 118140960795 + 435125 * 2 ^ 59
def prefixEnd_435125 : Nat := 4983230072969 + 3 ^ 40 * 435125 * 2
def baseEnd_435125 : Nat := 132401937651979440080831

theorem tailTrace_435125 : CollatzResearch.WordTrace tailWord_435125 prefixEnd_435125 132401937651979440080831 := by
  unfold tailWord_435125
  simp only [CollatzResearch.WordTrace]
  refine ⟨15870312548623913278714829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10580208365749275519143219 15870312548623913278714829)
  ·
    refine ⟨5951367205733967479518061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15870312548623913278714829 5951367205733967479518061)
    ·
      refine ⟨2231762702150237804819273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5951367205733967479518061 2231762702150237804819273)
      ·
        refine ⟨1673822026612678353614455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2231762702150237804819273 1673822026612678353614455)
        ·
          refine ⟨2510733039919017530421683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1673822026612678353614455 2510733039919017530421683)
          ·
            refine ⟨3766099559878526295632525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510733039919017530421683 3766099559878526295632525)
            ·
              refine ⟨1412287334954447360862197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3766099559878526295632525 1412287334954447360862197)
              ·
                refine ⟨132401937651979440080831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1412287334954447360862197 132401937651979440080831)
                ·
                  rfl

theorem cell19_435125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_435125 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435125 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435125 prefixEnd_435125 := by exact prefixLift 435125
  have htrace : WordTrace (prefixWord ++ tailWord_435125) baseStart_435125 baseEnd_435125 := by
    simpa [prefixWord, tailWord_435125, baseEnd_435125] using wordTrace_append hprefix tailTrace_435125
  have hstable : (prefixWord ++ tailWord_435125).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435125).length < 2 ^ (prefixWord ++ tailWord_435125).sum := by decide
  have hdescent : baseEnd_435125 < baseStart_435125 := by decide
  rcases family_descends (prefixWord ++ tailWord_435125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435140 : List Nat := [2, 3, 3, 3, 1, 2, 5]
def baseStart_435140 : Nat := 118140960795 + 435140 * 2 ^ 59
def prefixEnd_435140 : Nat := 4983230072969 + 3 ^ 40 * 435140 * 2
def baseEnd_435140 : Nat := 44135500641487949915819

theorem tailTrace_435140 : CollatzResearch.WordTrace tailWord_435140 prefixEnd_435140 44135500641487949915819 := by
  unfold tailWord_435140
  simp only [CollatzResearch.WordTrace]
  refine ⟨7935429821784785420255437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10580573095713047227007249 7935429821784785420255437)
  ·
    refine ⟨2975786183169294532595789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7935429821784785420255437 2975786183169294532595789)
    ·
      refine ⟨1115919818688485449723421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2975786183169294532595789 1115919818688485449723421)
      ·
        refine ⟨418469932008182043646283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1115919818688485449723421 418469932008182043646283)
        ·
          refine ⟨627704898012273065469425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418469932008182043646283 627704898012273065469425)
          ·
            refine ⟨470778673509204799102069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 627704898012273065469425 470778673509204799102069)
            ·
              refine ⟨44135500641487949915819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 470778673509204799102069 44135500641487949915819)
              ·
                rfl

theorem cell19_435140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 5].length) (baseStart_435140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435140 prefixEnd_435140 := by exact prefixLift 435140
  have htrace : WordTrace (prefixWord ++ tailWord_435140) baseStart_435140 baseEnd_435140 := by
    simpa [prefixWord, tailWord_435140, baseEnd_435140] using wordTrace_append hprefix tailTrace_435140
  have hstable : (prefixWord ++ tailWord_435140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435140).length < 2 ^ (prefixWord ++ tailWord_435140).sum := by decide
  have hdescent : baseEnd_435140 < baseStart_435140 := by decide
  rcases family_descends (prefixWord ++ tailWord_435140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435429 : List Nat := [1, 3, 1, 4, 3, 1, 6]
def baseStart_435429 : Nat := 118140960795 + 435429 * 2 ^ 59
def prefixEnd_435429 : Nat := 4983230072969 + 3 ^ 40 * 435429 * 2
def baseEnd_435429 : Nat := 44164813413665603108149

theorem tailTrace_435429 : CollatzResearch.WordTrace tailWord_435429 prefixEnd_435429 44164813413665603108149 := by
  unfold tailWord_435429
  simp only [CollatzResearch.WordTrace]
  refine ⟨15881400339522573197781341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10587600226348382131854227 15881400339522573197781341)
  ·
    refine ⟨5955525127320964949168003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15881400339522573197781341 5955525127320964949168003)
    ·
      refine ⟨8933287690981447423752005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5955525127320964949168003 8933287690981447423752005)
      ·
        refine ⟨1674991442059021391953501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8933287690981447423752005 1674991442059021391953501)
        ·
          refine ⟨628121790772133021982563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1674991442059021391953501 628121790772133021982563)
          ·
            refine ⟨942182686158199532973845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 628121790772133021982563 942182686158199532973845)
            ·
              refine ⟨44164813413665603108149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 942182686158199532973845 44164813413665603108149)
              ·
                rfl

theorem cell19_435429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 6].length) (baseStart_435429 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435429 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435429 prefixEnd_435429 := by exact prefixLift 435429
  have htrace : WordTrace (prefixWord ++ tailWord_435429) baseStart_435429 baseEnd_435429 := by
    simpa [prefixWord, tailWord_435429, baseEnd_435429] using wordTrace_append hprefix tailTrace_435429
  have hstable : (prefixWord ++ tailWord_435429).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435429).length < 2 ^ (prefixWord ++ tailWord_435429).sum := by decide
  have hdescent : baseEnd_435429 < baseStart_435429 := by decide
  rcases family_descends (prefixWord ++ tailWord_435429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435450 : List Nat := [3, 1, 1, 1, 1, 4, 2, 6]
def baseStart_435450 : Nat := 118140960795 + 435450 * 2 ^ 59
def prefixEnd_435450 : Nat := 4983230072969 + 3 ^ 40 * 435450 * 2
def baseEnd_435450 : Nat := 132500830222474982857723

theorem tailTrace_435450 : CollatzResearch.WordTrace tailWord_435450 prefixEnd_435450 132500830222474982857723 := by
  unfold tailWord_435450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3970541568111623446073951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10588110848297662522863869 3970541568111623446073951)
  ·
    refine ⟨5955812352167435169110927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3970541568111623446073951 5955812352167435169110927)
    ·
      refine ⟨8933718528251152753666391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5955812352167435169110927 8933718528251152753666391)
      ·
        refine ⟨13400577792376729130499587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8933718528251152753666391 13400577792376729130499587)
        ·
          refine ⟨20100866688565093695749381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13400577792376729130499587 20100866688565093695749381)
          ·
            refine ⟨3768912504105955067953009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20100866688565093695749381 3768912504105955067953009)
            ·
              refine ⟨2826684378079466300964757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3768912504105955067953009 2826684378079466300964757)
              ·
                refine ⟨132500830222474982857723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2826684378079466300964757 132500830222474982857723)
                ·
                  rfl

theorem cell19_435450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_435450 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435450 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435450 prefixEnd_435450 := by exact prefixLift 435450
  have htrace : WordTrace (prefixWord ++ tailWord_435450) baseStart_435450 baseEnd_435450 := by
    simpa [prefixWord, tailWord_435450, baseEnd_435450] using wordTrace_append hprefix tailTrace_435450
  have hstable : (prefixWord ++ tailWord_435450).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435450).length < 2 ^ (prefixWord ++ tailWord_435450).sum := by decide
  have hdescent : baseEnd_435450 < baseStart_435450 := by decide
  rcases family_descends (prefixWord ++ tailWord_435450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435467 : List Nat := [1, 1, 1, 1, 5, 3, 4, 3]
def baseStart_435467 : Nat := 118140960795 + 435467 * 2 ^ 59
def prefixEnd_435467 : Nat := 4983230072969 + 3 ^ 40 * 435467 * 2
def baseEnd_435467 : Nat := 132506003064623980479899

theorem tailTrace_435467 : CollatzResearch.WordTrace tailWord_435467 prefixEnd_435467 132506003064623980479899 := by
  unfold tailWord_435467
  simp only [CollatzResearch.WordTrace]
  refine ⟨15882786313384905687664655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10588524208923270458443103 15882786313384905687664655)
  ·
    refine ⟨23824179470077358531496983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15882786313384905687664655 23824179470077358531496983)
    ·
      refine ⟨35736269205116037797245475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23824179470077358531496983 35736269205116037797245475)
      ·
        refine ⟨53604403807674056695868213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35736269205116037797245475 53604403807674056695868213)
        ·
          refine ⟨5025412856969442815237645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53604403807674056695868213 5025412856969442815237645)
          ·
            refine ⟨1884529821363541055714117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5025412856969442815237645 1884529821363541055714117)
            ·
              refine ⟨353349341505663947946397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1884529821363541055714117 353349341505663947946397)
              ·
                refine ⟨132506003064623980479899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353349341505663947946397 132506003064623980479899)
                ·
                  rfl

theorem cell19_435467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 3].length) (baseStart_435467 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435467 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435467 prefixEnd_435467 := by exact prefixLift 435467
  have htrace : WordTrace (prefixWord ++ tailWord_435467) baseStart_435467 baseEnd_435467 := by
    simpa [prefixWord, tailWord_435467, baseEnd_435467] using wordTrace_append hprefix tailTrace_435467
  have hstable : (prefixWord ++ tailWord_435467).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435467).length < 2 ^ (prefixWord ++ tailWord_435467).sum := by decide
  have hdescent : baseEnd_435467 < baseStart_435467 := by decide
  rcases family_descends (prefixWord ++ tailWord_435467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435505 : List Nat := [1, 2, 2, 3, 3, 2, 2, 4]
def baseStart_435505 : Nat := 118140960795 + 435505 * 2 ^ 59
def prefixEnd_435505 : Nat := 4983230072969 + 3 ^ 40 * 435505 * 2
def baseEnd_435505 : Nat := 132517565888251151635351

theorem tailTrace_435505 : CollatzResearch.WordTrace tailWord_435505 prefixEnd_435505 132517565888251151635351 := by
  unfold tailWord_435505
  simp only [CollatzResearch.WordTrace]
  refine ⟨15884172287247238177547969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10589448191498158785031979 15884172287247238177547969)
  ·
    refine ⟨11913129215435428633160977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15884172287247238177547969 11913129215435428633160977)
    ·
      refine ⟨8934846911576571474870733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11913129215435428633160977 8934846911576571474870733)
      ·
        refine ⟨3350567591841214303076525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8934846911576571474870733 3350567591841214303076525)
        ·
          refine ⟨1256462846940455363653697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3350567591841214303076525 1256462846940455363653697)
          ·
            refine ⟨942347135205341522740273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1256462846940455363653697 942347135205341522740273)
            ·
              refine ⟨706760351404006142055205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 942347135205341522740273 706760351404006142055205)
              ·
                refine ⟨132517565888251151635351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 706760351404006142055205 132517565888251151635351)
                ·
                  rfl

theorem cell19_435505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_435505 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435505 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435505 prefixEnd_435505 := by exact prefixLift 435505
  have htrace : WordTrace (prefixWord ++ tailWord_435505) baseStart_435505 baseEnd_435505 := by
    simpa [prefixWord, tailWord_435505, baseEnd_435505] using wordTrace_append hprefix tailTrace_435505
  have hstable : (prefixWord ++ tailWord_435505).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435505).length < 2 ^ (prefixWord ++ tailWord_435505).sum := by decide
  have hdescent : baseEnd_435505 < baseStart_435505 := by decide
  rcases family_descends (prefixWord ++ tailWord_435505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435507 : List Nat := [1, 1, 1, 2, 5, 2, 1, 6]
def baseStart_435507 : Nat := 118140960795 + 435507 * 2 ^ 59
def prefixEnd_435507 : Nat := 4983230072969 + 3 ^ 40 * 435507 * 2
def baseEnd_435507 : Nat := 132518174457915739590901

theorem tailTrace_435507 : CollatzResearch.WordTrace tailWord_435507 prefixEnd_435507 132518174457915739590901 := by
  unfold tailWord_435507
  simp only [CollatzResearch.WordTrace]
  refine ⟨15884245233239992519120775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10589496822159995012747183 15884245233239992519120775)
  ·
    refine ⟨23826367849859988778681163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15884245233239992519120775 23826367849859988778681163)
    ·
      refine ⟨35739551774789983168021745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23826367849859988778681163 35739551774789983168021745)
      ·
        refine ⟨26804663831092487376016309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35739551774789983168021745 26804663831092487376016309)
        ·
          refine ⟨2512937234164920691501529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26804663831092487376016309 2512937234164920691501529)
          ·
            refine ⟨1884702925623690518626147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2512937234164920691501529 1884702925623690518626147)
            ·
              refine ⟨2827054388435535777939221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1884702925623690518626147 2827054388435535777939221)
              ·
                refine ⟨132518174457915739590901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2827054388435535777939221 132518174457915739590901)
                ·
                  rfl

theorem cell19_435507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_435507 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435507 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435507 prefixEnd_435507 := by exact prefixLift 435507
  have htrace : WordTrace (prefixWord ++ tailWord_435507) baseStart_435507 baseEnd_435507 := by
    simpa [prefixWord, tailWord_435507, baseEnd_435507] using wordTrace_append hprefix tailTrace_435507
  have hstable : (prefixWord ++ tailWord_435507).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435507).length < 2 ^ (prefixWord ++ tailWord_435507).sum := by decide
  have hdescent : baseEnd_435507 < baseStart_435507 := by decide
  rcases family_descends (prefixWord ++ tailWord_435507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435560 : List Nat := [2, 1, 4, 2, 3, 2, 1, 4]
def baseStart_435560 : Nat := 118140960795 + 435560 * 2 ^ 59
def prefixEnd_435560 : Nat := 4983230072969 + 3 ^ 40 * 435560 * 2
def baseEnd_435560 : Nat := 132534301554027320412979

theorem tailTrace_435560 : CollatzResearch.WordTrace tailWord_435560 prefixEnd_435560 132534301554027320412979 := by
  unfold tailWord_435560
  simp only [CollatzResearch.WordTrace]
  refine ⟨7943089151023991285400067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10590785534698655047200089 7943089151023991285400067)
  ·
    refine ⟨11914633726535986928100101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7943089151023991285400067 11914633726535986928100101)
    ·
      refine ⟨2233993823725497549018769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11914633726535986928100101 2233993823725497549018769)
      ·
        refine ⟨1675495367794123161764077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2233993823725497549018769 1675495367794123161764077)
        ·
          refine ⟨628310762922796185661529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1675495367794123161764077 628310762922796185661529)
          ·
            refine ⟨471233072192097139246147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 628310762922796185661529 471233072192097139246147)
            ·
              refine ⟨706849608288145708869221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471233072192097139246147 706849608288145708869221)
              ·
                refine ⟨132534301554027320412979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 706849608288145708869221 132534301554027320412979)
                ·
                  rfl

theorem cell19_435560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_435560 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435560 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435560 prefixEnd_435560 := by exact prefixLift 435560
  have htrace : WordTrace (prefixWord ++ tailWord_435560) baseStart_435560 baseEnd_435560 := by
    simpa [prefixWord, tailWord_435560, baseEnd_435560] using wordTrace_append hprefix tailTrace_435560
  have hstable : (prefixWord ++ tailWord_435560).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435560).length < 2 ^ (prefixWord ++ tailWord_435560).sum := by decide
  have hdescent : baseEnd_435560 < baseStart_435560 := by decide
  rcases family_descends (prefixWord ++ tailWord_435560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435581 : List Nat := [1, 4, 1, 1, 2, 2, 5, 3]
def baseStart_435581 : Nat := 118140960795 + 435581 * 2 ^ 59
def prefixEnd_435581 : Nat := 4983230072969 + 3 ^ 40 * 435581 * 2
def baseEnd_435581 : Nat := 132540691535505493946255

theorem tailTrace_435581 : CollatzResearch.WordTrace tailWord_435581 prefixEnd_435581 132540691535505493946255 := by
  unfold tailWord_435581
  simp only [CollatzResearch.WordTrace]
  refine ⟨15886944234971903157314597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10591296156647935438209731 15886944234971903157314597)
  ·
    refine ⟨2978802044057231841996487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15886944234971903157314597 2978802044057231841996487)
    ·
      refine ⟨4468203066085847762994731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2978802044057231841996487 4468203066085847762994731)
      ·
        refine ⟨6702304599128771644492097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4468203066085847762994731 6702304599128771644492097)
        ·
          refine ⟨5026728449346578733369073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6702304599128771644492097 5026728449346578733369073)
          ·
            refine ⟨3770046337009934050026805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5026728449346578733369073 3770046337009934050026805)
            ·
              refine ⟨353441844094681317190013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3770046337009934050026805 353441844094681317190013)
              ·
                refine ⟨132540691535505493946255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353441844094681317190013 132540691535505493946255)
                ·
                  rfl

theorem cell19_435581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 3].length) (baseStart_435581 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435581 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435581 prefixEnd_435581 := by exact prefixLift 435581
  have htrace : WordTrace (prefixWord ++ tailWord_435581) baseStart_435581 baseEnd_435581 := by
    simpa [prefixWord, tailWord_435581, baseEnd_435581] using wordTrace_append hprefix tailTrace_435581
  have hstable : (prefixWord ++ tailWord_435581).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435581).length < 2 ^ (prefixWord ++ tailWord_435581).sum := by decide
  have hdescent : baseEnd_435581 < baseStart_435581 := by decide
  rcases family_descends (prefixWord ++ tailWord_435581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435697 : List Nat := [1, 2, 2, 2, 3, 2, 2, 5]
def baseStart_435697 : Nat := 118140960795 + 435697 * 2 ^ 59
def prefixEnd_435697 : Nat := 4983230072969 + 3 ^ 40 * 435697 * 2
def baseEnd_435697 : Nat := 132575988576051595368161

theorem tailTrace_435697 : CollatzResearch.WordTrace tailWord_435697 prefixEnd_435697 132575988576051595368161 := by
  unfold tailWord_435697
  simp only [CollatzResearch.WordTrace]
  refine ⟨15891175102551654968537345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10594116735034436645691563 15891175102551654968537345)
  ·
    refine ⟨11918381326913741226403009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15891175102551654968537345 11918381326913741226403009)
    ·
      refine ⟨8938785995185305919802257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11918381326913741226403009 8938785995185305919802257)
      ·
        refine ⟨6704089496388979439851693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8938785995185305919802257 6704089496388979439851693)
        ·
          refine ⟨2514033561145867289944385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6704089496388979439851693 2514033561145867289944385)
          ·
            refine ⟨1885525170859400467458289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2514033561145867289944385 1885525170859400467458289)
            ·
              refine ⟨1414143878144550350593717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1885525170859400467458289 1414143878144550350593717)
              ·
                refine ⟨132575988576051595368161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1414143878144550350593717 132575988576051595368161)
                ·
                  rfl

theorem cell19_435697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_435697 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435697 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435697 prefixEnd_435697 := by exact prefixLift 435697
  have htrace : WordTrace (prefixWord ++ tailWord_435697) baseStart_435697 baseEnd_435697 := by
    simpa [prefixWord, tailWord_435697, baseEnd_435697] using wordTrace_append hprefix tailTrace_435697
  have hstable : (prefixWord ++ tailWord_435697).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435697).length < 2 ^ (prefixWord ++ tailWord_435697).sum := by decide
  have hdescent : baseEnd_435697 < baseStart_435697 := by decide
  rcases family_descends (prefixWord ++ tailWord_435697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435714 : List Nat := [3, 4, 1, 2, 1, 8]
def baseStart_435714 : Nat := 118140960795 + 435714 * 2 ^ 59
def prefixEnd_435714 : Nat := 4983230072969 + 3 ^ 40 * 435714 * 2
def baseEnd_435714 : Nat := 14731240157577843665593

theorem tailTrace_435714 : CollatzResearch.WordTrace tailWord_435714 prefixEnd_435714 14731240157577843665593 := by
  unfold tailWord_435714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3972948785872516717976549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10594530095660044581270797 3972948785872516717976549)
  ·
    refine ⟨744927897351096884620603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3972948785872516717976549 744927897351096884620603)
    ·
      refine ⟨1117391846026645326930905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 744927897351096884620603 1117391846026645326930905)
      ·
        refine ⟨838043884519983995198179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1117391846026645326930905 838043884519983995198179)
        ·
          refine ⟨1257065826779975992797269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 838043884519983995198179 1257065826779975992797269)
          ·
            refine ⟨14731240157577843665593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1257065826779975992797269 14731240157577843665593)
            ·
              rfl

theorem cell19_435714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 8].length) (baseStart_435714 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435714 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435714 prefixEnd_435714 := by exact prefixLift 435714
  have htrace : WordTrace (prefixWord ++ tailWord_435714) baseStart_435714 baseEnd_435714 := by
    simpa [prefixWord, tailWord_435714, baseEnd_435714] using wordTrace_append hprefix tailTrace_435714
  have hstable : (prefixWord ++ tailWord_435714).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435714).length < 2 ^ (prefixWord ++ tailWord_435714).sum := by decide
  have hdescent : baseEnd_435714 < baseStart_435714 := by decide
  rcases family_descends (prefixWord ++ tailWord_435714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435716 : List Nat := [2, 3, 2, 3, 9]
def baseStart_435716 : Nat := 118140960795 + 435716 * 2 ^ 59
def prefixEnd_435716 : Nat := 4983230072969 + 3 ^ 40 * 435716 * 2
def baseEnd_435716 : Nat := 4910435925476488183181

theorem tailTrace_435716 : CollatzResearch.WordTrace tailWord_435716 prefixEnd_435716 4910435925476488183181 := by
  unfold tailWord_435716
  simp only [CollatzResearch.WordTrace]
  refine ⟨7945934044741410606739501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10594578726321880808986001 7945934044741410606739501)
  ·
    refine ⟨2979725266778028977527313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7945934044741410606739501 2979725266778028977527313)
    ·
      refine ⟨2234793950083521733145485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2979725266778028977527313 2234793950083521733145485)
      ·
        refine ⟨838047731281320649929557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2234793950083521733145485 838047731281320649929557)
        ·
          refine ⟨4910435925476488183181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 838047731281320649929557 4910435925476488183181)
          ·
            rfl

theorem cell19_435716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 9].length) (baseStart_435716 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435716 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435716 prefixEnd_435716 := by exact prefixLift 435716
  have htrace : WordTrace (prefixWord ++ tailWord_435716) baseStart_435716 baseEnd_435716 := by
    simpa [prefixWord, tailWord_435716, baseEnd_435716] using wordTrace_append hprefix tailTrace_435716
  have hstable : (prefixWord ++ tailWord_435716).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435716).length < 2 ^ (prefixWord ++ tailWord_435716).sum := by decide
  have hdescent : baseEnd_435716 < baseStart_435716 := by decide
  rcases family_descends (prefixWord ++ tailWord_435716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435733 : List Nat := [1, 3, 2, 1, 3, 4, 1, 4]
def baseStart_435733 : Nat := 118140960795 + 435733 * 2 ^ 59
def prefixEnd_435733 : Nat := 4983230072969 + 3 ^ 40 * 435733 * 2
def baseEnd_435733 : Nat := 132586942830014178568063

theorem tailTrace_435733 : CollatzResearch.WordTrace tailWord_435733 prefixEnd_435733 132586942830014178568063 := by
  unfold tailWord_435733
  simp only [CollatzResearch.WordTrace]
  refine ⟨15892488130421233116847853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10594992086947488744565235 15892488130421233116847853)
  ·
    refine ⟨5959683048907962418817945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15892488130421233116847853 5959683048907962418817945)
    ·
      refine ⟨4469762286680971814113459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5959683048907962418817945 4469762286680971814113459)
      ·
        refine ⟨6704643430021457721170189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4469762286680971814113459 6704643430021457721170189)
        ·
          refine ⟨2514241286258046645438821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6704643430021457721170189 2514241286258046645438821)
          ·
            refine ⟨471420241173383746019779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2514241286258046645438821 471420241173383746019779)
            ·
              refine ⟨707130361760075619029669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 471420241173383746019779 707130361760075619029669)
              ·
                refine ⟨132586942830014178568063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 707130361760075619029669 132586942830014178568063)
                ·
                  rfl

theorem cell19_435733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 4].length) (baseStart_435733 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435733 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435733 prefixEnd_435733 := by exact prefixLift 435733
  have htrace : WordTrace (prefixWord ++ tailWord_435733) baseStart_435733 baseEnd_435733 := by
    simpa [prefixWord, tailWord_435733, baseEnd_435733] using wordTrace_append hprefix tailTrace_435733
  have hstable : (prefixWord ++ tailWord_435733).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435733).length < 2 ^ (prefixWord ++ tailWord_435733).sum := by decide
  have hdescent : baseEnd_435733 < baseStart_435733 := by decide
  rcases family_descends (prefixWord ++ tailWord_435733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435811 : List Nat := [1, 1, 1, 5, 1, 4, 1, 5]
def baseStart_435811 : Nat := 118140960795 + 435811 * 2 ^ 59
def prefixEnd_435811 : Nat := 4983230072969 + 3 ^ 40 * 435811 * 2
def baseEnd_435811 : Nat := 132610677046933108834517

theorem tailTrace_435811 : CollatzResearch.WordTrace tailWord_435811 prefixEnd_435811 132610677046933108834517 := by
  unfold tailWord_435811
  simp only [CollatzResearch.WordTrace]
  refine ⟨15895333024138652438187287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10596888682759101625458191 15895333024138652438187287)
  ·
    refine ⟨23842999536207978657280931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15895333024138652438187287 23842999536207978657280931)
    ·
      refine ⟨35764499304311967985921397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23842999536207978657280931 35764499304311967985921397)
      ·
        refine ⟨3352921809779246998680131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35764499304311967985921397 3352921809779246998680131)
        ·
          refine ⟨5029382714668870498020197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3352921809779246998680131 5029382714668870498020197)
          ·
            refine ⟨943009259000413218378787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5029382714668870498020197 943009259000413218378787)
            ·
              refine ⟨1414513888500619827568181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 943009259000413218378787 1414513888500619827568181)
              ·
                refine ⟨132610677046933108834517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1414513888500619827568181 132610677046933108834517)
                ·
                  rfl

theorem cell19_435811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_435811 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435811 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435811 prefixEnd_435811 := by exact prefixLift 435811
  have htrace : WordTrace (prefixWord ++ tailWord_435811) baseStart_435811 baseEnd_435811 := by
    simpa [prefixWord, tailWord_435811, baseEnd_435811] using wordTrace_append hprefix tailTrace_435811
  have hstable : (prefixWord ++ tailWord_435811).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435811).length < 2 ^ (prefixWord ++ tailWord_435811).sum := by decide
  have hdescent : baseEnd_435811 < baseStart_435811 := by decide
  rcases family_descends (prefixWord ++ tailWord_435811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435889 : List Nat := [1, 2, 2, 14]
def baseStart_435889 : Nat := 118140960795 + 435889 * 2 ^ 59
def prefixEnd_435889 : Nat := 4983230072969 + 3 ^ 40 * 435889 * 2
def baseEnd_435889 : Nat := 1637461867454963445691

theorem tailTrace_435889 : CollatzResearch.WordTrace tailWord_435889 prefixEnd_435889 1637461867454963445691 := by
  unfold tailWord_435889
  simp only [CollatzResearch.WordTrace]
  refine ⟨15898177917856071759526721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10598785278570714506351147 15898177917856071759526721)
  ·
    refine ⟨11923633438392053819645041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15898177917856071759526721 11923633438392053819645041)
    ·
      refine ⟨8942725078794040364733781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11923633438392053819645041 8942725078794040364733781)
      ·
        refine ⟨1637461867454963445691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 8942725078794040364733781 1637461867454963445691)
        ·
          rfl

theorem cell19_435889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 14].length) (baseStart_435889 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435889 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435889 prefixEnd_435889 := by exact prefixLift 435889
  have htrace : WordTrace (prefixWord ++ tailWord_435889) baseStart_435889 baseEnd_435889 := by
    simpa [prefixWord, tailWord_435889, baseEnd_435889] using wordTrace_append hprefix tailTrace_435889
  have hstable : (prefixWord ++ tailWord_435889).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435889).length < 2 ^ (prefixWord ++ tailWord_435889).sum := by decide
  have hdescent : baseEnd_435889 < baseStart_435889 := by decide
  rcases family_descends (prefixWord ++ tailWord_435889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_435944 : List Nat := [2, 1, 4, 1, 3, 2, 6]
def baseStart_435944 : Nat := 118140960795 + 435944 * 2 ^ 59
def prefixEnd_435944 : Nat := 4983230072969 + 3 ^ 40 * 435944 * 2
def baseEnd_435944 : Nat := 44217048976542735959533

theorem tailTrace_435944 : CollatzResearch.WordTrace tailWord_435944 prefixEnd_435944 44217048976542735959533 := by
  unfold tailWord_435944
  simp only [CollatzResearch.WordTrace]
  refine ⟨7950091966328408076389443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10600122621771210768519257 7950091966328408076389443)
  ·
    refine ⟨11925137949492612114584165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7950091966328408076389443 11925137949492612114584165)
    ·
      refine ⟨2235963365529864771484531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11925137949492612114584165 2235963365529864771484531)
      ·
        refine ⟨3353945048294797157226797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2235963365529864771484531 3353945048294797157226797)
        ·
          refine ⟨1257729393110548933960049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3353945048294797157226797 1257729393110548933960049)
          ·
            refine ⟨943297044832911700470037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1257729393110548933960049 943297044832911700470037)
            ·
              refine ⟨44217048976542735959533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 943297044832911700470037 44217048976542735959533)
              ·
                rfl

theorem cell19_435944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 6].length) (baseStart_435944 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_435944 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_435944 prefixEnd_435944 := by exact prefixLift 435944
  have htrace : WordTrace (prefixWord ++ tailWord_435944) baseStart_435944 baseEnd_435944 := by
    simpa [prefixWord, tailWord_435944, baseEnd_435944] using wordTrace_append hprefix tailTrace_435944
  have hstable : (prefixWord ++ tailWord_435944).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_435944).length < 2 ^ (prefixWord ++ tailWord_435944).sum := by decide
  have hdescent : baseEnd_435944 < baseStart_435944 := by decide
  rcases family_descends (prefixWord ++ tailWord_435944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436001 : List Nat := [1, 2, 3, 2, 1, 5, 5]
def baseStart_436001 : Nat := 118140960795 + 436001 * 2 ^ 59
def prefixEnd_436001 : Nat := 4983230072969 + 3 ^ 40 * 436001 * 2
def baseEnd_436001 : Nat := 44222830388356321537259

theorem tailTrace_436001 : CollatzResearch.WordTrace tailWord_436001 prefixEnd_436001 44222830388356321537259 := by
  unfold tailWord_436001
  simp only [CollatzResearch.WordTrace]
  refine ⟨15902262893450314887603857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10601508595633543258402571 15902262893450314887603857)
  ·
    refine ⟨11926697170087736165702893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15902262893450314887603857 11926697170087736165702893)
    ·
      refine ⟨4472511438782901062138585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11926697170087736165702893 4472511438782901062138585)
      ·
        refine ⟨3354383579087175796603939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4472511438782901062138585 3354383579087175796603939)
        ·
          refine ⟨5031575368630763694905909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3354383579087175796603939 5031575368630763694905909)
          ·
            refine ⟨471710190809134096397429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5031575368630763694905909 471710190809134096397429)
            ·
              refine ⟨44222830388356321537259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 471710190809134096397429 44222830388356321537259)
              ·
                rfl

theorem cell19_436001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 5].length) (baseStart_436001 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436001 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436001 prefixEnd_436001 := by exact prefixLift 436001
  have htrace : WordTrace (prefixWord ++ tailWord_436001) baseStart_436001 baseEnd_436001 := by
    simpa [prefixWord, tailWord_436001, baseEnd_436001] using wordTrace_append hprefix tailTrace_436001
  have hstable : (prefixWord ++ tailWord_436001).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436001).length < 2 ^ (prefixWord ++ tailWord_436001).sum := by decide
  have hdescent : baseEnd_436001 < baseStart_436001 := by decide
  rcases family_descends (prefixWord ++ tailWord_436001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436003 : List Nat := [1, 1, 1, 4, 2, 1, 9]
def baseStart_436003 : Nat := 118140960795 + 436003 * 2 ^ 59
def prefixEnd_436003 : Nat := 4983230072969 + 3 ^ 40 * 436003 * 2
def baseEnd_436003 : Nat := 44223033244911184189109

theorem tailTrace_436003 : CollatzResearch.WordTrace tailWord_436003 prefixEnd_436003 44223033244911184189109 := by
  unfold tailWord_436003
  simp only [CollatzResearch.WordTrace]
  refine ⟨15902335839443069229176663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10601557226295379486117775 15902335839443069229176663)
  ·
    refine ⟨23853503759164603843764995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15902335839443069229176663 23853503759164603843764995)
    ·
      refine ⟨35780255638746905765647493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23853503759164603843764995 35780255638746905765647493)
      ·
        refine ⟨6708797932265044831058905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35780255638746905765647493 6708797932265044831058905)
        ·
          refine ⟨5031598449198783623294179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6708797932265044831058905 5031598449198783623294179)
          ·
            refine ⟨7547397673798175434941269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5031598449198783623294179 7547397673798175434941269)
            ·
              refine ⟨44223033244911184189109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7547397673798175434941269 44223033244911184189109)
              ·
                rfl

theorem cell19_436003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 9].length) (baseStart_436003 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436003 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436003 prefixEnd_436003 := by exact prefixLift 436003
  have htrace : WordTrace (prefixWord ++ tailWord_436003) baseStart_436003 baseEnd_436003 := by
    simpa [prefixWord, tailWord_436003, baseEnd_436003] using wordTrace_append hprefix tailTrace_436003
  have hstable : (prefixWord ++ tailWord_436003).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436003).length < 2 ^ (prefixWord ++ tailWord_436003).sum := by decide
  have hdescent : baseEnd_436003 < baseStart_436003 := by decide
  rcases family_descends (prefixWord ++ tailWord_436003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436041 : List Nat := [1, 2, 1, 1, 2, 4, 1, 7]
def baseStart_436041 : Nat := 118140960795 + 436041 * 2 ^ 59
def prefixEnd_436041 : Nat := 4983230072969 + 3 ^ 40 * 436041 * 2
def baseEnd_436041 : Nat := 132680662558360723722779

theorem tailTrace_436041 : CollatzResearch.WordTrace tailWord_436041 prefixEnd_436041 132680662558360723722779 := by
  unfold tailWord_436041
  simp only [CollatzResearch.WordTrace]
  refine ⟨15903721813305401719059977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10602481208870267812706651 15903721813305401719059977)
  ·
    refine ⟨11927791359979051289294983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15903721813305401719059977 11927791359979051289294983)
    ·
      refine ⟨17891687039968576933942475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11927791359979051289294983 17891687039968576933942475)
      ·
        refine ⟨26837530559952865400913713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17891687039968576933942475 26837530559952865400913713)
        ·
          refine ⟨20128147919964649050685285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26837530559952865400913713 20128147919964649050685285)
          ·
            refine ⟨3774027734993371697003491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20128147919964649050685285 3774027734993371697003491)
            ·
              refine ⟨5661041602490057545505237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3774027734993371697003491 5661041602490057545505237)
              ·
                refine ⟨132680662558360723722779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5661041602490057545505237 132680662558360723722779)
                ·
                  rfl

theorem cell19_436041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_436041 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436041 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436041 prefixEnd_436041 := by exact prefixLift 436041
  have htrace : WordTrace (prefixWord ++ tailWord_436041) baseStart_436041 baseEnd_436041 := by
    simpa [prefixWord, tailWord_436041, baseEnd_436041] using wordTrace_append hprefix tailTrace_436041
  have hstable : (prefixWord ++ tailWord_436041).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436041).length < 2 ^ (prefixWord ++ tailWord_436041).sum := by decide
  have hdescent : baseEnd_436041 < baseStart_436041 := by decide
  rcases family_descends (prefixWord ++ tailWord_436041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436077 : List Nat := [1, 5, 1, 1, 1, 1, 5, 4]
def baseStart_436077 : Nat := 118140960795 + 436077 * 2 ^ 59
def prefixEnd_436077 : Nat := 4983230072969 + 3 ^ 40 * 436077 * 2
def baseEnd_436077 : Nat := 132691616812323306922681

theorem tailTrace_436077 : CollatzResearch.WordTrace tailWord_436077 prefixEnd_436077 132691616812323306922681 := by
  unfold tailWord_436077
  simp only [CollatzResearch.WordTrace]
  refine ⟨15905034841174979867370485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10603356560783319911580323 15905034841174979867370485)
  ·
    refine ⟨1491097016360154362565983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15905034841174979867370485 1491097016360154362565983)
    ·
      refine ⟨2236645524540231543848975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1491097016360154362565983 2236645524540231543848975)
      ·
        refine ⟨3354968286810347315773463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2236645524540231543848975 3354968286810347315773463)
        ·
          refine ⟨5032452430215520973660195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3354968286810347315773463 5032452430215520973660195)
          ·
            refine ⟨7548678645323281460490293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5032452430215520973660195 7548678645323281460490293)
            ·
              refine ⟨707688622999057636920965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7548678645323281460490293 707688622999057636920965)
              ·
                refine ⟨132691616812323306922681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 707688622999057636920965 132691616812323306922681)
                ·
                  rfl

theorem cell19_436077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_436077 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436077 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436077 prefixEnd_436077 := by exact prefixLift 436077
  have htrace : WordTrace (prefixWord ++ tailWord_436077) baseStart_436077 baseEnd_436077 := by
    simpa [prefixWord, tailWord_436077, baseEnd_436077] using wordTrace_append hprefix tailTrace_436077
  have hstable : (prefixWord ++ tailWord_436077).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436077).length < 2 ^ (prefixWord ++ tailWord_436077).sum := by decide
  have hdescent : baseEnd_436077 < baseStart_436077 := by decide
  rcases family_descends (prefixWord ++ tailWord_436077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436096 : List Nat := [2, 1, 1, 2, 1, 2, 7, 3]
def baseStart_436096 : Nat := 118140960795 + 436096 * 2 ^ 59
def prefixEnd_436096 : Nat := 4983230072969 + 3 ^ 40 * 436096 * 2
def baseEnd_436096 : Nat := 132697398224136892500407

theorem tailTrace_436096 : CollatzResearch.WordTrace tailWord_436096 prefixEnd_436096 132697398224136892500407 := by
  unfold tailWord_436096
  simp only [CollatzResearch.WordTrace]
  refine ⟨7952863914053073056156071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10603818552070764074874761 7952863914053073056156071)
  ·
    refine ⟨11929295871079609584234107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7952863914053073056156071 11929295871079609584234107)
    ·
      refine ⟨17893943806619414376351161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11929295871079609584234107 17893943806619414376351161)
      ·
        refine ⟨13420457854964560782263371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17893943806619414376351161 13420457854964560782263371)
        ·
          refine ⟨20130686782446841173395057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13420457854964560782263371 20130686782446841173395057)
          ·
            refine ⟨15098015086835130880046293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20130686782446841173395057 15098015086835130880046293)
            ·
              refine ⟨353859728597698380001085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 15098015086835130880046293 353859728597698380001085)
              ·
                refine ⟨132697398224136892500407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353859728597698380001085 132697398224136892500407)
                ·
                  rfl

theorem cell19_436096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_436096 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436096 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436096 prefixEnd_436096 := by exact prefixLift 436096
  have htrace : WordTrace (prefixWord ++ tailWord_436096) baseStart_436096 baseEnd_436096 := by
    simpa [prefixWord, tailWord_436096, baseEnd_436096] using wordTrace_append hprefix tailTrace_436096
  have hstable : (prefixWord ++ tailWord_436096).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436096).length < 2 ^ (prefixWord ++ tailWord_436096).sum := by decide
  have hdescent : baseEnd_436096 < baseStart_436096 := by decide
  rcases family_descends (prefixWord ++ tailWord_436096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436117 : List Nat := [1, 3, 2, 1, 1, 3, 8]
def baseStart_436117 : Nat := 118140960795 + 436117 * 2 ^ 59
def prefixEnd_436117 : Nat := 4983230072969 + 3 ^ 40 * 436117 * 2
def baseEnd_436117 : Nat := 44234596068538355344561

theorem tailTrace_436117 : CollatzResearch.WordTrace tailWord_436117 prefixEnd_436117 44234596068538355344561 := by
  unfold tailWord_436117
  simp only [CollatzResearch.WordTrace]
  refine ⟨15906493761030066698826605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10604329174020044465884403 15906493761030066698826605)
  ·
    refine ⟨5964935160386275012059977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15906493761030066698826605 5964935160386275012059977)
    ·
      refine ⟨4473701370289706259044983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5964935160386275012059977 4473701370289706259044983)
      ·
        refine ⟨6710552055434559388567475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4473701370289706259044983 6710552055434559388567475)
        ·
          refine ⟨10065828083151839082851213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6710552055434559388567475 10065828083151839082851213)
          ·
            refine ⟨3774685531181939656069205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10065828083151839082851213 3774685531181939656069205)
            ·
              refine ⟨44234596068538355344561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3774685531181939656069205 44234596068538355344561)
              ·
                rfl

theorem cell19_436117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 8].length) (baseStart_436117 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436117 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436117 prefixEnd_436117 := by exact prefixLift 436117
  have htrace : WordTrace (prefixWord ++ tailWord_436117) baseStart_436117 baseEnd_436117 := by
    simpa [prefixWord, tailWord_436117, baseEnd_436117] using wordTrace_append hprefix tailTrace_436117
  have hstable : (prefixWord ++ tailWord_436117).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436117).length < 2 ^ (prefixWord ++ tailWord_436117).sum := by decide
  have hdescent : baseEnd_436117 < baseStart_436117 := by decide
  rcases family_descends (prefixWord ++ tailWord_436117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436172 : List Nat := [2, 2, 1, 4, 1, 4, 5]
def baseStart_436172 : Nat := 118140960795 + 436172 * 2 ^ 59
def prefixEnd_436172 : Nat := 4983230072969 + 3 ^ 40 * 436172 * 2
def baseEnd_436172 : Nat := 44240174623797078270437

theorem tailTrace_436172 : CollatzResearch.WordTrace tailWord_436172 prefixEnd_436172 44240174623797078270437 := by
  unfold tailWord_436172
  simp only [CollatzResearch.WordTrace]
  refine ⟨7954249887915405546039385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10605666517220540728052513 7954249887915405546039385)
  ·
    refine ⟨5965687415936554159529539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7954249887915405546039385 5965687415936554159529539)
    ·
      refine ⟨8948531123904831239294309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5965687415936554159529539 8948531123904831239294309)
      ·
        refine ⟨1677849585732155857367683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8948531123904831239294309 1677849585732155857367683)
        ·
          refine ⟨2516774378598233786051525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1677849585732155857367683 2516774378598233786051525)
          ·
            refine ⟨471895195987168834884661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2516774378598233786051525 471895195987168834884661)
            ·
              refine ⟨44240174623797078270437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 471895195987168834884661 44240174623797078270437)
              ·
                rfl

theorem cell19_436172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 5].length) (baseStart_436172 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436172 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436172 prefixEnd_436172 := by exact prefixLift 436172
  have htrace : WordTrace (prefixWord ++ tailWord_436172) baseStart_436172 baseEnd_436172 := by
    simpa [prefixWord, tailWord_436172, baseEnd_436172] using wordTrace_append hprefix tailTrace_436172
  have hstable : (prefixWord ++ tailWord_436172).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436172).length < 2 ^ (prefixWord ++ tailWord_436172).sum := by decide
  have hdescent : baseEnd_436172 < baseStart_436172 := by decide
  rcases family_descends (prefixWord ++ tailWord_436172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436189 : List Nat := [1, 4, 3, 1, 3, 1, 2, 4]
def baseStart_436189 : Nat := 118140960795 + 436189 * 2 ^ 59
def prefixEnd_436189 : Nat := 4983230072969 + 3 ^ 40 * 436189 * 2
def baseEnd_436189 : Nat := 132725696713540232433487

theorem tailTrace_436189 : CollatzResearch.WordTrace tailWord_436189 prefixEnd_436189 132725696713540232433487 := by
  unfold tailWord_436189
  simp only [CollatzResearch.WordTrace]
  refine ⟨15909119816769222995447621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10606079877846148663631747 15909119816769222995447621)
  ·
    refine ⟨2982959965644229311646429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15909119816769222995447621 2982959965644229311646429)
    ·
      refine ⟨1118609987116585991867411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2982959965644229311646429 1118609987116585991867411)
      ·
        refine ⟨1677914980674878987801117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1118609987116585991867411 1677914980674878987801117)
        ·
          refine ⟨629218117753079620425419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1677914980674878987801117 629218117753079620425419)
          ·
            refine ⟨943827176629619430638129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629218117753079620425419 943827176629619430638129)
            ·
              refine ⟨707870382472214572978597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 943827176629619430638129 707870382472214572978597)
              ·
                refine ⟨132725696713540232433487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 707870382472214572978597 132725696713540232433487)
                ·
                  rfl

theorem cell19_436189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 4].length) (baseStart_436189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436189 prefixEnd_436189 := by exact prefixLift 436189
  have htrace : WordTrace (prefixWord ++ tailWord_436189) baseStart_436189 baseEnd_436189 := by
    simpa [prefixWord, tailWord_436189, baseEnd_436189] using wordTrace_append hprefix tailTrace_436189
  have hstable : (prefixWord ++ tailWord_436189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436189).length < 2 ^ (prefixWord ++ tailWord_436189).sum := by decide
  have hdescent : baseEnd_436189 < baseStart_436189 := by decide
  rcases family_descends (prefixWord ++ tailWord_436189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436191 : List Nat := [1, 1, 2, 3, 4, 2, 2, 4]
def baseStart_436191 : Nat := 118140960795 + 436191 * 2 ^ 59
def prefixEnd_436191 : Nat := 4983230072969 + 3 ^ 40 * 436191 * 2
def baseEnd_436191 : Nat := 132726305283204820389037

theorem tailTrace_436191 : CollatzResearch.WordTrace tailWord_436191 prefixEnd_436191 132726305283204820389037 := by
  unfold tailWord_436191
  simp only [CollatzResearch.WordTrace]
  refine ⟨15909192762761977337020427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10606128508507984891346951 15909192762761977337020427)
  ·
    refine ⟨23863789144142966005530641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15909192762761977337020427 23863789144142966005530641)
    ·
      refine ⟨17897841858107224504147981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23863789144142966005530641 17897841858107224504147981)
      ·
        refine ⟨6711690696790209189055493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17897841858107224504147981 6711690696790209189055493)
        ·
          refine ⟨1258442005648164222947905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6711690696790209189055493 1258442005648164222947905)
          ·
            refine ⟨943831504236123167210929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1258442005648164222947905 943831504236123167210929)
            ·
              refine ⟨707873628177092375408197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 943831504236123167210929 707873628177092375408197)
              ·
                refine ⟨132726305283204820389037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 707873628177092375408197 132726305283204820389037)
                ·
                  rfl

theorem cell19_436191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_436191 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436191 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436191 prefixEnd_436191 := by exact prefixLift 436191
  have htrace : WordTrace (prefixWord ++ tailWord_436191) baseStart_436191 baseEnd_436191 := by
    simpa [prefixWord, tailWord_436191, baseEnd_436191] using wordTrace_append hprefix tailTrace_436191
  have hstable : (prefixWord ++ tailWord_436191).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436191).length < 2 ^ (prefixWord ++ tailWord_436191).sum := by decide
  have hdescent : baseEnd_436191 < baseStart_436191 := by decide
  rcases family_descends (prefixWord ++ tailWord_436191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436193 : List Nat := [1, 2, 3, 1, 2, 1, 3, 6]
def baseStart_436193 : Nat := 118140960795 + 436193 * 2 ^ 59
def prefixEnd_436193 : Nat := 4983230072969 + 3 ^ 40 * 436193 * 2
def baseEnd_436193 : Nat := 132726913852869408344587

theorem tailTrace_436193 : CollatzResearch.WordTrace tailWord_436193 prefixEnd_436193 132726913852869408344587 := by
  unfold tailWord_436193
  simp only [CollatzResearch.WordTrace]
  refine ⟨15909265708754731678593233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10606177139169821119062155 15909265708754731678593233)
  ·
    refine ⟨11931949281566048758944925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15909265708754731678593233 11931949281566048758944925)
    ·
      refine ⟨4474480980587268284604347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11931949281566048758944925 4474480980587268284604347)
      ·
        refine ⟨6711721470880902426906521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4474480980587268284604347 6711721470880902426906521)
        ·
          refine ⟨5033791103160676820179891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6711721470880902426906521 5033791103160676820179891)
          ·
            refine ⟨7550686654741015230269837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5033791103160676820179891 7550686654741015230269837)
            ·
              refine ⟨2831507495527880711351189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7550686654741015230269837 2831507495527880711351189)
              ·
                refine ⟨132726913852869408344587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2831507495527880711351189 132726913852869408344587)
                ·
                  rfl

theorem cell19_436193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_436193 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436193 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436193 prefixEnd_436193 := by exact prefixLift 436193
  have htrace : WordTrace (prefixWord ++ tailWord_436193) baseStart_436193 baseEnd_436193 := by
    simpa [prefixWord, tailWord_436193, baseEnd_436193] using wordTrace_append hprefix tailTrace_436193
  have hstable : (prefixWord ++ tailWord_436193).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436193).length < 2 ^ (prefixWord ++ tailWord_436193).sum := by decide
  have hdescent : baseEnd_436193 < baseStart_436193 := by decide
  rcases family_descends (prefixWord ++ tailWord_436193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436231 : List Nat := [1, 1, 4, 3, 1, 9]
def baseStart_436231 : Nat := 118140960795 + 436231 * 2 ^ 59
def prefixEnd_436231 : Nat := 4983230072969 + 3 ^ 40 * 436231 * 2
def baseEnd_436231 : Nat := 14748719630721842166671

theorem tailTrace_436231 : CollatzResearch.WordTrace tailWord_436231 prefixEnd_436231 14748719630721842166671 := by
  unfold tailWord_436231
  simp only [CollatzResearch.WordTrace]
  refine ⟨15910651682617064168476547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10607101121744709445651031 15910651682617064168476547)
  ·
    refine ⟨23865977523925596252714821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15910651682617064168476547 23865977523925596252714821)
    ·
      refine ⟨4474870785736049297384029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23865977523925596252714821 4474870785736049297384029)
      ·
        refine ⟨1678076544651018486519011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4474870785736049297384029 1678076544651018486519011)
        ·
          refine ⟨2517114816976527729778517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678076544651018486519011 2517114816976527729778517)
          ·
            refine ⟨14748719630721842166671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2517114816976527729778517 14748719630721842166671)
            ·
              rfl

theorem cell19_436231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 9].length) (baseStart_436231 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436231 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436231 prefixEnd_436231 := by exact prefixLift 436231
  have htrace : WordTrace (prefixWord ++ tailWord_436231) baseStart_436231 baseEnd_436231 := by
    simpa [prefixWord, tailWord_436231, baseEnd_436231] using wordTrace_append hprefix tailTrace_436231
  have hstable : (prefixWord ++ tailWord_436231).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436231).length < 2 ^ (prefixWord ++ tailWord_436231).sum := by decide
  have hdescent : baseEnd_436231 < baseStart_436231 := by decide
  rcases family_descends (prefixWord ++ tailWord_436231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436263 : List Nat := [1, 1, 7, 1, 2, 1, 3, 3]
def baseStart_436263 : Nat := 118140960795 + 436263 * 2 ^ 59
def prefixEnd_436263 : Nat := 4983230072969 + 3 ^ 40 * 436263 * 2
def baseEnd_436263 : Nat := 132748213791129986788841

theorem tailTrace_436263 : CollatzResearch.WordTrace tailWord_436263 prefixEnd_436263 132748213791129986788841 := by
  unfold tailWord_436263
  simp only [CollatzResearch.WordTrace]
  refine ⟨15911818818501133633641443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10607879212334089089094295 15911818818501133633641443)
  ·
    refine ⟨23867728227751700450462165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15911818818501133633641443 23867728227751700450462165)
    ·
      refine ⟨559399880337930479307707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 23867728227751700450462165 559399880337930479307707)
      ·
        refine ⟨839099820506895718961561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 559399880337930479307707 839099820506895718961561)
        ·
          refine ⟨629324865380171789221171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 839099820506895718961561 629324865380171789221171)
          ·
            refine ⟨943987298070257683831757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629324865380171789221171 943987298070257683831757)
            ·
              refine ⟨353995236776346631436909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 943987298070257683831757 353995236776346631436909)
              ·
                refine ⟨132748213791129986788841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 353995236776346631436909 132748213791129986788841)
                ·
                  rfl

theorem cell19_436263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 3].length) (baseStart_436263 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436263 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436263 prefixEnd_436263 := by exact prefixLift 436263
  have htrace : WordTrace (prefixWord ++ tailWord_436263) baseStart_436263 baseEnd_436263 := by
    simpa [prefixWord, tailWord_436263, baseEnd_436263] using wordTrace_append hprefix tailTrace_436263
  have hstable : (prefixWord ++ tailWord_436263).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436263).length < 2 ^ (prefixWord ++ tailWord_436263).sum := by decide
  have hdescent : baseEnd_436263 < baseStart_436263 := by decide
  rcases family_descends (prefixWord ++ tailWord_436263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436288 : List Nat := [2, 1, 1, 2, 2, 5, 6]
def baseStart_436288 : Nat := 118140960795 + 436288 * 2 ^ 59
def prefixEnd_436288 : Nat := 4983230072969 + 3 ^ 40 * 436288 * 2
def baseEnd_436288 : Nat := 44251940303979112077739

theorem tailTrace_436288 : CollatzResearch.WordTrace tailWord_436288 prefixEnd_436288 44251940303979112077739 := by
  unfold tailWord_436288
  simp only [CollatzResearch.WordTrace]
  refine ⟨7956365321705281451650759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10608487095607041935534345 7956365321705281451650759)
  ·
    refine ⟨11934547982557922177476139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7956365321705281451650759 11934547982557922177476139)
    ·
      refine ⟨17901821973836883266214209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11934547982557922177476139 17901821973836883266214209)
      ·
        refine ⟨13426366480377662449660657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17901821973836883266214209 13426366480377662449660657)
        ·
          refine ⟨10069774860283246837245493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13426366480377662449660657 10069774860283246837245493)
          ·
            refine ⟨944041393151554390991765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10069774860283246837245493 944041393151554390991765)
            ·
              refine ⟨44251940303979112077739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 944041393151554390991765 44251940303979112077739)
              ·
                rfl

theorem cell19_436288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 6].length) (baseStart_436288 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436288 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436288 prefixEnd_436288 := by exact prefixLift 436288
  have htrace : WordTrace (prefixWord ++ tailWord_436288) baseStart_436288 baseEnd_436288 := by
    simpa [prefixWord, tailWord_436288, baseEnd_436288] using wordTrace_append hprefix tailTrace_436288
  have hstable : (prefixWord ++ tailWord_436288).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436288).length < 2 ^ (prefixWord ++ tailWord_436288).sum := by decide
  have hdescent : baseEnd_436288 < baseStart_436288 := by decide
  rcases family_descends (prefixWord ++ tailWord_436288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436322 : List Nat := [3, 3, 2, 2, 2, 1, 1, 5]
def baseStart_436322 : Nat := 118140960795 + 436322 * 2 ^ 59
def prefixEnd_436322 : Nat := 4983230072969 + 3 ^ 40 * 436322 * 2
def baseEnd_436322 : Nat := 132766166596235331477569

theorem tailTrace_436322 : CollatzResearch.WordTrace tailWord_436322 prefixEnd_436322 132766166596235331477569 := by
  unfold tailWord_436322
  simp only [CollatzResearch.WordTrace]
  refine ⟨3978492681321846677509805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10609313816858257806692813 3978492681321846677509805)
  ·
    refine ⟨1491934755495692504066177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3978492681321846677509805 1491934755495692504066177)
    ·
      refine ⟨1118951066621769378049633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1491934755495692504066177 1118951066621769378049633)
      ·
        refine ⟨839213299966327033537225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1118951066621769378049633 839213299966327033537225)
        ·
          refine ⟨629409974974745275152919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 839213299966327033537225 629409974974745275152919)
          ·
            refine ⟨944114962462117912729379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629409974974745275152919 944114962462117912729379)
            ·
              refine ⟨1416172443693176869094069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944114962462117912729379 1416172443693176869094069)
              ·
                refine ⟨132766166596235331477569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1416172443693176869094069 132766166596235331477569)
                ·
                  rfl

theorem cell19_436322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_436322 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436322 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436322 prefixEnd_436322 := by exact prefixLift 436322
  have htrace : WordTrace (prefixWord ++ tailWord_436322) baseStart_436322 baseEnd_436322 := by
    simpa [prefixWord, tailWord_436322, baseEnd_436322] using wordTrace_append hprefix tailTrace_436322
  have hstable : (prefixWord ++ tailWord_436322).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436322).length < 2 ^ (prefixWord ++ tailWord_436322).sum := by decide
  have hdescent : baseEnd_436322 < baseStart_436322 := by decide
  rcases family_descends (prefixWord ++ tailWord_436322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436324 : List Nat := [2, 3, 1, 1, 2, 1, 6, 3]
def baseStart_436324 : Nat := 118140960795 + 436324 * 2 ^ 59
def prefixEnd_436324 : Nat := 4983230072969 + 3 ^ 40 * 436324 * 2
def baseEnd_436324 : Nat := 132766775165899919433119

theorem tailTrace_436324 : CollatzResearch.WordTrace tailWord_436324 prefixEnd_436324 132766775165899919433119 := by
  unfold tailWord_436324
  simp only [CollatzResearch.WordTrace]
  refine ⟨7957021835640070525806013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10609362447520094034408017 7957021835640070525806013)
  ·
    refine ⟨2983883188365026447177255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7957021835640070525806013 2983883188365026447177255)
    ·
      refine ⟨4475824782547539670765883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2983883188365026447177255 4475824782547539670765883)
      ·
        refine ⟨6713737173821309506148825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4475824782547539670765883 6713737173821309506148825)
        ·
          refine ⟨5035302880365982129611619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6713737173821309506148825 5035302880365982129611619)
          ·
            refine ⟨7552954320548973194417429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5035302880365982129611619 7552954320548973194417429)
            ·
              refine ⟨354044733775733118488317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7552954320548973194417429 354044733775733118488317)
              ·
                refine ⟨132766775165899919433119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 354044733775733118488317 132766775165899919433119)
                ·
                  rfl

theorem cell19_436324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_436324 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436324 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436324 prefixEnd_436324 := by exact prefixLift 436324
  have htrace : WordTrace (prefixWord ++ tailWord_436324) baseStart_436324 baseEnd_436324 := by
    simpa [prefixWord, tailWord_436324, baseEnd_436324] using wordTrace_append hprefix tailTrace_436324
  have hstable : (prefixWord ++ tailWord_436324).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436324).length < 2 ^ (prefixWord ++ tailWord_436324).sum := by decide
  have hdescent : baseEnd_436324 < baseStart_436324 := by decide
  rcases family_descends (prefixWord ++ tailWord_436324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436345 : List Nat := [1, 2, 1, 3, 4, 1, 7]
def baseStart_436345 : Nat := 118140960795 + 436345 * 2 ^ 59
def prefixEnd_436345 : Nat := 4983230072969 + 3 ^ 40 * 436345 * 2
def baseEnd_436345 : Nat := 44257721715792697655465

theorem tailTrace_436345 : CollatzResearch.WordTrace tailWord_436345 prefixEnd_436345 44257721715792697655465 := by
  unfold tailWord_436345
  simp only [CollatzResearch.WordTrace]
  refine ⟨15914809604204061638126489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10609873069469374425417659 15914809604204061638126489)
  ·
    refine ⟨11936107203153046228594867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15914809604204061638126489 11936107203153046228594867)
    ·
      refine ⟨17904160804729569342892301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11936107203153046228594867 17904160804729569342892301)
      ·
        refine ⟨6714060301773588503584613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17904160804729569342892301 6714060301773588503584613)
        ·
          refine ⟨1258886306582547844422115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6714060301773588503584613 1258886306582547844422115)
          ·
            refine ⟨1888329459873821766633173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1258886306582547844422115 1888329459873821766633173)
            ·
              refine ⟨44257721715792697655465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1888329459873821766633173 44257721715792697655465)
              ·
                rfl

theorem cell19_436345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 7].length) (baseStart_436345 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436345 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436345 prefixEnd_436345 := by exact prefixLift 436345
  have htrace : WordTrace (prefixWord ++ tailWord_436345) baseStart_436345 baseEnd_436345 := by
    simpa [prefixWord, tailWord_436345, baseEnd_436345] using wordTrace_append hprefix tailTrace_436345
  have hstable : (prefixWord ++ tailWord_436345).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436345).length < 2 ^ (prefixWord ++ tailWord_436345).sum := by decide
  have hdescent : baseEnd_436345 < baseStart_436345 := by decide
  rcases family_descends (prefixWord ++ tailWord_436345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436362 : List Nat := [3, 1, 2, 3, 1, 3, 2, 4]
def baseStart_436362 : Nat := 118140960795 + 436362 * 2 ^ 59
def prefixEnd_436362 : Nat := 4983230072969 + 3 ^ 40 * 436362 * 2
def baseEnd_436362 : Nat := 132778337989527090588571

theorem tailTrace_436362 : CollatzResearch.WordTrace tailWord_436362 prefixEnd_436362 132778337989527090588571 := by
  unfold tailWord_436362
  simp only [CollatzResearch.WordTrace]
  refine ⟨3978857411285618385373835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10610286430094982360996893 3978857411285618385373835)
  ·
    refine ⟨5968286116928427578060753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3978857411285618385373835 5968286116928427578060753)
    ·
      refine ⟨4476214587696320683545565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5968286116928427578060753 4476214587696320683545565)
      ·
        refine ⟨1678580470386120256329587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4476214587696320683545565 1678580470386120256329587)
        ·
          refine ⟨2517870705579180384494381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1678580470386120256329587 2517870705579180384494381)
          ·
            refine ⟨944201514592192644185393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2517870705579180384494381 944201514592192644185393)
            ·
              refine ⟨708151135944144483139045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 944201514592192644185393 708151135944144483139045)
              ·
                refine ⟨132778337989527090588571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 708151135944144483139045 132778337989527090588571)
                ·
                  rfl

theorem cell19_436362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_436362 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436362 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436362 prefixEnd_436362 := by exact prefixLift 436362
  have htrace : WordTrace (prefixWord ++ tailWord_436362) baseStart_436362 baseEnd_436362 := by
    simpa [prefixWord, tailWord_436362, baseEnd_436362] using wordTrace_append hprefix tailTrace_436362
  have hstable : (prefixWord ++ tailWord_436362).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436362).length < 2 ^ (prefixWord ++ tailWord_436362).sum := by decide
  have hdescent : baseEnd_436362 < baseStart_436362 := by decide
  rcases family_descends (prefixWord ++ tailWord_436362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436398 : List Nat := [4, 1, 4, 2, 1, 7]
def baseStart_436398 : Nat := 118140960795 + 436398 * 2 ^ 59
def prefixEnd_436398 : Nat := 4983230072969 + 3 ^ 40 * 436398 * 2
def baseEnd_436398 : Nat := 14754365804832185976497

theorem tailTrace_436398 : CollatzResearch.WordTrace tailWord_436398 prefixEnd_436398 14754365804832185976497 := by
  unfold tailWord_436398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1989592834126506461225731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10611161782008034459870565 1989592834126506461225731)
  ·
    refine ⟨2984389251189759691838597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1989592834126506461225731 2984389251189759691838597)
    ·
      refine ⟨559572984598079942219737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2984389251189759691838597 559572984598079942219737)
      ·
        refine ⟨419679738448559956664803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 559572984598079942219737 419679738448559956664803)
        ·
          refine ⟨629519607672839934997205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419679738448559956664803 629519607672839934997205)
          ·
            refine ⟨14754365804832185976497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 629519607672839934997205 14754365804832185976497)
            ·
              rfl

theorem cell19_436398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 7].length) (baseStart_436398 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436398 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436398 prefixEnd_436398 := by exact prefixLift 436398
  have htrace : WordTrace (prefixWord ++ tailWord_436398) baseStart_436398 baseEnd_436398 := by
    simpa [prefixWord, tailWord_436398, baseEnd_436398] using wordTrace_append hprefix tailTrace_436398
  have hstable : (prefixWord ++ tailWord_436398).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436398).length < 2 ^ (prefixWord ++ tailWord_436398).sum := by decide
  have hdescent : baseEnd_436398 < baseStart_436398 := by decide
  rcases family_descends (prefixWord ++ tailWord_436398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436421 : List Nat := [1, 3, 1, 1, 1, 1, 7, 4]
def baseStart_436421 : Nat := 118140960795 + 436421 * 2 ^ 59
def prefixEnd_436421 : Nat := 4983230072969 + 3 ^ 40 * 436421 * 2
def baseEnd_436421 : Nat := 132796290794632435277299

theorem tailTrace_436421 : CollatzResearch.WordTrace tailWord_436421 prefixEnd_436421 132796290794632435277299 := by
  unfold tailWord_436421
  simp only [CollatzResearch.WordTrace]
  refine ⟨15917581551928726617893117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10611721034619151078595411 15917581551928726617893117)
  ·
    refine ⟨5969093081973272481709919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15917581551928726617893117 5969093081973272481709919)
    ·
      refine ⟨8953639622959908722564879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5969093081973272481709919 8953639622959908722564879)
      ·
        refine ⟨13430459434439863083847319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8953639622959908722564879 13430459434439863083847319)
        ·
          refine ⟨20145689151659794625770979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13430459434439863083847319 20145689151659794625770979)
          ·
            refine ⟨30218533727489691938656469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20145689151659794625770979 30218533727489691938656469)
            ·
              refine ⟨708246884238039654812261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 30218533727489691938656469 708246884238039654812261)
              ·
                refine ⟨132796290794632435277299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 708246884238039654812261 132796290794632435277299)
                ·
                  rfl

theorem cell19_436421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_436421 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436421 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436421 prefixEnd_436421 := by exact prefixLift 436421
  have htrace : WordTrace (prefixWord ++ tailWord_436421) baseStart_436421 baseEnd_436421 := by
    simpa [prefixWord, tailWord_436421, baseEnd_436421] using wordTrace_append hprefix tailTrace_436421
  have hstable : (prefixWord ++ tailWord_436421).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436421).length < 2 ^ (prefixWord ++ tailWord_436421).sum := by decide
  have hdescent : baseEnd_436421 < baseStart_436421 := by decide
  rcases family_descends (prefixWord ++ tailWord_436421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436497 : List Nat := [1, 2, 2, 1, 1, 6, 1, 5]
def baseStart_436497 : Nat := 118140960795 + 436497 * 2 ^ 59
def prefixEnd_436497 : Nat := 4983230072969 + 3 ^ 40 * 436497 * 2
def baseEnd_436497 : Nat := 132819416441886777588203

theorem tailTrace_436497 : CollatzResearch.WordTrace tailWord_436497 prefixEnd_436497 132819416441886777588203 := by
  unfold tailWord_436497
  simp only [CollatzResearch.WordTrace]
  refine ⟨15920353499653391597659745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10613568999768927731773163 15920353499653391597659745)
  ·
    refine ⟨11940265124740043698244809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15920353499653391597659745 11940265124740043698244809)
    ·
      refine ⟨8955198843555032773683607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11940265124740043698244809 8955198843555032773683607)
      ·
        refine ⟨13432798265332549160525411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8955198843555032773683607 13432798265332549160525411)
        ·
          refine ⟨20149197397998823740788117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13432798265332549160525411 20149197397998823740788117)
          ·
            refine ⟨944493628031194862849443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20149197397998823740788117 944493628031194862849443)
            ·
              refine ⟨1416740442046792294274165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 944493628031194862849443 1416740442046792294274165)
              ·
                refine ⟨132819416441886777588203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1416740442046792294274165 132819416441886777588203)
                ·
                  rfl

theorem cell19_436497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_436497 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436497 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436497 prefixEnd_436497 := by exact prefixLift 436497
  have htrace : WordTrace (prefixWord ++ tailWord_436497) baseStart_436497 baseEnd_436497 := by
    simpa [prefixWord, tailWord_436497, baseEnd_436497] using wordTrace_append hprefix tailTrace_436497
  have hstable : (prefixWord ++ tailWord_436497).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436497).length < 2 ^ (prefixWord ++ tailWord_436497).sum := by decide
  have hdescent : baseEnd_436497 < baseStart_436497 := by decide
  rcases family_descends (prefixWord ++ tailWord_436497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436514 : List Nat := [3, 3, 1, 1, 3, 3, 5]
def baseStart_436514 : Nat := 118140960795 + 436514 * 2 ^ 59
def prefixEnd_436514 : Nat := 4983230072969 + 3 ^ 40 * 436514 * 2
def baseEnd_436514 : Nat := 44274863094678591736793

theorem tailTrace_436514 : CollatzResearch.WordTrace tailWord_436514 prefixEnd_436514 44274863094678591736793 := by
  unfold tailWord_436514
  simp only [CollatzResearch.WordTrace]
  refine ⟨3980243385147950875257149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10613982360394535667352397 3980243385147950875257149)
  ·
    refine ⟨1492591269430481578221431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3980243385147950875257149 1492591269430481578221431)
    ·
      refine ⟨2238886904145722367332147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1492591269430481578221431 2238886904145722367332147)
      ·
        refine ⟨3358330356218583550998221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2238886904145722367332147 3358330356218583550998221)
        ·
          refine ⟨1259373883581968831624333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3358330356218583550998221 1259373883581968831624333)
          ·
            refine ⟨472265206343238311859125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1259373883581968831624333 472265206343238311859125)
            ·
              refine ⟨44274863094678591736793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 472265206343238311859125 44274863094678591736793)
              ·
                rfl

theorem cell19_436514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 5].length) (baseStart_436514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436514 prefixEnd_436514 := by exact prefixLift 436514
  have htrace : WordTrace (prefixWord ++ tailWord_436514) baseStart_436514 baseEnd_436514 := by
    simpa [prefixWord, tailWord_436514, baseEnd_436514] using wordTrace_append hprefix tailTrace_436514
  have hstable : (prefixWord ++ tailWord_436514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436514).length < 2 ^ (prefixWord ++ tailWord_436514).sum := by decide
  have hdescent : baseEnd_436514 < baseStart_436514 := by decide
  rcases family_descends (prefixWord ++ tailWord_436514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436516 : List Nat := [2, 3, 1, 3, 1, 2, 7]
def baseStart_436516 : Nat := 118140960795 + 436516 * 2 ^ 59
def prefixEnd_436516 : Nat := 4983230072969 + 3 ^ 40 * 436516 * 2
def baseEnd_436516 : Nat := 44275065951233454388643

theorem tailTrace_436516 : CollatzResearch.WordTrace tailWord_436516 prefixEnd_436516 44275065951233454388643 := by
  unfold tailWord_436516
  simp only [CollatzResearch.WordTrace]
  refine ⟨7960523243292278921300701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10614030991056371895067601 7960523243292278921300701)
  ·
    refine ⟨2985196216234604595487763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7960523243292278921300701 2985196216234604595487763)
    ·
      refine ⟨4477794324351906893231645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2985196216234604595487763 4477794324351906893231645)
      ·
        refine ⟨1679172871631965084961867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4477794324351906893231645 1679172871631965084961867)
        ·
          refine ⟨2518759307447947627442801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1679172871631965084961867 2518759307447947627442801)
          ·
            refine ⟨1889069480585960720582101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2518759307447947627442801 1889069480585960720582101)
            ·
              refine ⟨44275065951233454388643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1889069480585960720582101 44275065951233454388643)
              ·
                rfl

theorem cell19_436516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 7].length) (baseStart_436516 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436516 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436516 prefixEnd_436516 := by exact prefixLift 436516
  have htrace : WordTrace (prefixWord ++ tailWord_436516) baseStart_436516 baseEnd_436516 := by
    simpa [prefixWord, tailWord_436516, baseEnd_436516] using wordTrace_append hprefix tailTrace_436516
  have hstable : (prefixWord ++ tailWord_436516).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436516).length < 2 ^ (prefixWord ++ tailWord_436516).sum := by decide
  have hdescent : baseEnd_436516 < baseStart_436516 := by decide
  rcases family_descends (prefixWord ++ tailWord_436516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436588 : List Nat := [2, 2, 1, 1, 7, 1, 1, 4]
def baseStart_436588 : Nat := 118140960795 + 436588 * 2 ^ 59
def prefixEnd_436588 : Nat := 4983230072969 + 3 ^ 40 * 436588 * 2
def baseEnd_436588 : Nat := 132847106361625529565733

theorem tailTrace_436588 : CollatzResearch.WordTrace tailWord_436588 prefixEnd_436588 132847106361625529565733 := by
  unfold tailWord_436588
  simp only [CollatzResearch.WordTrace]
  refine ⟨7961836271161857069611209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10615781694882476092814945 7961836271161857069611209)
  ·
    refine ⟨5971377203371392802208407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7961836271161857069611209 5971377203371392802208407)
    ·
      refine ⟨8957065805057089203312611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5971377203371392802208407 8957065805057089203312611)
      ·
        refine ⟨13435598707585633804968917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8957065805057089203312611 13435598707585633804968917)
        ·
          refine ⟨314896844709038292303959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 13435598707585633804968917 314896844709038292303959)
          ·
            refine ⟨472345267063557438455939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314896844709038292303959 472345267063557438455939)
            ·
              refine ⟨708517900595336157683909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472345267063557438455939 708517900595336157683909)
              ·
                refine ⟨132847106361625529565733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 708517900595336157683909 132847106361625529565733)
                ·
                  rfl

theorem cell19_436588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 4].length) (baseStart_436588 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436588 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436588 prefixEnd_436588 := by exact prefixLift 436588
  have htrace : WordTrace (prefixWord ++ tailWord_436588) baseStart_436588 baseEnd_436588 := by
    simpa [prefixWord, tailWord_436588, baseEnd_436588] using wordTrace_append hprefix tailTrace_436588
  have hstable : (prefixWord ++ tailWord_436588).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436588).length < 2 ^ (prefixWord ++ tailWord_436588).sum := by decide
  have hdescent : baseEnd_436588 < baseStart_436588 := by decide
  rcases family_descends (prefixWord ++ tailWord_436588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436592 : List Nat := [2, 1, 1, 1, 4, 3, 3, 4]
def baseStart_436592 : Nat := 118140960795 + 436592 * 2 ^ 59
def prefixEnd_436592 : Nat := 4983230072969 + 3 ^ 40 * 436592 * 2
def baseEnd_436592 : Nat := 132848323500954705476833

theorem tailTrace_436592 : CollatzResearch.WordTrace tailWord_436592 prefixEnd_436592 132848323500954705476833 := by
  unfold tailWord_436592
  simp only [CollatzResearch.WordTrace]
  refine ⟨7961909217154611411184015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10615878956206148548245353 7961909217154611411184015)
  ·
    refine ⟨11942863825731917116776023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7961909217154611411184015 11942863825731917116776023)
    ·
      refine ⟨17914295738597875675164035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11942863825731917116776023 17914295738597875675164035)
      ·
        refine ⟨26871443607896813512746053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17914295738597875675164035 26871443607896813512746053)
        ·
          refine ⟨5038395676480652533639885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26871443607896813512746053 5038395676480652533639885)
          ·
            refine ⟨1889398378680244700114957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5038395676480652533639885 1889398378680244700114957)
            ·
              refine ⟨708524392005091762543109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1889398378680244700114957 708524392005091762543109)
              ·
                refine ⟨132848323500954705476833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 708524392005091762543109 132848323500954705476833)
                ·
                  rfl

theorem cell19_436592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_436592 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436592 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436592 prefixEnd_436592 := by exact prefixLift 436592
  have htrace : WordTrace (prefixWord ++ tailWord_436592) baseStart_436592 baseEnd_436592 := by
    simpa [prefixWord, tailWord_436592, baseEnd_436592] using wordTrace_append hprefix tailTrace_436592
  have hstable : (prefixWord ++ tailWord_436592).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436592).length < 2 ^ (prefixWord ++ tailWord_436592).sum := by decide
  have hdescent : baseEnd_436592 < baseStart_436592 := by decide
  rcases family_descends (prefixWord ++ tailWord_436592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436628 : List Nat := [2, 4, 2, 1, 3, 1, 6]
def baseStart_436628 : Nat := 118140960795 + 436628 * 2 ^ 59
def prefixEnd_436628 : Nat := 4983230072969 + 3 ^ 40 * 436628 * 2
def baseEnd_436628 : Nat := 44286425918305762892245

theorem tailTrace_436628 : CollatzResearch.WordTrace tailWord_436628 prefixEnd_436628 44286425918305762892245 := by
  unfold tailWord_436628
  simp only [CollatzResearch.WordTrace]
  refine ⟨7962565731089400485339269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10616754308119200647119025 7962565731089400485339269)
  ·
    refine ⟨1492981074579262591001113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7962565731089400485339269 1492981074579262591001113)
    ·
      refine ⟨1119735805934446943250835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1492981074579262591001113 1119735805934446943250835)
      ·
        refine ⟨1679603708901670414876253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1119735805934446943250835 1679603708901670414876253)
        ·
          refine ⟨629851390838126405578595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1679603708901670414876253 629851390838126405578595)
          ·
            refine ⟨944777086257189608367893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629851390838126405578595 944777086257189608367893)
            ·
              refine ⟨44286425918305762892245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 944777086257189608367893 44286425918305762892245)
              ·
                rfl

theorem cell19_436628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 6].length) (baseStart_436628 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436628 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436628 prefixEnd_436628 := by exact prefixLift 436628
  have htrace : WordTrace (prefixWord ++ tailWord_436628) baseStart_436628 baseEnd_436628 := by
    simpa [prefixWord, tailWord_436628, baseEnd_436628] using wordTrace_append hprefix tailTrace_436628
  have hstable : (prefixWord ++ tailWord_436628).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436628).length < 2 ^ (prefixWord ++ tailWord_436628).sum := by decide
  have hdescent : baseEnd_436628 < baseStart_436628 := by decide
  rcases family_descends (prefixWord ++ tailWord_436628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436660 : List Nat := [2, 5, 2, 2, 1, 2, 2, 3]
def baseStart_436660 : Nat := 118140960795 + 436660 * 2 ^ 59
def prefixEnd_436660 : Nat := 4983230072969 + 3 ^ 40 * 436660 * 2
def baseEnd_436660 : Nat := 132869014869550695965537

theorem tailTrace_436660 : CollatzResearch.WordTrace tailWord_436660 prefixEnd_436660 132869014869550695965537 := by
  unfold tailWord_436660
  simp only [CollatzResearch.WordTrace]
  refine ⟨7963149299031435217921717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10617532398708580290562289 7963149299031435217921717)
  ·
    refine ⟨746545246784197051680161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7963149299031435217921717 746545246784197051680161)
    ·
      refine ⟨559908935088147788760121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 746545246784197051680161 559908935088147788760121)
      ·
        refine ⟨419931701316110841570091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 559908935088147788760121 419931701316110841570091)
        ·
          refine ⟨629897551974166262355137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419931701316110841570091 629897551974166262355137)
          ·
            refine ⟨472423163980624696766353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 629897551974166262355137 472423163980624696766353)
            ·
              refine ⟨354317372985468522574765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472423163980624696766353 354317372985468522574765)
              ·
                refine ⟨132869014869550695965537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 354317372985468522574765 132869014869550695965537)
                ·
                  rfl

theorem cell19_436660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_436660 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436660 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436660 prefixEnd_436660 := by exact prefixLift 436660
  have htrace : WordTrace (prefixWord ++ tailWord_436660) baseStart_436660 baseEnd_436660 := by
    simpa [prefixWord, tailWord_436660, baseEnd_436660] using wordTrace_append hprefix tailTrace_436660
  have hstable : (prefixWord ++ tailWord_436660).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436660).length < 2 ^ (prefixWord ++ tailWord_436660).sum := by decide
  have hdescent : baseEnd_436660 < baseStart_436660 := by decide
  rcases family_descends (prefixWord ++ tailWord_436660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436759 : List Nat := [1, 1, 3, 6, 1, 2, 1, 4]
def baseStart_436759 : Nat := 118140960795 + 436759 * 2 ^ 59
def prefixEnd_436759 : Nat := 4983230072969 + 3 ^ 40 * 436759 * 2
def baseEnd_436759 : Nat := 132899139067947799765267

theorem tailTrace_436759 : CollatzResearch.WordTrace tailWord_436759 prefixEnd_436759 132899139067947799765267 := by
  unfold tailWord_436759
  simp only [CollatzResearch.WordTrace]
  refine ⟨15929909424704210343697331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10619939616469473562464887 15929909424704210343697331)
  ·
    refine ⟨23894864137056315515545997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15929909424704210343697331 23894864137056315515545997)
    ·
      refine ⟨8960574051396118318329749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23894864137056315515545997 8960574051396118318329749)
      ·
        refine ⟨420026908659193046171707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8960574051396118318329749 420026908659193046171707)
        ·
          refine ⟨630040362988789569257561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420026908659193046171707 630040362988789569257561)
          ·
            refine ⟨472530272241592176943171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 630040362988789569257561 472530272241592176943171)
            ·
              refine ⟨708795408362388265414757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472530272241592176943171 708795408362388265414757)
              ·
                refine ⟨132899139067947799765267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 708795408362388265414757 132899139067947799765267)
                ·
                  rfl

theorem cell19_436759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 4].length) (baseStart_436759 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436759 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436759 prefixEnd_436759 := by exact prefixLift 436759
  have htrace : WordTrace (prefixWord ++ tailWord_436759) baseStart_436759 baseEnd_436759 := by
    simpa [prefixWord, tailWord_436759, baseEnd_436759] using wordTrace_append hprefix tailTrace_436759
  have hstable : (prefixWord ++ tailWord_436759).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436759).length < 2 ^ (prefixWord ++ tailWord_436759).sum := by decide
  have hdescent : baseEnd_436759 < baseStart_436759 := by decide
  rcases family_descends (prefixWord ++ tailWord_436759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436784 : List Nat := [2, 1, 1, 1, 2, 3, 2, 7]
def baseStart_436784 : Nat := 118140960795 + 436784 * 2 ^ 59
def prefixEnd_436784 : Nat := 4983230072969 + 3 ^ 40 * 436784 * 2
def baseEnd_436784 : Nat := 132906746188755149209643

theorem tailTrace_436784 : CollatzResearch.WordTrace tailWord_436784 prefixEnd_436784 132906746188755149209643 := by
  unfold tailWord_436784
  simp only [CollatzResearch.WordTrace]
  refine ⟨7965410624806819806678703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10620547499742426408904937 7965410624806819806678703)
  ·
    refine ⟨11948115937210229710018055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7965410624806819806678703 11948115937210229710018055)
    ·
      refine ⟨17922173905815344565027083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11948115937210229710018055 17922173905815344565027083)
      ·
        refine ⟨26883260858723016847540625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17922173905815344565027083 26883260858723016847540625)
        ·
          refine ⟨20162445644042262635655469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26883260858723016847540625 20162445644042262635655469)
          ·
            refine ⟨7560917116515848488370801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20162445644042262635655469 7560917116515848488370801)
            ·
              refine ⟨5670687837386886366278101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7560917116515848488370801 5670687837386886366278101)
              ·
                refine ⟨132906746188755149209643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5670687837386886366278101 132906746188755149209643)
                ·
                  rfl

theorem cell19_436784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_436784 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436784 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436784 prefixEnd_436784 := by exact prefixLift 436784
  have htrace : WordTrace (prefixWord ++ tailWord_436784) baseStart_436784 baseEnd_436784 := by
    simpa [prefixWord, tailWord_436784, baseEnd_436784] using wordTrace_append hprefix tailTrace_436784
  have hstable : (prefixWord ++ tailWord_436784).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436784).length < 2 ^ (prefixWord ++ tailWord_436784).sum := by decide
  have hdescent : baseEnd_436784 < baseStart_436784 := by decide
  rcases family_descends (prefixWord ++ tailWord_436784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436801 : List Nat := [1, 2, 5, 1, 1, 3, 6]
def baseStart_436801 : Nat := 118140960795 + 436801 * 2 ^ 59
def prefixEnd_436801 : Nat := 4983230072969 + 3 ^ 40 * 436801 * 2
def baseEnd_436801 : Nat := 44303973010301382277273

theorem tailTrace_436801 : CollatzResearch.WordTrace tailWord_436801 prefixEnd_436801 44303973010301382277273 := by
  unfold tailWord_436801
  simp only [CollatzResearch.WordTrace]
  refine ⟨15931441290552051516726257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10620960860368034344484171 15931441290552051516726257)
  ·
    refine ⟨11948580967914038637544693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15931441290552051516726257 11948580967914038637544693)
    ·
      refine ⟨1120179465741941122269815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11948580967914038637544693 1120179465741941122269815)
      ·
        refine ⟨1680269198612911683404723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1120179465741941122269815 1680269198612911683404723)
        ·
          refine ⟨2520403797919367525107085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1680269198612911683404723 2520403797919367525107085)
          ·
            refine ⟨945151424219762821915157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2520403797919367525107085 945151424219762821915157)
            ·
              refine ⟨44303973010301382277273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 945151424219762821915157 44303973010301382277273)
              ·
                rfl

theorem cell19_436801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 6].length) (baseStart_436801 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436801 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436801 prefixEnd_436801 := by exact prefixLift 436801
  have htrace : WordTrace (prefixWord ++ tailWord_436801) baseStart_436801 baseEnd_436801 := by
    simpa [prefixWord, tailWord_436801, baseEnd_436801] using wordTrace_append hprefix tailTrace_436801
  have hstable : (prefixWord ++ tailWord_436801).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436801).length < 2 ^ (prefixWord ++ tailWord_436801).sum := by decide
  have hdescent : baseEnd_436801 < baseStart_436801 := by decide
  rcases family_descends (prefixWord ++ tailWord_436801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436854 : List Nat := [5, 1, 1, 2, 4, 1, 5]
def baseStart_436854 : Nat := 118140960795 + 436854 * 2 ^ 59
def prefixEnd_436854 : Nat := 4983230072969 + 3 ^ 40 * 436854 * 2
def baseEnd_436854 : Nat := 44309348709005242551299

theorem tailTrace_436854 : CollatzResearch.WordTrace tailWord_436854 prefixEnd_436854 44309348709005242551299 := by
  unfold tailWord_436854
  simp only [CollatzResearch.WordTrace]
  refine ⟨995835897460002598025351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10622249572906694378937077 995835897460002598025351)
  ·
    refine ⟨1493753846190003897038027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 995835897460002598025351 1493753846190003897038027)
    ·
      refine ⟨2240630769285005845557041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1493753846190003897038027 2240630769285005845557041)
      ·
        refine ⟨1680473076963754384167781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2240630769285005845557041 1680473076963754384167781)
        ·
          refine ⟨315088701930703947031459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1680473076963754384167781 315088701930703947031459)
          ·
            refine ⟨472633052896055920547189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315088701930703947031459 472633052896055920547189)
            ·
              refine ⟨44309348709005242551299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 472633052896055920547189 44309348709005242551299)
              ·
                rfl

theorem cell19_436854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 5].length) (baseStart_436854 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436854 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436854 prefixEnd_436854 := by exact prefixLift 436854
  have htrace : WordTrace (prefixWord ++ tailWord_436854) baseStart_436854 baseEnd_436854 := by
    simpa [prefixWord, tailWord_436854, baseEnd_436854] using wordTrace_append hprefix tailTrace_436854
  have hstable : (prefixWord ++ tailWord_436854).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436854).length < 2 ^ (prefixWord ++ tailWord_436854).sum := by decide
  have hdescent : baseEnd_436854 < baseStart_436854 := by decide
  rcases family_descends (prefixWord ++ tailWord_436854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436860 : List Nat := [2, 2, 2, 1, 1, 2, 9]
def baseStart_436860 : Nat := 118140960795 + 436860 * 2 ^ 59
def prefixEnd_436860 : Nat := 4983230072969 + 3 ^ 40 * 436860 * 2
def baseEnd_436860 : Nat := 44309957278669830506849

theorem tailTrace_436860 : CollatzResearch.WordTrace tailWord_436860 prefixEnd_436860 44309957278669830506849 := by
  unfold tailWord_436860
  simp only [CollatzResearch.WordTrace]
  refine ⟨7966796598669152296562017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10622395464892203062082689 7966796598669152296562017)
  ·
    refine ⟨5975097449001864222421513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7966796598669152296562017 5975097449001864222421513)
    ·
      refine ⟨4481323086751398166816135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5975097449001864222421513 4481323086751398166816135)
      ·
        refine ⟨6721984630127097250224203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4481323086751398166816135 6721984630127097250224203)
        ·
          refine ⟨10082976945190645875336305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6721984630127097250224203 10082976945190645875336305)
          ·
            refine ⟨7562232708892984406502229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10082976945190645875336305 7562232708892984406502229)
            ·
              refine ⟨44309957278669830506849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7562232708892984406502229 44309957278669830506849)
              ·
                rfl

theorem cell19_436860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 9].length) (baseStart_436860 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436860 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436860 prefixEnd_436860 := by exact prefixLift 436860
  have htrace : WordTrace (prefixWord ++ tailWord_436860) baseStart_436860 baseEnd_436860 := by
    simpa [prefixWord, tailWord_436860, baseEnd_436860] using wordTrace_append hprefix tailTrace_436860
  have hstable : (prefixWord ++ tailWord_436860).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436860).length < 2 ^ (prefixWord ++ tailWord_436860).sum := by decide
  have hdescent : baseEnd_436860 < baseStart_436860 := by decide
  rcases family_descends (prefixWord ++ tailWord_436860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436913 : List Nat := [1, 2, 2, 6, 2, 6]
def baseStart_436913 : Nat := 118140960795 + 436913 * 2 ^ 59
def prefixEnd_436913 : Nat := 4983230072969 + 3 ^ 40 * 436913 * 2
def baseEnd_436913 : Nat := 14771777659124563593625

theorem tailTrace_436913 : CollatzResearch.WordTrace tailWord_436913 prefixEnd_436913 14771777659124563593625 := by
  unfold tailWord_436913
  simp only [CollatzResearch.WordTrace]
  refine ⟨15935526266146294644803393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10623684177430863096535595 15935526266146294644803393)
  ·
    refine ⟨11951644699609720983602545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15935526266146294644803393 11951644699609720983602545)
    ·
      refine ⟨8963733524707290737701909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11951644699609720983602545 8963733524707290737701909)
      ·
        refine ⟨420175008970654253329777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8963733524707290737701909 420175008970654253329777)
        ·
          refine ⟨315131256727990689997333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420175008970654253329777 315131256727990689997333)
          ·
            refine ⟨14771777659124563593625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 315131256727990689997333 14771777659124563593625)
            ·
              rfl

theorem cell19_436913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 6].length) (baseStart_436913 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436913 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436913 prefixEnd_436913 := by exact prefixLift 436913
  have htrace : WordTrace (prefixWord ++ tailWord_436913) baseStart_436913 baseEnd_436913 := by
    simpa [prefixWord, tailWord_436913, baseEnd_436913] using wordTrace_append hprefix tailTrace_436913
  have hstable : (prefixWord ++ tailWord_436913).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436913).length < 2 ^ (prefixWord ++ tailWord_436913).sum := by decide
  have hdescent : baseEnd_436913 < baseStart_436913 := by decide
  rcases family_descends (prefixWord ++ tailWord_436913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436932 : List Nat := [2, 3, 3, 1, 1, 4, 1, 4]
def baseStart_436932 : Nat := 118140960795 + 436932 * 2 ^ 59
def prefixEnd_436932 : Nat := 4983230072969 + 3 ^ 40 * 436932 * 2
def baseEnd_436932 : Nat := 132951780343934657920351

theorem tailTrace_436932 : CollatzResearch.WordTrace tailWord_436932 prefixEnd_436932 132951780343934657920351 := by
  unfold tailWord_436932
  simp only [CollatzResearch.WordTrace]
  refine ⟨7968109626538730444872525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10624146168718307259830033 7968109626538730444872525)
  ·
    refine ⟨2988041109952023916827197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7968109626538730444872525 2988041109952023916827197)
    ·
      refine ⟨1120515416232008968810199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2988041109952023916827197 1120515416232008968810199)
      ·
        refine ⟨1680773124348013453215299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1120515416232008968810199 1680773124348013453215299)
        ·
          refine ⟨2521159686522020179822949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1680773124348013453215299 2521159686522020179822949)
          ·
            refine ⟨472717441222878783716803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2521159686522020179822949 472717441222878783716803)
            ·
              refine ⟨709076161834318175575205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472717441222878783716803 709076161834318175575205)
              ·
                refine ⟨132951780343934657920351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 709076161834318175575205 132951780343934657920351)
                ·
                  rfl

theorem cell19_436932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_436932 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436932 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436932 prefixEnd_436932 := by exact prefixLift 436932
  have htrace : WordTrace (prefixWord ++ tailWord_436932) baseStart_436932 baseEnd_436932 := by
    simpa [prefixWord, tailWord_436932, baseEnd_436932] using wordTrace_append hprefix tailTrace_436932
  have hstable : (prefixWord ++ tailWord_436932).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436932).length < 2 ^ (prefixWord ++ tailWord_436932).sum := by decide
  have hdescent : baseEnd_436932 < baseStart_436932 := by decide
  rcases family_descends (prefixWord ++ tailWord_436932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436949 : List Nat := [1, 3, 2, 5, 1, 1, 3, 3]
def baseStart_436949 : Nat := 118140960795 + 436949 * 2 ^ 59
def prefixEnd_436949 : Nat := 4983230072969 + 3 ^ 40 * 436949 * 2
def baseEnd_436949 : Nat := 132956953186083655542527

theorem tailTrace_436949 : CollatzResearch.WordTrace tailWord_436949 prefixEnd_436949 132956953186083655542527 := by
  unfold tailWord_436949
  simp only [CollatzResearch.WordTrace]
  refine ⟨15936839294015872793113901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10624559529343915195409267 15936839294015872793113901)
  ·
    refine ⟨5976314735255952297417713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15936839294015872793113901 5976314735255952297417713)
    ·
      refine ⟨4482236051441964223063285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5976314735255952297417713 4482236051441964223063285)
      ·
        refine ⟨420209629822684145912183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4482236051441964223063285 420209629822684145912183)
        ·
          refine ⟨630314444734026218868275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420209629822684145912183 630314444734026218868275)
          ·
            refine ⟨945471667101039328302413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630314444734026218868275 945471667101039328302413)
            ·
              refine ⟨354551875162889748113405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 945471667101039328302413 354551875162889748113405)
              ·
                refine ⟨132956953186083655542527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 354551875162889748113405 132956953186083655542527)
                ·
                  rfl

theorem cell19_436949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 3].length) (baseStart_436949 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436949 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436949 prefixEnd_436949 := by exact prefixLift 436949
  have htrace : WordTrace (prefixWord ++ tailWord_436949) baseStart_436949 baseEnd_436949 := by
    simpa [prefixWord, tailWord_436949, baseEnd_436949] using wordTrace_append hprefix tailTrace_436949
  have hstable : (prefixWord ++ tailWord_436949).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436949).length < 2 ^ (prefixWord ++ tailWord_436949).sum := by decide
  have hdescent : baseEnd_436949 < baseStart_436949 := by decide
  rcases family_descends (prefixWord ++ tailWord_436949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436953 : List Nat := [1, 2, 1, 2, 3, 2, 5, 3]
def baseStart_436953 : Nat := 118140960795 + 436953 * 2 ^ 59
def prefixEnd_436953 : Nat := 4983230072969 + 3 ^ 40 * 436953 * 2
def baseEnd_436953 : Nat := 132958170325412831453627

theorem tailTrace_436953 : CollatzResearch.WordTrace tailWord_436953 prefixEnd_436953 132958170325412831453627 := by
  unfold tailWord_436953
  simp only [CollatzResearch.WordTrace]
  refine ⟨15936985186001381476259513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10624656790667587650839675 15936985186001381476259513)
  ·
    refine ⟨11952738889501036107194635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15936985186001381476259513 11952738889501036107194635)
    ·
      refine ⟨17929108334251554160791953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11952738889501036107194635 17929108334251554160791953)
      ·
        refine ⟨13446831250688665620593965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17929108334251554160791953 13446831250688665620593965)
        ·
          refine ⟨5042561719008249607722737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13446831250688665620593965 5042561719008249607722737)
          ·
            refine ⟨3781921289256187205792053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5042561719008249607722737 3781921289256187205792053)
            ·
              refine ⟨354555120867767550543005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3781921289256187205792053 354555120867767550543005)
              ·
                refine ⟨132958170325412831453627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 354555120867767550543005 132958170325412831453627)
                ·
                  rfl

theorem cell19_436953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 3].length) (baseStart_436953 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436953 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436953 prefixEnd_436953 := by exact prefixLift 436953
  have htrace : WordTrace (prefixWord ++ tailWord_436953) baseStart_436953 baseEnd_436953 := by
    simpa [prefixWord, tailWord_436953, baseEnd_436953] using wordTrace_append hprefix tailTrace_436953
  have hstable : (prefixWord ++ tailWord_436953).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436953).length < 2 ^ (prefixWord ++ tailWord_436953).sum := by decide
  have hdescent : baseEnd_436953 < baseStart_436953 := by decide
  rcases family_descends (prefixWord ++ tailWord_436953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_436993 : List Nat := [1, 2, 4, 1, 1, 1, 1, 8]
def baseStart_436993 : Nat := 118140960795 + 436993 * 2 ^ 59
def prefixEnd_436993 : Nat := 4983230072969 + 3 ^ 40 * 436993 * 2
def baseEnd_436993 : Nat := 132970341718704590564629

theorem tailTrace_436993 : CollatzResearch.WordTrace tailWord_436993 prefixEnd_436993 132970341718704590564629 := by
  unfold tailWord_436993
  simp only [CollatzResearch.WordTrace]
  refine ⟨15938444105856468307715633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10625629403904312205143755 15938444105856468307715633)
  ·
    refine ⟨11953833079392351230786725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15938444105856468307715633 11953833079392351230786725)
    ·
      refine ⟨2241343702386065855772511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11953833079392351230786725 2241343702386065855772511)
      ·
        refine ⟨3362015553579098783658767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2241343702386065855772511 3362015553579098783658767)
        ·
          refine ⟨5043023330368648175488151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3362015553579098783658767 5043023330368648175488151)
          ·
            refine ⟨7564534995552972263232227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5043023330368648175488151 7564534995552972263232227)
            ·
              refine ⟨11346802493329458394848341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7564534995552972263232227 11346802493329458394848341)
              ·
                refine ⟨132970341718704590564629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11346802493329458394848341 132970341718704590564629)
                ·
                  rfl

theorem cell19_436993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_436993 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_436993 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_436993 prefixEnd_436993 := by exact prefixLift 436993
  have htrace : WordTrace (prefixWord ++ tailWord_436993) baseStart_436993 baseEnd_436993 := by
    simpa [prefixWord, tailWord_436993, baseEnd_436993] using wordTrace_append hprefix tailTrace_436993
  have hstable : (prefixWord ++ tailWord_436993).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_436993).length < 2 ^ (prefixWord ++ tailWord_436993).sum := by decide
  have hdescent : baseEnd_436993 < baseStart_436993 := by decide
  rcases family_descends (prefixWord ++ tailWord_436993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437105 : List Nat := [1, 2, 2, 2, 1, 6, 1, 4]
def baseStart_437105 : Nat := 118140960795 + 437105 * 2 ^ 59
def prefixEnd_437105 : Nat := 4983230072969 + 3 ^ 40 * 437105 * 2
def baseEnd_437105 : Nat := 133004421619921516075435

theorem tailTrace_437105 : CollatzResearch.WordTrace tailWord_437105 prefixEnd_437105 133004421619921516075435 := by
  unfold tailWord_437105
  simp only [CollatzResearch.WordTrace]
  refine ⟨15942529081450711435792769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10628352720967140957195179 15942529081450711435792769)
  ·
    refine ⟨11956896811088033576844577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15942529081450711435792769 11956896811088033576844577)
    ·
      refine ⟨8967672608316025182633433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11956896811088033576844577 8967672608316025182633433)
      ·
        refine ⟨6725754456237018886975075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8967672608316025182633433 6725754456237018886975075)
        ·
          refine ⟨10088631684355528330462613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6725754456237018886975075 10088631684355528330462613)
          ·
            refine ⟨472904610204165390490435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10088631684355528330462613 472904610204165390490435)
            ·
              refine ⟨709356915306248085735653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472904610204165390490435 709356915306248085735653)
              ·
                refine ⟨133004421619921516075435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 709356915306248085735653 133004421619921516075435)
                ·
                  rfl

theorem cell19_437105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 4].length) (baseStart_437105 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437105 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437105 prefixEnd_437105 := by exact prefixLift 437105
  have htrace : WordTrace (prefixWord ++ tailWord_437105) baseStart_437105 baseEnd_437105 := by
    simpa [prefixWord, tailWord_437105, baseEnd_437105] using wordTrace_append hprefix tailTrace_437105
  have hstable : (prefixWord ++ tailWord_437105).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437105).length < 2 ^ (prefixWord ++ tailWord_437105).sum := by decide
  have hdescent : baseEnd_437105 < baseStart_437105 := by decide
  rcases family_descends (prefixWord ++ tailWord_437105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437107 : List Nat := [1, 1, 1, 2, 2, 1, 7, 4]
def baseStart_437107 : Nat := 118140960795 + 437107 * 2 ^ 59
def prefixEnd_437107 : Nat := 4983230072969 + 3 ^ 40 * 437107 * 2
def baseEnd_437107 : Nat := 133005030189586104030985

theorem tailTrace_437107 : CollatzResearch.WordTrace tailWord_437107 prefixEnd_437107 133005030189586104030985 := by
  unfold tailWord_437107
  simp only [CollatzResearch.WordTrace]
  refine ⟨15942602027443465777365575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10628401351628977184910383 15942602027443465777365575)
  ·
    refine ⟨23913903041165198666048363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15942602027443465777365575 23913903041165198666048363)
    ·
      refine ⟨35870854561747797999072545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23913903041165198666048363 35870854561747797999072545)
      ·
        refine ⟨26903140921310848499304409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35870854561747797999072545 26903140921310848499304409)
        ·
          refine ⟨20177355690983136374478307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26903140921310848499304409 20177355690983136374478307)
          ·
            refine ⟨30266033536474704561717461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20177355690983136374478307 30266033536474704561717461)
            ·
              refine ⟨709360161011125888165253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 30266033536474704561717461 709360161011125888165253)
              ·
                refine ⟨133005030189586104030985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 709360161011125888165253 133005030189586104030985)
                ·
                  rfl

theorem cell19_437107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_437107 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437107 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437107 prefixEnd_437107 := by exact prefixLift 437107
  have htrace : WordTrace (prefixWord ++ tailWord_437107) baseStart_437107 baseEnd_437107 := by
    simpa [prefixWord, tailWord_437107, baseEnd_437107] using wordTrace_append hprefix tailTrace_437107
  have hstable : (prefixWord ++ tailWord_437107).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437107).length < 2 ^ (prefixWord ++ tailWord_437107).sum := by decide
  have hdescent : baseEnd_437107 < baseStart_437107 := by decide
  rcases family_descends (prefixWord ++ tailWord_437107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437181 : List Nat := [1, 4, 1, 2, 4, 1, 1, 5]
def baseStart_437181 : Nat := 118140960795 + 437181 * 2 ^ 59
def prefixEnd_437181 : Nat := 4983230072969 + 3 ^ 40 * 437181 * 2
def baseEnd_437181 : Nat := 133027547267175858386339

theorem tailTrace_437181 : CollatzResearch.WordTrace tailWord_437181 prefixEnd_437181 133027547267175858386339 := by
  unfold tailWord_437181
  simp only [CollatzResearch.WordTrace]
  refine ⟨15945301029175376415559397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10630200686116917610372931 15945301029175376415559397)
  ·
    refine ⟨2989743942970383077917387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15945301029175376415559397 2989743942970383077917387)
    ·
      refine ⟨4484615914455574616876081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2989743942970383077917387 4484615914455574616876081)
      ·
        refine ⟨3363461935841680962657061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4484615914455574616876081 3363461935841680962657061)
        ·
          refine ⟨630649112970315180498199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3363461935841680962657061 630649112970315180498199)
          ·
            refine ⟨945973669455472770747299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630649112970315180498199 945973669455472770747299)
            ·
              refine ⟨1418960504183209156120949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945973669455472770747299 1418960504183209156120949)
              ·
                refine ⟨133027547267175858386339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1418960504183209156120949 133027547267175858386339)
                ·
                  rfl

theorem cell19_437181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 5].length) (baseStart_437181 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437181 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437181 prefixEnd_437181 := by exact prefixLift 437181
  have htrace : WordTrace (prefixWord ++ tailWord_437181) baseStart_437181 baseEnd_437181 := by
    simpa [prefixWord, tailWord_437181, baseEnd_437181] using wordTrace_append hprefix tailTrace_437181
  have hstable : (prefixWord ++ tailWord_437181).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437181).length < 2 ^ (prefixWord ++ tailWord_437181).sum := by decide
  have hdescent : baseEnd_437181 < baseStart_437181 := by decide
  rcases family_descends (prefixWord ++ tailWord_437181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437238 : List Nat := [5, 1, 1, 1, 3, 1, 2, 5]
def baseStart_437238 : Nat := 118140960795 + 437238 * 2 ^ 59
def prefixEnd_437238 : Nat := 4983230072969 + 3 ^ 40 * 437238 * 2
def baseEnd_437238 : Nat := 133044891502616615119517

theorem tailTrace_437238 : CollatzResearch.WordTrace tailWord_437238 prefixEnd_437238 133044891502616615119517 := by
  unfold tailWord_437238
  simp only [CollatzResearch.WordTrace]
  refine ⟨996711249373054696899023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10631586659979250100256245 996711249373054696899023)
  ·
    refine ⟨1495066874059582045348535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 996711249373054696899023 1495066874059582045348535)
    ·
      refine ⟨2242600311089373068022803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1495066874059582045348535 2242600311089373068022803)
      ·
        refine ⟨3363900466634059602034205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2242600311089373068022803 3363900466634059602034205)
        ·
          refine ⟨1261462674987772350762827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3363900466634059602034205 1261462674987772350762827)
          ·
            refine ⟨1892194012481658526144241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1261462674987772350762827 1892194012481658526144241)
            ·
              refine ⟨1419145509361243894608181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1892194012481658526144241 1419145509361243894608181)
              ·
                refine ⟨133044891502616615119517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1419145509361243894608181 133044891502616615119517)
                ·
                  rfl

theorem cell19_437238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_437238 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437238 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437238 prefixEnd_437238 := by exact prefixLift 437238
  have htrace : WordTrace (prefixWord ++ tailWord_437238) baseStart_437238 baseEnd_437238 := by
    simpa [prefixWord, tailWord_437238, baseEnd_437238] using wordTrace_append hprefix tailTrace_437238
  have hstable : (prefixWord ++ tailWord_437238).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437238).length < 2 ^ (prefixWord ++ tailWord_437238).sum := by decide
  have hdescent : baseEnd_437238 < baseStart_437238 := by decide
  rcases family_descends (prefixWord ++ tailWord_437238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437390 : List Nat := [4, 1, 1, 3, 2, 2, 2, 4]
def baseStart_437390 : Nat := 118140960795 + 437390 * 2 ^ 59
def prefixEnd_437390 : Nat := 4983230072969 + 3 ^ 40 * 437390 * 2
def baseEnd_437390 : Nat := 133091142797125299741325

theorem tailTrace_437390 : CollatzResearch.WordTrace tailWord_437390 prefixEnd_437390 133091142797125299741325 := by
  unfold tailWord_437390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1994115485677275638739703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10635282590278803406611749 1994115485677275638739703)
  ·
    refine ⟨2991173228515913458109555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1994115485677275638739703 2991173228515913458109555)
    ·
      refine ⟨4486759842773870187164333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2991173228515913458109555 4486759842773870187164333)
      ·
        refine ⟨1682534941040201320186625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4486759842773870187164333 1682534941040201320186625)
        ·
          refine ⟨1261901205780150990139969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1682534941040201320186625 1261901205780150990139969)
          ·
            refine ⟨946425904335113242604977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1261901205780150990139969 946425904335113242604977)
            ·
              refine ⟨709819428251334931953733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946425904335113242604977 709819428251334931953733)
              ·
                refine ⟨133091142797125299741325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 709819428251334931953733 133091142797125299741325)
                ·
                  rfl

theorem cell19_437390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_437390 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437390 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437390 prefixEnd_437390 := by exact prefixLift 437390
  have htrace : WordTrace (prefixWord ++ tailWord_437390) baseStart_437390 baseEnd_437390 := by
    simpa [prefixWord, tailWord_437390, baseEnd_437390] using wordTrace_append hprefix tailTrace_437390
  have hstable : (prefixWord ++ tailWord_437390).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437390).length < 2 ^ (prefixWord ++ tailWord_437390).sum := by decide
  have hdescent : baseEnd_437390 < baseStart_437390 := by decide
  rcases family_descends (prefixWord ++ tailWord_437390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437428 : List Nat := [2, 5, 3, 9]
def baseStart_437428 : Nat := 118140960795 + 437428 * 2 ^ 59
def prefixEnd_437428 : Nat := 4983230072969 + 3 ^ 40 * 437428 * 2
def baseEnd_437428 : Nat := 1643243279268549023417

theorem tailTrace_437428 : CollatzResearch.WordTrace tailWord_437428 prefixEnd_437428 1643243279268549023417 := by
  unfold tailWord_437428
  simp only [CollatzResearch.WordTrace]
  refine ⟨7977154929640268799900469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10636206572853691733200625 7977154929640268799900469)
  ·
    refine ⟨747858274653775199990669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7977154929640268799900469 747858274653775199990669)
    ·
      refine ⟨280446852995165699996501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 747858274653775199990669 280446852995165699996501)
      ·
        refine ⟨1643243279268549023417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 9 280446852995165699996501 1643243279268549023417)
        ·
          rfl

theorem cell19_437428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 9].length) (baseStart_437428 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437428 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437428 prefixEnd_437428 := by exact prefixLift 437428
  have htrace : WordTrace (prefixWord ++ tailWord_437428) baseStart_437428 baseEnd_437428 := by
    simpa [prefixWord, tailWord_437428, baseEnd_437428] using wordTrace_append hprefix tailTrace_437428
  have hstable : (prefixWord ++ tailWord_437428).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437428).length < 2 ^ (prefixWord ++ tailWord_437428).sum := by decide
  have hdescent : baseEnd_437428 < baseStart_437428 := by decide
  rcases family_descends (prefixWord ++ tailWord_437428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437451 : List Nat := [1, 1, 1, 1, 3, 2, 2, 8]
def baseStart_437451 : Nat := 118140960795 + 437451 * 2 ^ 59
def prefixEnd_437451 : Nat := 4983230072969 + 3 ^ 40 * 437451 * 2
def baseEnd_437451 : Nat := 133109704171895232385603

theorem tailTrace_437451 : CollatzResearch.WordTrace tailWord_437451 prefixEnd_437451 133109704171895232385603 := by
  unfold tailWord_437451
  simp only [CollatzResearch.WordTrace]
  refine ⟨15955148738197212527888207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10636765825464808351925471 15955148738197212527888207)
  ·
    refine ⟨23932723107295818791832311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15955148738197212527888207 23932723107295818791832311)
    ·
      refine ⟨35899084660943728187748467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23932723107295818791832311 35899084660943728187748467)
      ·
        refine ⟨53848626991415592281622701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35899084660943728187748467 53848626991415592281622701)
        ·
          refine ⟨20193235121780847105608513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53848626991415592281622701 20193235121780847105608513)
          ·
            refine ⟨15144926341335635329206385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20193235121780847105608513 15144926341335635329206385)
            ·
              refine ⟨11358694756001726496904789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15144926341335635329206385 11358694756001726496904789)
              ·
                refine ⟨133109704171895232385603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11358694756001726496904789 133109704171895232385603)
                ·
                  rfl

theorem cell19_437451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_437451 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437451 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437451 prefixEnd_437451 := by exact prefixLift 437451
  have htrace : WordTrace (prefixWord ++ tailWord_437451) baseStart_437451 baseEnd_437451 := by
    simpa [prefixWord, tailWord_437451, baseEnd_437451] using wordTrace_append hprefix tailTrace_437451
  have hstable : (prefixWord ++ tailWord_437451).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437451).length < 2 ^ (prefixWord ++ tailWord_437451).sum := by decide
  have hdescent : baseEnd_437451 < baseStart_437451 := by decide
  rcases family_descends (prefixWord ++ tailWord_437451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437462 : List Nat := [5, 2, 1, 2, 2, 1, 3, 3]
def baseStart_437462 : Nat := 118140960795 + 437462 * 2 ^ 59
def prefixEnd_437462 : Nat := 4983230072969 + 3 ^ 40 * 437462 * 2
def baseEnd_437462 : Nat := 133113051305050466141129

theorem tailTrace_437462 : CollatzResearch.WordTrace tailWord_437462 prefixEnd_437462 133113051305050466141129 := by
  unfold tailWord_437462
  simp only [CollatzResearch.WordTrace]
  refine ⟨997221871322335087908665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10637033294104907604359093 997221871322335087908665)
  ·
    refine ⟨747916403491751315931499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 997221871322335087908665 747916403491751315931499)
    ·
      refine ⟨1121874605237626973897249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 747916403491751315931499 1121874605237626973897249)
      ·
        refine ⟨841405953928220230422937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1121874605237626973897249 841405953928220230422937)
        ·
          refine ⟨631054465446165172817203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 841405953928220230422937 631054465446165172817203)
          ·
            refine ⟨946581698169247759225805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631054465446165172817203 946581698169247759225805)
            ·
              refine ⟨354968136813467909709677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 946581698169247759225805 354968136813467909709677)
              ·
                refine ⟨133113051305050466141129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 354968136813467909709677 133113051305050466141129)
                ·
                  rfl

theorem cell19_437462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_437462 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437462 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437462 prefixEnd_437462 := by exact prefixLift 437462
  have htrace : WordTrace (prefixWord ++ tailWord_437462) baseStart_437462 baseEnd_437462 := by
    simpa [prefixWord, tailWord_437462, baseEnd_437462] using wordTrace_append hprefix tailTrace_437462
  have hstable : (prefixWord ++ tailWord_437462).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437462).length < 2 ^ (prefixWord ++ tailWord_437462).sum := by decide
  have hdescent : baseEnd_437462 < baseStart_437462 := by decide
  rcases family_descends (prefixWord ++ tailWord_437462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437487 : List Nat := [1, 1, 2, 1, 7, 1, 6]
def baseStart_437487 : Nat := 118140960795 + 437487 * 2 ^ 59
def prefixEnd_437487 : Nat := 4983230072969 + 3 ^ 40 * 437487 * 2
def baseEnd_437487 : Nat := 44373552808619271861835

theorem tailTrace_437487 : CollatzResearch.WordTrace tailWord_437487 prefixEnd_437487 44373552808619271861835 := by
  unfold tailWord_437487
  simp only [CollatzResearch.WordTrace]
  refine ⟨15956461766066790676198715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10637641177377860450799143 15956461766066790676198715)
  ·
    refine ⟨23934692649100186014298073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15956461766066790676198715 23934692649100186014298073)
    ·
      refine ⟨17951019486825139510723555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23934692649100186014298073 17951019486825139510723555)
      ·
        refine ⟨26926529230237709266085333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17951019486825139510723555 26926529230237709266085333)
        ·
          refine ⟨631090528833696310923875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 26926529230237709266085333 631090528833696310923875)
          ·
            refine ⟨946635793250544466385813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631090528833696310923875 946635793250544466385813)
            ·
              refine ⟨44373552808619271861835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 946635793250544466385813 44373552808619271861835)
              ·
                rfl

theorem cell19_437487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 6].length) (baseStart_437487 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437487 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437487 prefixEnd_437487 := by exact prefixLift 437487
  have htrace : WordTrace (prefixWord ++ tailWord_437487) baseStart_437487 baseEnd_437487 := by
    simpa [prefixWord, tailWord_437487, baseEnd_437487] using wordTrace_append hprefix tailTrace_437487
  have hstable : (prefixWord ++ tailWord_437487).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437487).length < 2 ^ (prefixWord ++ tailWord_437487).sum := by decide
  have hdescent : baseEnd_437487 < baseStart_437487 := by decide
  rcases family_descends (prefixWord ++ tailWord_437487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437544 : List Nat := [2, 1, 5, 1, 2, 1, 7]
def baseStart_437544 : Nat := 118140960795 + 437544 * 2 ^ 59
def prefixEnd_437544 : Nat := 4983230072969 + 3 ^ 40 * 437544 * 2
def baseEnd_437544 : Nat := 44379334220432857439561

theorem tailTrace_437544 : CollatzResearch.WordTrace tailWord_437544 prefixEnd_437544 44379334220432857439561 := by
  unfold tailWord_437544
  simp only [CollatzResearch.WordTrace]
  refine ⟨7979270363430144705511843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10639027151240192940682457 7979270363430144705511843)
  ·
    refine ⟨11968905545145217058267765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7979270363430144705511843 11968905545145217058267765)
    ·
      refine ⟨1122084894857364099212603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11968905545145217058267765 1122084894857364099212603)
      ·
        refine ⟨1683127342286046148818905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1122084894857364099212603 1683127342286046148818905)
        ·
          refine ⟨1262345506714534611614179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1683127342286046148818905 1262345506714534611614179)
          ·
            refine ⟨1893518260071801917421269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262345506714534611614179 1893518260071801917421269)
            ·
              refine ⟨44379334220432857439561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1893518260071801917421269 44379334220432857439561)
              ·
                rfl

theorem cell19_437544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 7].length) (baseStart_437544 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437544 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437544 prefixEnd_437544 := by exact prefixLift 437544
  have htrace : WordTrace (prefixWord ++ tailWord_437544) baseStart_437544 baseEnd_437544 := by
    simpa [prefixWord, tailWord_437544, baseEnd_437544] using wordTrace_append hprefix tailTrace_437544
  have hstable : (prefixWord ++ tailWord_437544).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437544).length < 2 ^ (prefixWord ++ tailWord_437544).sum := by decide
  have hdescent : baseEnd_437544 < baseStart_437544 := by decide
  rcases family_descends (prefixWord ++ tailWord_437544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437561 : List Nat := [1, 2, 1, 6, 2, 1, 2, 4]
def baseStart_437561 : Nat := 118140960795 + 437561 * 2 ^ 59
def prefixEnd_437561 : Nat := 4983230072969 + 3 ^ 40 * 437561 * 2
def baseEnd_437561 : Nat := 133143175503447569940859

theorem tailTrace_437561 : CollatzResearch.WordTrace tailWord_437561 prefixEnd_437561 133143175503447569940859 := by
  unfold tailWord_437561
  simp only [CollatzResearch.WordTrace]
  refine ⟨15959160767798701314392537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10639440511865800876261691 15959160767798701314392537)
  ·
    refine ⟨11969370575849025985794403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15959160767798701314392537 11969370575849025985794403)
    ·
      refine ⟨17954055863773538978691605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11969370575849025985794403 17954055863773538978691605)
      ·
        refine ⟨841596368614384639626169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17954055863773538978691605 841596368614384639626169)
        ·
          refine ⟨631197276460788479719627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 841596368614384639626169 631197276460788479719627)
          ·
            refine ⟨946795914691182719579441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631197276460788479719627 946795914691182719579441)
            ·
              refine ⟨710096936018387039684581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946795914691182719579441 710096936018387039684581)
              ·
                refine ⟨133143175503447569940859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 710096936018387039684581 133143175503447569940859)
                ·
                  rfl

theorem cell19_437561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 4].length) (baseStart_437561 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437561 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437561 prefixEnd_437561 := by exact prefixLift 437561
  have htrace : WordTrace (prefixWord ++ tailWord_437561) baseStart_437561 baseEnd_437561 := by
    simpa [prefixWord, tailWord_437561, baseEnd_437561] using wordTrace_append hprefix tailTrace_437561
  have hstable : (prefixWord ++ tailWord_437561).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437561).length < 2 ^ (prefixWord ++ tailWord_437561).sum := by decide
  have hdescent : baseEnd_437561 < baseStart_437561 := by decide
  rcases family_descends (prefixWord ++ tailWord_437561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437584 : List Nat := [2, 1, 1, 1, 1, 5, 1, 7]
def baseStart_437584 : Nat := 118140960795 + 437584 * 2 ^ 59
def prefixEnd_437584 : Nat := 4983230072969 + 3 ^ 40 * 437584 * 2
def baseEnd_437584 : Nat := 133150174054590331429685

theorem tailTrace_437584 : CollatzResearch.WordTrace tailWord_437584 prefixEnd_437584 133150174054590331429685 := by
  unfold tailWord_437584
  simp only [CollatzResearch.WordTrace]
  refine ⟨7979999823357688121239903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10639999764476917494986537 7979999823357688121239903)
  ·
    refine ⟨11969999735036532181859855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7979999823357688121239903 11969999735036532181859855)
    ·
      refine ⟨17954999602554798272789783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11969999735036532181859855 17954999602554798272789783)
      ·
        refine ⟨26932499403832197409184675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17954999602554798272789783 26932499403832197409184675)
        ·
          refine ⟨40398749105748296113777013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26932499403832197409184675 40398749105748296113777013)
          ·
            refine ⟨3787382728663902760666595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40398749105748296113777013 3787382728663902760666595)
            ·
              refine ⟨5681074092995854140999893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3787382728663902760666595 5681074092995854140999893)
              ·
                refine ⟨133150174054590331429685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5681074092995854140999893 133150174054590331429685)
                ·
                  rfl

theorem cell19_437584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_437584 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437584 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437584 prefixEnd_437584 := by exact prefixLift 437584
  have htrace : WordTrace (prefixWord ++ tailWord_437584) baseStart_437584 baseEnd_437584 := by
    simpa [prefixWord, tailWord_437584, baseEnd_437584] using wordTrace_append hprefix tailTrace_437584
  have hstable : (prefixWord ++ tailWord_437584).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437584).length < 2 ^ (prefixWord ++ tailWord_437584).sum := by decide
  have hdescent : baseEnd_437584 < baseStart_437584 := by decide
  rcases family_descends (prefixWord ++ tailWord_437584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437597 : List Nat := [1, 4, 5, 1, 1, 7]
def baseStart_437597 : Nat := 118140960795 + 437597 * 2 ^ 59
def prefixEnd_437597 : Nat := 4983230072969 + 3 ^ 40 * 437597 * 2
def baseEnd_437597 : Nat := 14794903306378905904529

theorem tailTrace_437597 : CollatzResearch.WordTrace tailWord_437597 prefixEnd_437597 14794903306378905904529 := by
  unfold tailWord_437597
  simp only [CollatzResearch.WordTrace]
  refine ⟨15960473795668279462703045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10640315863778852975135363 15960473795668279462703045)
  ·
    refine ⟨2992588836687802399256821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15960473795668279462703045 2992588836687802399256821)
    ·
      refine ⟨280555203439481474930327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2992588836687802399256821 280555203439481474930327)
      ·
        refine ⟨420832805159222212395491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280555203439481474930327 420832805159222212395491)
        ·
          refine ⟨631249207738833318593237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420832805159222212395491 631249207738833318593237)
          ·
            refine ⟨14794903306378905904529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 631249207738833318593237 14794903306378905904529)
            ·
              rfl

theorem cell19_437597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 7].length) (baseStart_437597 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437597 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437597 prefixEnd_437597 := by exact prefixLift 437597
  have htrace : WordTrace (prefixWord ++ tailWord_437597) baseStart_437597 baseEnd_437597 := by
    simpa [prefixWord, tailWord_437597, baseEnd_437597] using wordTrace_append hprefix tailTrace_437597
  have hstable : (prefixWord ++ tailWord_437597).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437597).length < 2 ^ (prefixWord ++ tailWord_437597).sum := by decide
  have hdescent : baseEnd_437597 < baseStart_437597 := by decide
  rcases family_descends (prefixWord ++ tailWord_437597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437603 : List Nat := [1, 1, 1, 5, 2, 9]
def baseStart_437603 : Nat := 118140960795 + 437603 * 2 ^ 59
def prefixEnd_437603 : Nat := 4983230072969 + 3 ^ 40 * 437603 * 2
def baseEnd_437603 : Nat := 14795106162933768556379

theorem tailTrace_437603 : CollatzResearch.WordTrace tailWord_437603 prefixEnd_437603 14795106162933768556379 := by
  unfold tailWord_437603
  simp only [CollatzResearch.WordTrace]
  refine ⟨15960692633646542487421463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10640461755764361658280975 15960692633646542487421463)
  ·
    refine ⟨23941038950469813731132195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15960692633646542487421463 23941038950469813731132195)
    ·
      refine ⟨35911558425704720596698293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23941038950469813731132195 35911558425704720596698293)
      ·
        refine ⟨3366708602409817555940465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35911558425704720596698293 3366708602409817555940465)
        ·
          refine ⟨2525031451807363166955349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3366708602409817555940465 2525031451807363166955349)
          ·
            refine ⟨14795106162933768556379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2525031451807363166955349 14795106162933768556379)
            ·
              rfl

theorem cell19_437603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 9].length) (baseStart_437603 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437603 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437603 prefixEnd_437603 := by exact prefixLift 437603
  have htrace : WordTrace (prefixWord ++ tailWord_437603) baseStart_437603 baseEnd_437603 := by
    simpa [prefixWord, tailWord_437603, baseEnd_437603] using wordTrace_append hprefix tailTrace_437603
  have hstable : (prefixWord ++ tailWord_437603).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437603).length < 2 ^ (prefixWord ++ tailWord_437603).sum := by decide
  have hdescent : baseEnd_437603 < baseStart_437603 := by decide
  rcases family_descends (prefixWord ++ tailWord_437603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437614 : List Nat := [4, 1, 2, 4, 2, 1, 1, 4]
def baseStart_437614 : Nat := 118140960795 + 437614 * 2 ^ 59
def prefixEnd_437614 : Nat := 4983230072969 + 3 ^ 40 * 437614 * 2
def baseEnd_437614 : Nat := 133159302599559150762937

theorem tailTrace_437614 : CollatzResearch.WordTrace tailWord_437614 prefixEnd_437614 133159302599559150762937 := by
  unfold tailWord_437614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1995136729575836420758987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10640729224404460910714597 1995136729575836420758987)
  ·
    refine ⟨2992705094363754631138481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1995136729575836420758987 2992705094363754631138481)
    ·
      refine ⟨2244528820772815973353861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2992705094363754631138481 2244528820772815973353861)
      ·
        refine ⟨420849153894902995003849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2244528820772815973353861 420849153894902995003849)
        ·
          refine ⟨315636865421177246252887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420849153894902995003849 315636865421177246252887)
          ·
            refine ⟨473455298131765869379331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315636865421177246252887 473455298131765869379331)
            ·
              refine ⟨710182947197648804068997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473455298131765869379331 710182947197648804068997)
              ·
                refine ⟨133159302599559150762937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 710182947197648804068997 133159302599559150762937)
                ·
                  rfl

theorem cell19_437614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_437614 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437614 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437614 prefixEnd_437614 := by exact prefixLift 437614
  have htrace : WordTrace (prefixWord ++ tailWord_437614) baseStart_437614 baseEnd_437614 := by
    simpa [prefixWord, tailWord_437614, baseEnd_437614] using wordTrace_append hprefix tailTrace_437614
  have hstable : (prefixWord ++ tailWord_437614).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437614).length < 2 ^ (prefixWord ++ tailWord_437614).sum := by decide
  have hdescent : baseEnd_437614 < baseStart_437614 := by decide
  rcases family_descends (prefixWord ++ tailWord_437614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437692 : List Nat := [2, 2, 2, 4, 2, 2, 2, 3]
def baseStart_437692 : Nat := 118140960795 + 437692 * 2 ^ 59
def prefixEnd_437692 : Nat := 4983230072969 + 3 ^ 40 * 437692 * 2
def baseEnd_437692 : Nat := 133183036816478081029391

theorem tailTrace_437692 : CollatzResearch.WordTrace tailWord_437692 prefixEnd_437692 133183036816478081029391 := by
  unfold tailWord_437692
  simp only [CollatzResearch.WordTrace]
  refine ⟨7981969365162055343705665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10642625820216073791607553 7981969365162055343705665)
  ·
    refine ⟨5986477023871541507779249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7981969365162055343705665 5986477023871541507779249)
    ·
      refine ⟨4489857767903656130834437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5986477023871541507779249 4489857767903656130834437)
      ·
        refine ⟨841848331481935524531457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4489857767903656130834437 841848331481935524531457)
        ·
          refine ⟨631386248611451643398593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 841848331481935524531457 631386248611451643398593)
          ·
            refine ⟨473539686458588732548945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 631386248611451643398593 473539686458588732548945)
            ·
              refine ⟨355154764843941549411709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473539686458588732548945 355154764843941549411709)
              ·
                refine ⟨133183036816478081029391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355154764843941549411709 133183036816478081029391)
                ·
                  rfl

theorem cell19_437692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_437692 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437692 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437692 prefixEnd_437692 := by exact prefixLift 437692
  have htrace : WordTrace (prefixWord ++ tailWord_437692) baseStart_437692 baseEnd_437692 := by
    simpa [prefixWord, tailWord_437692, baseEnd_437692] using wordTrace_append hprefix tailTrace_437692
  have hstable : (prefixWord ++ tailWord_437692).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437692).length < 2 ^ (prefixWord ++ tailWord_437692).sum := by decide
  have hdescent : baseEnd_437692 < baseStart_437692 := by decide
  rcases family_descends (prefixWord ++ tailWord_437692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437696 : List Nat := [2, 1, 1, 2, 3, 1, 6, 3]
def baseStart_437696 : Nat := 118140960795 + 437696 * 2 ^ 59
def prefixEnd_437696 : Nat := 4983230072969 + 3 ^ 40 * 437696 * 2
def baseEnd_437696 : Nat := 133184253955807256940491

theorem tailTrace_437696 : CollatzResearch.WordTrace tailWord_437696 prefixEnd_437696 133184253955807256940491 := by
  unfold tailWord_437696
  simp only [CollatzResearch.WordTrace]
  refine ⟨7982042311154809685278471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10642723081539746247037961 7982042311154809685278471)
  ·
    refine ⟨11973063466732214527917707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7982042311154809685278471 11973063466732214527917707)
    ·
      refine ⟨17959595200098321791876561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11973063466732214527917707 17959595200098321791876561)
      ·
        refine ⟨13469696400073741343907421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17959595200098321791876561 13469696400073741343907421)
        ·
          refine ⟨5051136150027653003965283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13469696400073741343907421 5051136150027653003965283)
          ·
            refine ⟨7576704225041479505947925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5051136150027653003965283 7576704225041479505947925)
            ·
              refine ⟨355158010548819351841309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7576704225041479505947925 355158010548819351841309)
              ·
                refine ⟨133184253955807256940491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355158010548819351841309 133184253955807256940491)
                ·
                  rfl

theorem cell19_437696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_437696 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437696 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437696 prefixEnd_437696 := by exact prefixLift 437696
  have htrace : WordTrace (prefixWord ++ tailWord_437696) baseStart_437696 baseEnd_437696 := by
    simpa [prefixWord, tailWord_437696, baseEnd_437696] using wordTrace_append hprefix tailTrace_437696
  have hstable : (prefixWord ++ tailWord_437696).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437696).length < 2 ^ (prefixWord ++ tailWord_437696).sum := by decide
  have hdescent : baseEnd_437696 < baseStart_437696 := by decide
  rcases family_descends (prefixWord ++ tailWord_437696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437766 : List Nat := [6, 2, 1, 1, 3, 6]
def baseStart_437766 : Nat := 118140960795 + 437766 * 2 ^ 59
def prefixEnd_437766 : Nat := 4983230072969 + 3 ^ 40 * 437766 * 2
def baseEnd_437766 : Nat := 14800617099340870598305

theorem tailTrace_437766 : CollatzResearch.WordTrace tailWord_437766 prefixEnd_437766 14800617099340870598305 := by
  unfold tailWord_437766
  simp only [CollatzResearch.WordTrace]
  refine ⟨498957429126750666425161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10644425154704014217070101 498957429126750666425161)
  ·
    refine ⟨374218071845062999818871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 498957429126750666425161 374218071845062999818871)
    ·
      refine ⟨561327107767594499728307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374218071845062999818871 561327107767594499728307)
      ·
        refine ⟨841990661651391749592461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561327107767594499728307 841990661651391749592461)
        ·
          refine ⟨315746498119271906097173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 841990661651391749592461 315746498119271906097173)
          ·
            refine ⟨14800617099340870598305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 315746498119271906097173 14800617099340870598305)
            ·
              rfl

theorem cell19_437766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 6].length) (baseStart_437766 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437766 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437766 prefixEnd_437766 := by exact prefixLift 437766
  have htrace : WordTrace (prefixWord ++ tailWord_437766) baseStart_437766 baseEnd_437766 := by
    simpa [prefixWord, tailWord_437766, baseEnd_437766] using wordTrace_append hprefix tailTrace_437766
  have hstable : (prefixWord ++ tailWord_437766).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437766).length < 2 ^ (prefixWord ++ tailWord_437766).sum := by decide
  have hdescent : baseEnd_437766 < baseStart_437766 := by decide
  rcases family_descends (prefixWord ++ tailWord_437766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437772 : List Nat := [2, 2, 1, 2, 6, 6]
def baseStart_437772 : Nat := 118140960795 + 437772 * 2 ^ 59
def prefixEnd_437772 : Nat := 4983230072969 + 3 ^ 40 * 437772 * 2
def baseEnd_437772 : Nat := 14800819955895733250155

theorem tailTrace_437772 : CollatzResearch.WordTrace tailWord_437772 prefixEnd_437772 14800819955895733250155 := by
  unfold tailWord_437772
  simp only [CollatzResearch.WordTrace]
  refine ⟨7983428285017142175161785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10644571046689522900215713 7983428285017142175161785)
  ·
    refine ⟨5987571213762856631371339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7983428285017142175161785 5987571213762856631371339)
    ·
      refine ⟨8981356820644284947057009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5987571213762856631371339 8981356820644284947057009)
      ·
        refine ⟨6736017615483213710292757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8981356820644284947057009 6736017615483213710292757)
        ·
          refine ⟨315750825725775642669973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6736017615483213710292757 315750825725775642669973)
          ·
            refine ⟨14800819955895733250155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 315750825725775642669973 14800819955895733250155)
            ·
              rfl

theorem cell19_437772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 6].length) (baseStart_437772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437772 prefixEnd_437772 := by exact prefixLift 437772
  have htrace : WordTrace (prefixWord ++ tailWord_437772) baseStart_437772 baseEnd_437772 := by
    simpa [prefixWord, tailWord_437772, baseEnd_437772] using wordTrace_append hprefix tailTrace_437772
  have hstable : (prefixWord ++ tailWord_437772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437772).length < 2 ^ (prefixWord ++ tailWord_437772).sum := by decide
  have hdescent : baseEnd_437772 < baseStart_437772 := by decide
  rcases family_descends (prefixWord ++ tailWord_437772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437774 : List Nat := [4, 1, 1, 2, 11]
def baseStart_437774 : Nat := 118140960795 + 437774 * 2 ^ 59
def prefixEnd_437774 : Nat := 4983230072969 + 3 ^ 40 * 437774 * 2
def baseEnd_437774 : Nat := 4933629191582451378035

theorem tailTrace_437774 : CollatzResearch.WordTrace tailWord_437774 prefixEnd_437774 4933629191582451378035 := by
  unfold tailWord_437774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1995866189503379836487047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10644619677351359127930917 1995866189503379836487047)
  ·
    refine ⟨2993799284255069754730571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1995866189503379836487047 2993799284255069754730571)
    ·
      refine ⟨4490698926382604632095857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2993799284255069754730571 4490698926382604632095857)
      ·
        refine ⟨3368024194786953474071893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4490698926382604632095857 3368024194786953474071893)
        ·
          refine ⟨4933629191582451378035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3368024194786953474071893 4933629191582451378035)
          ·
            rfl

theorem cell19_437774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 11].length) (baseStart_437774 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437774 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437774 prefixEnd_437774 := by exact prefixLift 437774
  have htrace : WordTrace (prefixWord ++ tailWord_437774) baseStart_437774 baseEnd_437774 := by
    simpa [prefixWord, tailWord_437774, baseEnd_437774] using wordTrace_append hprefix tailTrace_437774
  have hstable : (prefixWord ++ tailWord_437774).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437774).length < 2 ^ (prefixWord ++ tailWord_437774).sum := by decide
  have hdescent : baseEnd_437774 < baseStart_437774 := by decide
  rcases family_descends (prefixWord ++ tailWord_437774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437954 : List Nat := [3, 5, 1, 2, 2, 1, 1, 4]
def baseStart_437954 : Nat := 118140960795 + 437954 * 2 ^ 59
def prefixEnd_437954 : Nat := 4983230072969 + 3 ^ 40 * 437954 * 2
def baseEnd_437954 : Nat := 133262759442539103206455

theorem tailTrace_437954 : CollatzResearch.WordTrace tailWord_437954 prefixEnd_437954 133262759442539103206455 := by
  unfold tailWord_437954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3993373663843732358362229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10648996436916619622299277 3993373663843732358362229)
  ·
    refine ⟨374378780985349908596459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3993373663843732358362229 374378780985349908596459)
    ·
      refine ⟨561568171478024862894689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 374378780985349908596459 561568171478024862894689)
      ·
        refine ⟨421176128608518647171017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 561568171478024862894689 421176128608518647171017)
        ·
          refine ⟨315882096456388985378263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421176128608518647171017 315882096456388985378263)
          ·
            refine ⟨473823144684583478067395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315882096456388985378263 473823144684583478067395)
            ·
              refine ⟨710734717026875217101093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473823144684583478067395 710734717026875217101093)
              ·
                refine ⟨133262759442539103206455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 710734717026875217101093 133262759442539103206455)
                ·
                  rfl

theorem cell19_437954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_437954 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437954 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437954 prefixEnd_437954 := by exact prefixLift 437954
  have htrace : WordTrace (prefixWord ++ tailWord_437954) baseStart_437954 baseEnd_437954 := by
    simpa [prefixWord, tailWord_437954, baseEnd_437954] using wordTrace_append hprefix tailTrace_437954
  have hstable : (prefixWord ++ tailWord_437954).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437954).length < 2 ^ (prefixWord ++ tailWord_437954).sum := by decide
  have hdescent : baseEnd_437954 < baseStart_437954 := by decide
  rcases family_descends (prefixWord ++ tailWord_437954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_437958 : List Nat := [6, 1, 2, 1, 1, 1, 3, 4]
def baseStart_437958 : Nat := 118140960795 + 437958 * 2 ^ 59
def prefixEnd_437958 : Nat := 4983230072969 + 3 ^ 40 * 437958 * 2
def baseEnd_437958 : Nat := 133263976581868279117555

theorem tailTrace_437958 : CollatzResearch.WordTrace tailWord_437958 prefixEnd_437958 133263976581868279117555 := by
  unfold tailWord_437958
  simp only [CollatzResearch.WordTrace]
  refine ⟨499176267105013691143579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10649093698240292077729685 499176267105013691143579)
  ·
    refine ⟨748764400657520536715369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 499176267105013691143579 748764400657520536715369)
    ·
      refine ⟨561573300493140402536527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 748764400657520536715369 561573300493140402536527)
      ·
        refine ⟨842359950739710603804791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561573300493140402536527 842359950739710603804791)
        ·
          refine ⟨1263539926109565905707187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842359950739710603804791 1263539926109565905707187)
          ·
            refine ⟨1895309889164348858560781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263539926109565905707187 1895309889164348858560781)
            ·
              refine ⟨710741208436630821960293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1895309889164348858560781 710741208436630821960293)
              ·
                refine ⟨133263976581868279117555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 710741208436630821960293 133263976581868279117555)
                ·
                  rfl

theorem cell19_437958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_437958 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_437958 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_437958 prefixEnd_437958 := by exact prefixLift 437958
  have htrace : WordTrace (prefixWord ++ tailWord_437958) baseStart_437958 baseEnd_437958 := by
    simpa [prefixWord, tailWord_437958, baseEnd_437958] using wordTrace_append hprefix tailTrace_437958
  have hstable : (prefixWord ++ tailWord_437958).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_437958).length < 2 ^ (prefixWord ++ tailWord_437958).sum := by decide
  have hdescent : baseEnd_437958 < baseStart_437958 := by decide
  rcases family_descends (prefixWord ++ tailWord_437958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438002 : List Nat := [3, 2, 1, 3, 1, 1, 8]
def baseStart_438002 : Nat := 118140960795 + 438002 * 2 ^ 59
def prefixEnd_438002 : Nat := 4983230072969 + 3 ^ 40 * 438002 * 2
def baseEnd_438002 : Nat := 44425788371496404713219

theorem tailTrace_438002 : CollatzResearch.WordTrace tailWord_438002 prefixEnd_438002 44425788371496404713219 := by
  unfold tailWord_438002
  simp only [CollatzResearch.WordTrace]
  refine ⟨3993811339800258407799065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10650163572800689087464173 3993811339800258407799065)
  ·
    refine ⟨2995358504850193805849299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3993811339800258407799065 2995358504850193805849299)
    ·
      refine ⟨4493037757275290708773949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2995358504850193805849299 4493037757275290708773949)
      ·
        refine ⟨1684889158978234015790231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4493037757275290708773949 1684889158978234015790231)
        ·
          refine ⟨2527333738467351023685347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1684889158978234015790231 2527333738467351023685347)
          ·
            refine ⟨3791000607701026535528021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2527333738467351023685347 3791000607701026535528021)
            ·
              refine ⟨44425788371496404713219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3791000607701026535528021 44425788371496404713219)
              ·
                rfl

theorem cell19_438002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 8].length) (baseStart_438002 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438002 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438002 prefixEnd_438002 := by exact prefixLift 438002
  have htrace : WordTrace (prefixWord ++ tailWord_438002) baseStart_438002 baseEnd_438002 := by
    simpa [prefixWord, tailWord_438002, baseEnd_438002] using wordTrace_append hprefix tailTrace_438002
  have hstable : (prefixWord ++ tailWord_438002).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438002).length < 2 ^ (prefixWord ++ tailWord_438002).sum := by decide
  have hdescent : baseEnd_438002 < baseStart_438002 := by decide
  rcases family_descends (prefixWord ++ tailWord_438002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438034 : List Nat := [3, 2, 4, 1, 1, 3, 2, 3]
def baseStart_438034 : Nat := 118140960795 + 438034 * 2 ^ 59
def prefixEnd_438034 : Nat := 4983230072969 + 3 ^ 40 * 438034 * 2
def baseEnd_438034 : Nat := 133287102229122621428459

theorem tailTrace_438034 : CollatzResearch.WordTrace tailWord_438034 prefixEnd_438034 133287102229122621428459 := by
  unfold tailWord_438034
  simp only [CollatzResearch.WordTrace]
  refine ⟨3994103123771275774090289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10650941663390068730907437 3994103123771275774090289)
  ·
    refine ⟨2995577342828456830567717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3994103123771275774090289 2995577342828456830567717)
    ·
      refine ⟨561670751780335655731447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2995577342828456830567717 561670751780335655731447)
      ·
        refine ⟨842506127670503483597171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 561670751780335655731447 842506127670503483597171)
        ·
          refine ⟨1263759191505755225395757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 842506127670503483597171 1263759191505755225395757)
          ·
            refine ⟨473909696814658209523409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1263759191505755225395757 473909696814658209523409)
            ·
              refine ⟨355432272610993657142557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473909696814658209523409 355432272610993657142557)
              ·
                refine ⟨133287102229122621428459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355432272610993657142557 133287102229122621428459)
                ·
                  rfl

theorem cell19_438034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_438034 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438034 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438034 prefixEnd_438034 := by exact prefixLift 438034
  have htrace : WordTrace (prefixWord ++ tailWord_438034) baseStart_438034 baseEnd_438034 := by
    simpa [prefixWord, tailWord_438034, baseEnd_438034] using wordTrace_append hprefix tailTrace_438034
  have hstable : (prefixWord ++ tailWord_438034).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438034).length < 2 ^ (prefixWord ++ tailWord_438034).sum := by decide
  have hdescent : baseEnd_438034 < baseStart_438034 := by decide
  rcases family_descends (prefixWord ++ tailWord_438034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438097 : List Nat := [1, 2, 2, 1, 5, 1, 2, 5]
def baseStart_438097 : Nat := 118140960795 + 438097 * 2 ^ 59
def prefixEnd_438097 : Nat := 4983230072969 + 3 ^ 40 * 438097 * 2
def baseEnd_438097 : Nat := 133306272173557142028287

theorem tailTrace_438097 : CollatzResearch.WordTrace tailWord_438097 prefixEnd_438097 133306272173557142028287 := by
  unfold tailWord_438097
  simp only [CollatzResearch.WordTrace]
  refine ⟨15978710293856864855904545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10652473529237909903936363 15978710293856864855904545)
  ·
    refine ⟨11984032720392648641928409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15978710293856864855904545 11984032720392648641928409)
    ·
      refine ⟨8988024540294486481446307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11984032720392648641928409 8988024540294486481446307)
      ·
        refine ⟨13482036810441729722169461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8988024540294486481446307 13482036810441729722169461)
        ·
          refine ⟨1263940950978912161453387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13482036810441729722169461 1263940950978912161453387)
          ·
            refine ⟨1895911426468368242180081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263940950978912161453387 1895911426468368242180081)
            ·
              refine ⟨1421933569851276181635061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1895911426468368242180081 1421933569851276181635061)
              ·
                refine ⟨133306272173557142028287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1421933569851276181635061 133306272173557142028287)
                ·
                  rfl

theorem cell19_438097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_438097 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438097 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438097 prefixEnd_438097 := by exact prefixLift 438097
  have htrace : WordTrace (prefixWord ++ tailWord_438097) baseStart_438097 baseEnd_438097 := by
    simpa [prefixWord, tailWord_438097, baseEnd_438097] using wordTrace_append hprefix tailTrace_438097
  have hstable : (prefixWord ++ tailWord_438097).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438097).length < 2 ^ (prefixWord ++ tailWord_438097).sum := by decide
  have hdescent : baseEnd_438097 < baseStart_438097 := by decide
  rcases family_descends (prefixWord ++ tailWord_438097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438116 : List Nat := [2, 3, 1, 1, 5, 7]
def baseStart_438116 : Nat := 118140960795 + 438116 * 2 ^ 59
def prefixEnd_438116 : Nat := 4983230072969 + 3 ^ 40 * 438116 * 2
def baseEnd_438116 : Nat := 14812450398374525289557

theorem tailTrace_438116 : CollatzResearch.WordTrace tailWord_438116 prefixEnd_438116 14812450398374525289557 := by
  unfold tailWord_438116
  simp only [CollatzResearch.WordTrace]
  refine ⟨7989701640394015550423101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10652935520525354067230801 7989701640394015550423101)
  ·
    refine ⟨2996138115147755831408663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7989701640394015550423101 2996138115147755831408663)
    ·
      refine ⟨4494207172721633747112995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2996138115147755831408663 4494207172721633747112995)
      ·
        refine ⟨6741310759082450620669493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4494207172721633747112995 6741310759082450620669493)
        ·
          refine ⟨631997883663979745687765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6741310759082450620669493 631997883663979745687765)
          ·
            refine ⟨14812450398374525289557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 631997883663979745687765 14812450398374525289557)
            ·
              rfl

theorem cell19_438116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 7].length) (baseStart_438116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438116 prefixEnd_438116 := by exact prefixLift 438116
  have htrace : WordTrace (prefixWord ++ tailWord_438116) baseStart_438116 baseEnd_438116 := by
    simpa [prefixWord, tailWord_438116, baseEnd_438116] using wordTrace_append hprefix tailTrace_438116
  have hstable : (prefixWord ++ tailWord_438116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438116).length < 2 ^ (prefixWord ++ tailWord_438116).sum := by decide
  have hdescent : baseEnd_438116 < baseStart_438116 := by decide
  rcases family_descends (prefixWord ++ tailWord_438116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438173 : List Nat := [1, 4, 2, 1, 2, 3, 6]
def baseStart_438173 : Nat := 118140960795 + 438173 * 2 ^ 59
def prefixEnd_438173 : Nat := 4983230072969 + 3 ^ 40 * 438173 * 2
def baseEnd_438173 : Nat := 44443132606937161446397

theorem tailTrace_438173 : CollatzResearch.WordTrace tailWord_438173 prefixEnd_438173 44443132606937161446397 := by
  unfold tailWord_438173
  simp only [CollatzResearch.WordTrace]
  refine ⟨15981482241581529835671173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10654321494387686557114115 15981482241581529835671173)
  ·
    refine ⟨2996527920296536844188345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15981482241581529835671173 2996527920296536844188345)
    ·
      refine ⟨2247395940222402633141259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2996527920296536844188345 2247395940222402633141259)
      ·
        refine ⟨3371093910333603949711889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2247395940222402633141259 3371093910333603949711889)
        ·
          refine ⟨2528320432750202962283917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3371093910333603949711889 2528320432750202962283917)
          ·
            refine ⟨948120162281326110856469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2528320432750202962283917 948120162281326110856469)
            ·
              refine ⟨44443132606937161446397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 948120162281326110856469 44443132606937161446397)
              ·
                rfl

theorem cell19_438173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 6].length) (baseStart_438173 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438173 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438173 prefixEnd_438173 := by exact prefixLift 438173
  have htrace : WordTrace (prefixWord ++ tailWord_438173) baseStart_438173 baseEnd_438173 := by
    simpa [prefixWord, tailWord_438173, baseEnd_438173] using wordTrace_append hprefix tailTrace_438173
  have hstable : (prefixWord ++ tailWord_438173).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438173).length < 2 ^ (prefixWord ++ tailWord_438173).sum := by decide
  have hdescent : baseEnd_438173 < baseStart_438173 := by decide
  rcases family_descends (prefixWord ++ tailWord_438173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438226 : List Nat := [3, 2, 2, 3, 3, 1, 5]
def baseStart_438226 : Nat := 118140960795 + 438226 * 2 ^ 59
def prefixEnd_438226 : Nat := 4983230072969 + 3 ^ 40 * 438226 * 2
def baseEnd_438226 : Nat := 44448508305641021720423

theorem tailTrace_438226 : CollatzResearch.WordTrace tailWord_438226 prefixEnd_438226 44448508305641021720423 := by
  unfold tailWord_438226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3995853827597379971837633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10655610206926346591567021 3995853827597379971837633)
  ·
    refine ⟨2996890370698034978878225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3995853827597379971837633 2996890370698034978878225)
    ·
      refine ⟨2247667778023526234158669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2996890370698034978878225 2247667778023526234158669)
      ·
        refine ⟨842875416758822337809501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2247667778023526234158669 842875416758822337809501)
        ·
          refine ⟨316078281284558376678563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 842875416758822337809501 316078281284558376678563)
          ·
            refine ⟨474117421926837565017845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316078281284558376678563 474117421926837565017845)
            ·
              refine ⟨44448508305641021720423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 474117421926837565017845 44448508305641021720423)
              ·
                rfl

theorem cell19_438226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 5].length) (baseStart_438226 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438226 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438226 prefixEnd_438226 := by exact prefixLift 438226
  have htrace : WordTrace (prefixWord ++ tailWord_438226) baseStart_438226 baseEnd_438226 := by
    simpa [prefixWord, tailWord_438226, baseEnd_438226] using wordTrace_append hprefix tailTrace_438226
  have hstable : (prefixWord ++ tailWord_438226).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438226).length < 2 ^ (prefixWord ++ tailWord_438226).sum := by decide
  have hdescent : baseEnd_438226 < baseStart_438226 := by decide
  rcases family_descends (prefixWord ++ tailWord_438226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438247 : List Nat := [1, 1, 5, 2, 3, 1, 2, 4]
def baseStart_438247 : Nat := 118140960795 + 438247 * 2 ^ 59
def prefixEnd_438247 : Nat := 4983230072969 + 3 ^ 40 * 438247 * 2
def baseEnd_438247 : Nat := 133351914898401238694545

theorem tailTrace_438247 : CollatzResearch.WordTrace tailWord_438247 prefixEnd_438247 133351914898401238694545 := by
  unfold tailWord_438247
  simp only [CollatzResearch.WordTrace]
  refine ⟨15984181243313440473864995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10656120828875626982576663 15984181243313440473864995)
  ·
    refine ⟨23976271864970160710797493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15984181243313440473864995 23976271864970160710797493)
    ·
      refine ⟨2247775487340952566637265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23976271864970160710797493 2247775487340952566637265)
      ·
        refine ⟨1685831615505714424977949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2247775487340952566637265 1685831615505714424977949)
        ·
          refine ⟨632186855814642909366731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1685831615505714424977949 632186855814642909366731)
          ·
            refine ⟨948280283721964364050097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632186855814642909366731 948280283721964364050097)
            ·
              refine ⟨711210212791473273037573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 948280283721964364050097 711210212791473273037573)
              ·
                refine ⟨133351914898401238694545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 711210212791473273037573 133351914898401238694545)
                ·
                  rfl

theorem cell19_438247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 4].length) (baseStart_438247 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438247 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438247 prefixEnd_438247 := by exact prefixLift 438247
  have htrace : WordTrace (prefixWord ++ tailWord_438247) baseStart_438247 baseEnd_438247 := by
    simpa [prefixWord, tailWord_438247, baseEnd_438247] using wordTrace_append hprefix tailTrace_438247
  have hstable : (prefixWord ++ tailWord_438247).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438247).length < 2 ^ (prefixWord ++ tailWord_438247).sum := by decide
  have hdescent : baseEnd_438247 < baseStart_438247 := by decide
  rcases family_descends (prefixWord ++ tailWord_438247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438327 : List Nat := [1, 1, 3, 1, 2, 2, 2, 7]
def baseStart_438327 : Nat := 118140960795 + 438327 * 2 ^ 59
def prefixEnd_438327 : Nat := 4983230072969 + 3 ^ 40 * 438327 * 2
def baseEnd_438327 : Nat := 133376257684984756916549

theorem tailTrace_438327 : CollatzResearch.WordTrace tailWord_438327 prefixEnd_438327 133376257684984756916549 := by
  unfold tailWord_438327
  simp only [CollatzResearch.WordTrace]
  refine ⟨15987099083023614136777235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10658066055349076091184823 15987099083023614136777235)
  ·
    refine ⟨23980648624535421205165853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15987099083023614136777235 23980648624535421205165853)
    ·
      refine ⟨8992743234200782951937195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23980648624535421205165853 8992743234200782951937195)
      ·
        refine ⟨13489114851301174427905793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8992743234200782951937195 13489114851301174427905793)
        ·
          refine ⟨10116836138475880820929345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13489114851301174427905793 10116836138475880820929345)
          ·
            refine ⟨7587627103856910615697009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10116836138475880820929345 7587627103856910615697009)
            ·
              refine ⟨5690720327892682961772757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7587627103856910615697009 5690720327892682961772757)
              ·
                refine ⟨133376257684984756916549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5690720327892682961772757 133376257684984756916549)
                ·
                  rfl

theorem cell19_438327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_438327 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438327 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438327 prefixEnd_438327 := by exact prefixLift 438327
  have htrace : WordTrace (prefixWord ++ tailWord_438327) baseStart_438327 baseEnd_438327 := by
    simpa [prefixWord, tailWord_438327, baseEnd_438327] using wordTrace_append hprefix tailTrace_438327
  have hstable : (prefixWord ++ tailWord_438327).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438327).length < 2 ^ (prefixWord ++ tailWord_438327).sum := by decide
  have hdescent : baseEnd_438327 < baseStart_438327 := by decide
  rcases family_descends (prefixWord ++ tailWord_438327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438342 : List Nat := [6, 1, 1, 1, 1, 1, 8]
def baseStart_438342 : Nat := 118140960795 + 438342 * 2 ^ 59
def prefixEnd_438342 : Nat := 4983230072969 + 3 ^ 40 * 438342 * 2
def baseEnd_438342 : Nat := 44460273985823055527725

theorem tailTrace_438342 : CollatzResearch.WordTrace tailWord_438342 prefixEnd_438342 44460273985823055527725 := by
  unfold tailWord_438342
  simp only [CollatzResearch.WordTrace]
  refine ⟨499613943061539740580415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10658430785312847799048853 499613943061539740580415)
  ·
    refine ⟨749420914592309610870623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 499613943061539740580415 749420914592309610870623)
    ·
      refine ⟨1124131371888464416305935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 749420914592309610870623 1124131371888464416305935)
      ·
        refine ⟨1686197057832696624458903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1124131371888464416305935 1686197057832696624458903)
        ·
          refine ⟨2529295586749044936688355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1686197057832696624458903 2529295586749044936688355)
          ·
            refine ⟨3793943380123567405032533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2529295586749044936688355 3793943380123567405032533)
            ·
              refine ⟨44460273985823055527725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3793943380123567405032533 44460273985823055527725)
              ·
                rfl

theorem cell19_438342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 8].length) (baseStart_438342 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438342 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438342 prefixEnd_438342 := by exact prefixLift 438342
  have htrace : WordTrace (prefixWord ++ tailWord_438342) baseStart_438342 baseEnd_438342 := by
    simpa [prefixWord, tailWord_438342, baseEnd_438342] using wordTrace_append hprefix tailTrace_438342
  have hstable : (prefixWord ++ tailWord_438342).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438342).length < 2 ^ (prefixWord ++ tailWord_438342).sum := by decide
  have hdescent : baseEnd_438342 < baseStart_438342 := by decide
  rcases family_descends (prefixWord ++ tailWord_438342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438378 : List Nat := [3, 1, 3, 2, 3, 2, 2, 3]
def baseStart_438378 : Nat := 118140960795 + 438378 * 2 ^ 59
def prefixEnd_438378 : Nat := 4983230072969 + 3 ^ 40 * 438378 * 2
def baseEnd_438378 : Nat := 133391776211431749783077

theorem tailTrace_438378 : CollatzResearch.WordTrace tailWord_438378 prefixEnd_438378 133391776211431749783077 := by
  unfold tailWord_438378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3997239801459712461720947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10659306137225899897922525 3997239801459712461720947)
  ·
    refine ⟨5995859702189568692581421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3997239801459712461720947 5995859702189568692581421)
    ·
      refine ⟨2248447388321088259718033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5995859702189568692581421 2248447388321088259718033)
      ·
        refine ⟨1686335541240816194788525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2248447388321088259718033 1686335541240816194788525)
        ·
          refine ⟨632375827965306073045697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1686335541240816194788525 632375827965306073045697)
          ·
            refine ⟨474281870973979554784273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 632375827965306073045697 474281870973979554784273)
            ·
              refine ⟨355711403230484666088205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474281870973979554784273 355711403230484666088205)
              ·
                refine ⟨133391776211431749783077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355711403230484666088205 133391776211431749783077)
                ·
                  rfl

theorem cell19_438378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_438378 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438378 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438378 prefixEnd_438378 := by exact prefixLift 438378
  have htrace : WordTrace (prefixWord ++ tailWord_438378) baseStart_438378 baseEnd_438378 := by
    simpa [prefixWord, tailWord_438378, baseEnd_438378] using wordTrace_append hprefix tailTrace_438378
  have hstable : (prefixWord ++ tailWord_438378).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438378).length < 2 ^ (prefixWord ++ tailWord_438378).sum := by decide
  have hdescent : baseEnd_438378 < baseStart_438378 := by decide
  rcases family_descends (prefixWord ++ tailWord_438378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438380 : List Nat := [2, 2, 1, 1, 3, 5, 2, 3]
def baseStart_438380 : Nat := 118140960795 + 438380 * 2 ^ 59
def prefixEnd_438380 : Nat := 4983230072969 + 3 ^ 40 * 438380 * 2
def baseEnd_438380 : Nat := 133392384781096337738627

theorem tailTrace_438380 : CollatzResearch.WordTrace tailWord_438380 prefixEnd_438380 133392384781096337738627 := by
  unfold tailWord_438380
  simp only [CollatzResearch.WordTrace]
  refine ⟨7994516075915802094228297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10659354767887736125637729 7994516075915802094228297)
  ·
    refine ⟨5995887056936851570671223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7994516075915802094228297 5995887056936851570671223)
    ·
      refine ⟨8993830585405277356006835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5995887056936851570671223 8993830585405277356006835)
      ·
        refine ⟨13490745878107916034010253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8993830585405277356006835 13490745878107916034010253)
        ·
          refine ⟨5059029704290468512753845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13490745878107916034010253 5059029704290468512753845)
          ·
            refine ⟨474284034777231423070673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5059029704290468512753845 474284034777231423070673)
            ·
              refine ⟨355713026082923567303005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474284034777231423070673 355713026082923567303005)
              ·
                refine ⟨133392384781096337738627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355713026082923567303005 133392384781096337738627)
                ·
                  rfl

theorem cell19_438380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_438380 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438380 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438380 prefixEnd_438380 := by exact prefixLift 438380
  have htrace : WordTrace (prefixWord ++ tailWord_438380) baseStart_438380 baseEnd_438380 := by
    simpa [prefixWord, tailWord_438380, baseEnd_438380] using wordTrace_append hprefix tailTrace_438380
  have hstable : (prefixWord ++ tailWord_438380).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438380).length < 2 ^ (prefixWord ++ tailWord_438380).sum := by decide
  have hdescent : baseEnd_438380 < baseStart_438380 := by decide
  rcases family_descends (prefixWord ++ tailWord_438380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438382 : List Nat := [4, 1, 2, 2, 1, 1, 3, 5]
def baseStart_438382 : Nat := 118140960795 + 438382 * 2 ^ 59
def prefixEnd_438382 : Nat := 4983230072969 + 3 ^ 40 * 438382 * 2
def baseEnd_438382 : Nat := 133392993350760925694177

theorem tailTrace_438382 : CollatzResearch.WordTrace tailWord_438382 prefixEnd_438382 133392993350760925694177 := by
  unfold tailWord_438382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1998638137228044816253675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10659403398549572353352933 1998638137228044816253675)
  ·
    refine ⟨2997957205842067224380513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1998638137228044816253675 2997957205842067224380513)
    ·
      refine ⟨2248467904381550418285385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2997957205842067224380513 2248467904381550418285385)
      ·
        refine ⟨1686350928286162813714039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2248467904381550418285385 1686350928286162813714039)
        ·
          refine ⟨2529526392429244220571059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1686350928286162813714039 2529526392429244220571059)
          ·
            refine ⟨3794289588643866330856589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2529526392429244220571059 3794289588643866330856589)
            ·
              refine ⟨1422858595741449874071221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3794289588643866330856589 1422858595741449874071221)
              ·
                refine ⟨133392993350760925694177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1422858595741449874071221 133392993350760925694177)
                ·
                  rfl

theorem cell19_438382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_438382 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438382 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438382 prefixEnd_438382 := by exact prefixLift 438382
  have htrace : WordTrace (prefixWord ++ tailWord_438382) baseStart_438382 baseEnd_438382 := by
    simpa [prefixWord, tailWord_438382, baseEnd_438382] using wordTrace_append hprefix tailTrace_438382
  have hstable : (prefixWord ++ tailWord_438382).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438382).length < 2 ^ (prefixWord ++ tailWord_438382).sum := by decide
  have hdescent : baseEnd_438382 < baseStart_438382 := by decide
  rcases family_descends (prefixWord ++ tailWord_438382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438403 : List Nat := [1, 1, 1, 3, 3, 3, 7]
def baseStart_438403 : Nat := 118140960795 + 438403 * 2 ^ 59
def prefixEnd_438403 : Nat := 4983230072969 + 3 ^ 40 * 438403 * 2
def baseEnd_438403 : Nat := 44466461110746366409151

theorem tailTrace_438403 : CollatzResearch.WordTrace tailWord_438403 prefixEnd_438403 44466461110746366409151 := by
  unfold tailWord_438403
  simp only [CollatzResearch.WordTrace]
  refine ⟨15989871030748279116543863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10659914020498852744362575 15989871030748279116543863)
  ·
    refine ⟨23984806546122418674815795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15989871030748279116543863 23984806546122418674815795)
    ·
      refine ⟨35977209819183628012223693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23984806546122418674815795 35977209819183628012223693)
      ·
        refine ⟨13491453682193860504583885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35977209819183628012223693 13491453682193860504583885)
        ·
          refine ⟨5059295130822697689218957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13491453682193860504583885 5059295130822697689218957)
          ·
            refine ⟨1897235674058511633457109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5059295130822697689218957 1897235674058511633457109)
            ·
              refine ⟨44466461110746366409151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1897235674058511633457109 44466461110746366409151)
              ·
                rfl

theorem cell19_438403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 7].length) (baseStart_438403 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438403 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438403 prefixEnd_438403 := by exact prefixLift 438403
  have htrace : WordTrace (prefixWord ++ tailWord_438403) baseStart_438403 baseEnd_438403 := by
    simpa [prefixWord, tailWord_438403, baseEnd_438403] using wordTrace_append hprefix tailTrace_438403
  have hstable : (prefixWord ++ tailWord_438403).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438403).length < 2 ^ (prefixWord ++ tailWord_438403).sum := by decide
  have hdescent : baseEnd_438403 < baseStart_438403 := by decide
  rcases family_descends (prefixWord ++ tailWord_438403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438452 : List Nat := [2, 5, 3, 1, 2, 6]
def baseStart_438452 : Nat := 118140960795 + 438452 * 2 ^ 59
def prefixEnd_438452 : Nat := 4983230072969 + 3 ^ 40 * 438452 * 2
def baseEnd_438452 : Nat := 14823810365446833793159

theorem tailTrace_438452 : CollatzResearch.WordTrace tailWord_438452 prefixEnd_438452 14823810365446833793159 := by
  unfold tailWord_438452
  simp only [CollatzResearch.WordTrace]
  refine ⟨7995829103785380242538805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10661105471713840323385073 7995829103785380242538805)
  ·
    refine ⟨749608978479879397738013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7995829103785380242538805 749608978479879397738013)
    ·
      refine ⟨281103366929954774151755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 749608978479879397738013 281103366929954774151755)
      ·
        refine ⟨421655050394932161227633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281103366929954774151755 421655050394932161227633)
        ·
          refine ⟨316241287796199120920725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421655050394932161227633 316241287796199120920725)
          ·
            refine ⟨14823810365446833793159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 316241287796199120920725 14823810365446833793159)
            ·
              rfl

theorem cell19_438452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 6].length) (baseStart_438452 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438452 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438452 prefixEnd_438452 := by exact prefixLift 438452
  have htrace : WordTrace (prefixWord ++ tailWord_438452) baseStart_438452 baseEnd_438452 := by
    simpa [prefixWord, tailWord_438452, baseEnd_438452] using wordTrace_append hprefix tailTrace_438452
  have hstable : (prefixWord ++ tailWord_438452).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438452).length < 2 ^ (prefixWord ++ tailWord_438452).sum := by decide
  have hdescent : baseEnd_438452 < baseStart_438452 := by decide
  rcases family_descends (prefixWord ++ tailWord_438452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438460 : List Nat := [2, 2, 2, 3, 10]
def baseStart_438460 : Nat := 118140960795 + 438460 * 2 ^ 59
def prefixEnd_438460 : Nat := 4983230072969 + 3 ^ 40 * 438460 * 2
def baseEnd_438460 : Nat := 4941360280284439109653

theorem tailTrace_438460 : CollatzResearch.WordTrace tailWord_438460 prefixEnd_438460 4941360280284439109653 := by
  unfold tailWord_438460
  simp only [CollatzResearch.WordTrace]
  refine ⟨7995974995770888925684417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10661299994361185234245889 7995974995770888925684417)
  ·
    refine ⟨5996981246828166694263313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7995974995770888925684417 5996981246828166694263313)
    ·
      refine ⟨4497735935121125020697485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5996981246828166694263313 4497735935121125020697485)
      ·
        refine ⟨1686650975670421882761557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4497735935121125020697485 1686650975670421882761557)
        ·
          refine ⟨4941360280284439109653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1686650975670421882761557 4941360280284439109653)
          ·
            rfl

theorem cell19_438460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 10].length) (baseStart_438460 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438460 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438460 prefixEnd_438460 := by exact prefixLift 438460
  have htrace : WordTrace (prefixWord ++ tailWord_438460) baseStart_438460 baseEnd_438460 := by
    simpa [prefixWord, tailWord_438460, baseEnd_438460] using wordTrace_append hprefix tailTrace_438460
  have hstable : (prefixWord ++ tailWord_438460).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438460).length < 2 ^ (prefixWord ++ tailWord_438460).sum := by decide
  have hdescent : baseEnd_438460 < baseStart_438460 := by decide
  rcases family_descends (prefixWord ++ tailWord_438460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438496 : List Nat := [2, 1, 1, 3, 1, 3, 5, 3]
def baseStart_438496 : Nat := 118140960795 + 438496 * 2 ^ 59
def prefixEnd_438496 : Nat := 4983230072969 + 3 ^ 40 * 438496 * 2
def baseEnd_438496 : Nat := 133427681821642439160533

theorem tailTrace_438496 : CollatzResearch.WordTrace tailWord_438496 prefixEnd_438496 133427681821642439160533 := by
  unfold tailWord_438496
  simp only [CollatzResearch.WordTrace]
  refine ⟨7996631509705677999839671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10662175346274237333119561 7996631509705677999839671)
  ·
    refine ⟨11994947264558516999759507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7996631509705677999839671 11994947264558516999759507)
    ·
      refine ⟨17992420896837775499639261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11994947264558516999759507 17992420896837775499639261)
      ·
        refine ⟨6747157836314165812364723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17992420896837775499639261 6747157836314165812364723)
        ·
          refine ⟨10120736754471248718547085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6747157836314165812364723 10120736754471248718547085)
          ·
            refine ⟨3795276282926718269455157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10120736754471248718547085 3795276282926718269455157)
            ·
              refine ⟨355807151524379837761421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3795276282926718269455157 355807151524379837761421)
              ·
                refine ⟨133427681821642439160533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355807151524379837761421 133427681821642439160533)
                ·
                  rfl

theorem cell19_438496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_438496 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438496 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438496 prefixEnd_438496 := by exact prefixLift 438496
  have htrace : WordTrace (prefixWord ++ tailWord_438496) baseStart_438496 baseEnd_438496 := by
    simpa [prefixWord, tailWord_438496, baseEnd_438496] using wordTrace_append hprefix tailTrace_438496
  have hstable : (prefixWord ++ tailWord_438496).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438496).length < 2 ^ (prefixWord ++ tailWord_438496).sum := by decide
  have hdescent : baseEnd_438496 < baseStart_438496 := by decide
  rcases family_descends (prefixWord ++ tailWord_438496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438551 : List Nat := [1, 1, 3, 4, 1, 4, 2, 3]
def baseStart_438551 : Nat := 118140960795 + 438551 * 2 ^ 59
def prefixEnd_438551 : Nat := 4983230072969 + 3 ^ 40 * 438551 * 2
def baseEnd_438551 : Nat := 133444417487418607938161

theorem tailTrace_438551 : CollatzResearch.WordTrace tailWord_438551 prefixEnd_438551 133444417487418607938161 := by
  unfold tailWord_438551
  simp only [CollatzResearch.WordTrace]
  refine ⟨15995269034212100392931507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10663512689474733595287671 15995269034212100392931507)
  ·
    refine ⟨23992903551318150589397261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15995269034212100392931507 23992903551318150589397261)
    ·
      refine ⟨8997338831744306471023973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23992903551318150589397261 8997338831744306471023973)
      ·
        refine ⟨1687001030952057463316995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8997338831744306471023973 1687001030952057463316995)
        ·
          refine ⟨2530501546428086194975493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1687001030952057463316995 2530501546428086194975493)
          ·
            refine ⟨474469039955266161557905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2530501546428086194975493 474469039955266161557905)
            ·
              refine ⟨355851779966449621168429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474469039955266161557905 355851779966449621168429)
              ·
                refine ⟨133444417487418607938161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355851779966449621168429 133444417487418607938161)
                ·
                  rfl

theorem cell19_438551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 3].length) (baseStart_438551 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438551 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438551 prefixEnd_438551 := by exact prefixLift 438551
  have htrace : WordTrace (prefixWord ++ tailWord_438551) baseStart_438551 baseEnd_438551 := by
    simpa [prefixWord, tailWord_438551, baseEnd_438551] using wordTrace_append hprefix tailTrace_438551
  have hstable : (prefixWord ++ tailWord_438551).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438551).length < 2 ^ (prefixWord ++ tailWord_438551).sum := by decide
  have hdescent : baseEnd_438551 < baseStart_438551 := by decide
  rcases family_descends (prefixWord ++ tailWord_438551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438570 : List Nat := [3, 1, 4, 2, 2, 2, 5]
def baseStart_438570 : Nat := 118140960795 + 438570 * 2 ^ 59
def prefixEnd_438570 : Nat := 4983230072969 + 3 ^ 40 * 438570 * 2
def baseEnd_438570 : Nat := 44483399633077397838629

theorem tailTrace_438570 : CollatzResearch.WordTrace tailWord_438570 prefixEnd_438570 44483399633077397838629 := by
  unfold tailWord_438570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3998990505285816659468291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10663974680762177758582109 3998990505285816659468291)
  ·
    refine ⟨5998485757928724989202437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3998990505285816659468291 5998485757928724989202437)
    ·
      refine ⟨1124716079611635935475457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5998485757928724989202437 1124716079611635935475457)
      ·
        refine ⟨843537059708726951606593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1124716079611635935475457 843537059708726951606593)
        ·
          refine ⟨632652794781545213704945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843537059708726951606593 632652794781545213704945)
          ·
            refine ⟨474489596086158910278709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 632652794781545213704945 474489596086158910278709)
            ·
              refine ⟨44483399633077397838629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 474489596086158910278709 44483399633077397838629)
              ·
                rfl

theorem cell19_438570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 5].length) (baseStart_438570 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438570 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438570 prefixEnd_438570 := by exact prefixLift 438570
  have htrace : WordTrace (prefixWord ++ tailWord_438570) baseStart_438570 baseEnd_438570 := by
    simpa [prefixWord, tailWord_438570, baseEnd_438570] using wordTrace_append hprefix tailTrace_438570
  have hstable : (prefixWord ++ tailWord_438570).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438570).length < 2 ^ (prefixWord ++ tailWord_438570).sum := by decide
  have hdescent : baseEnd_438570 < baseStart_438570 := by decide
  rcases family_descends (prefixWord ++ tailWord_438570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438631 : List Nat := [1, 1, 5, 1, 3, 8]
def baseStart_438631 : Nat := 118140960795 + 438631 * 2 ^ 59
def prefixEnd_438631 : Nat := 4983230072969 + 3 ^ 40 * 438631 * 2
def baseEnd_438631 : Nat := 14829862252666902906685

theorem tailTrace_438631 : CollatzResearch.WordTrace tailWord_438631 prefixEnd_438631 14829862252666902906685 := by
  unfold tailWord_438631
  simp only [CollatzResearch.WordTrace]
  refine ⟨15998186873922274055843747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10665457915948182703895831 15998186873922274055843747)
  ·
    refine ⟨23997280310883411083765621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15998186873922274055843747 23997280310883411083765621)
    ·
      refine ⟨2249745029145319789103027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23997280310883411083765621 2249745029145319789103027)
      ·
        refine ⟨3374617543717979683654541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2249745029145319789103027 3374617543717979683654541)
        ·
          refine ⟨1265481578894242381370453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3374617543717979683654541 1265481578894242381370453)
          ·
            refine ⟨14829862252666902906685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1265481578894242381370453 14829862252666902906685)
            ·
              rfl

theorem cell19_438631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 8].length) (baseStart_438631 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438631 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438631 prefixEnd_438631 := by exact prefixLift 438631
  have htrace : WordTrace (prefixWord ++ tailWord_438631) baseStart_438631 baseEnd_438631 := by
    simpa [prefixWord, tailWord_438631, baseEnd_438631] using wordTrace_append hprefix tailTrace_438631
  have hstable : (prefixWord ++ tailWord_438631).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438631).length < 2 ^ (prefixWord ++ tailWord_438631).sum := by decide
  have hdescent : baseEnd_438631 < baseStart_438631 := by decide
  rcases family_descends (prefixWord ++ tailWord_438631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438667 : List Nat := [1, 1, 1, 1, 4, 5, 3, 3]
def baseStart_438667 : Nat := 118140960795 + 438667 * 2 ^ 59
def prefixEnd_438667 : Nat := 4983230072969 + 3 ^ 40 * 438667 * 2
def baseEnd_438667 : Nat := 133479714527964709360067

theorem tailTrace_438667 : CollatzResearch.WordTrace tailWord_438667 prefixEnd_438667 133479714527964709360067 := by
  unfold tailWord_438667
  simp only [CollatzResearch.WordTrace]
  refine ⟨15999499901791852204154255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10666333267861234802769503 15999499901791852204154255)
  ·
    refine ⟨23999249852687778306231383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15999499901791852204154255 23999249852687778306231383)
    ·
      refine ⟨35998874779031667459347075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23999249852687778306231383 35998874779031667459347075)
      ·
        refine ⟨53998312168547501189020613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35998874779031667459347075 53998312168547501189020613)
        ·
          refine ⟨10124683531602656472941365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53998312168547501189020613 10124683531602656472941365)
          ·
            refine ⟨949189081087749044338253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10124683531602656472941365 949189081087749044338253)
            ·
              refine ⟨355945905407905891626845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 949189081087749044338253 355945905407905891626845)
              ·
                refine ⟨133479714527964709360067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355945905407905891626845 133479714527964709360067)
                ·
                  rfl

theorem cell19_438667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 3].length) (baseStart_438667 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438667 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438667 prefixEnd_438667 := by exact prefixLift 438667
  have htrace : WordTrace (prefixWord ++ tailWord_438667) baseStart_438667 baseEnd_438667 := by
    simpa [prefixWord, tailWord_438667, baseEnd_438667] using wordTrace_append hprefix tailTrace_438667
  have hstable : (prefixWord ++ tailWord_438667).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438667).length < 2 ^ (prefixWord ++ tailWord_438667).sum := by decide
  have hdescent : baseEnd_438667 < baseStart_438667 := by decide
  rcases family_descends (prefixWord ++ tailWord_438667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438688 : List Nat := [2, 1, 1, 4, 1, 4, 6]
def baseStart_438688 : Nat := 118140960795 + 438688 * 2 ^ 59
def prefixEnd_438688 : Nat := 4983230072969 + 3 ^ 40 * 438688 * 2
def baseEnd_438688 : Nat := 44495368169814294297781

theorem tailTrace_438688 : CollatzResearch.WordTrace tailWord_438688 prefixEnd_438688 44495368169814294297781 := by
  unfold tailWord_438688
  simp only [CollatzResearch.WordTrace]
  refine ⟨8000132917357886395334359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10666843889810515193779145 8000132917357886395334359)
  ·
    refine ⟨12000199376036829593001539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8000132917357886395334359 12000199376036829593001539)
    ·
      refine ⟨18000299064055244389502309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12000199376036829593001539 18000299064055244389502309)
      ·
        refine ⟨3375056074510358323031683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18000299064055244389502309 3375056074510358323031683)
        ·
          refine ⟨5062584111765537484547525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3375056074510358323031683 5062584111765537484547525)
          ·
            refine ⟨949234520956038278352661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5062584111765537484547525 949234520956038278352661)
            ·
              refine ⟨44495368169814294297781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 949234520956038278352661 44495368169814294297781)
              ·
                rfl

theorem cell19_438688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 6].length) (baseStart_438688 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438688 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438688 prefixEnd_438688 := by exact prefixLift 438688
  have htrace : WordTrace (prefixWord ++ tailWord_438688) baseStart_438688 baseEnd_438688 := by
    simpa [prefixWord, tailWord_438688, baseEnd_438688] using wordTrace_append hprefix tailTrace_438688
  have hstable : (prefixWord ++ tailWord_438688).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438688).length < 2 ^ (prefixWord ++ tailWord_438688).sum := by decide
  have hdescent : baseEnd_438688 < baseStart_438688 := by decide
  rcases family_descends (prefixWord ++ tailWord_438688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438762 : List Nat := [3, 1, 3, 1, 3, 2, 2, 4]
def baseStart_438762 : Nat := 118140960795 + 438762 * 2 ^ 59
def prefixEnd_438762 : Nat := 4983230072969 + 3 ^ 40 * 438762 * 2
def baseEnd_438762 : Nat := 133508621587032637248697

theorem tailTrace_438762 : CollatzResearch.WordTrace tailWord_438762 prefixEnd_438762 133508621587032637248697 := by
  unfold tailWord_438762
  simp only [CollatzResearch.WordTrace]
  refine ⟨4000741209111920857215635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10668643224298455619241693 4000741209111920857215635)
  ·
    refine ⟨6001111813667881285823453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4000741209111920857215635 6001111813667881285823453)
    ·
      refine ⟨2250416930125455482183795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6001111813667881285823453 2250416930125455482183795)
      ·
        refine ⟨3375625395188183223275693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2250416930125455482183795 3375625395188183223275693)
        ·
          refine ⟨1265859523195568708728385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3375625395188183223275693 1265859523195568708728385)
          ·
            refine ⟨949394642396676531546289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1265859523195568708728385 949394642396676531546289)
            ·
              refine ⟨712045981797507398659717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 949394642396676531546289 712045981797507398659717)
              ·
                refine ⟨133508621587032637248697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 712045981797507398659717 133508621587032637248697)
                ·
                  rfl

theorem cell19_438762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_438762 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438762 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438762 prefixEnd_438762 := by exact prefixLift 438762
  have htrace : WordTrace (prefixWord ++ tailWord_438762) baseStart_438762 baseEnd_438762 := by
    simpa [prefixWord, tailWord_438762, baseEnd_438762] using wordTrace_append hprefix tailTrace_438762
  have hstable : (prefixWord ++ tailWord_438762).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438762).length < 2 ^ (prefixWord ++ tailWord_438762).sum := by decide
  have hdescent : baseEnd_438762 < baseStart_438762 := by decide
  rcases family_descends (prefixWord ++ tailWord_438762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438764 : List Nat := [2, 2, 1, 1, 2, 1, 6, 4]
def baseStart_438764 : Nat := 118140960795 + 438764 * 2 ^ 59
def prefixEnd_438764 : Nat := 4983230072969 + 3 ^ 40 * 438764 * 2
def baseEnd_438764 : Nat := 133509230156697225204247

theorem tailTrace_438764 : CollatzResearch.WordTrace tailWord_438764 prefixEnd_438764 133509230156697225204247 := by
  unfold tailWord_438764
  simp only [CollatzResearch.WordTrace]
  refine ⟨8001518891220218885217673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10668691854960291846956897 8001518891220218885217673)
  ·
    refine ⟨6001139168415164163913255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8001518891220218885217673 6001139168415164163913255)
    ·
      refine ⟨9001708752622746245869883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6001139168415164163913255 9001708752622746245869883)
      ·
        refine ⟨13502563128934119368804825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9001708752622746245869883 13502563128934119368804825)
        ·
          refine ⟨10126922346700589526603619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13502563128934119368804825 10126922346700589526603619)
          ·
            refine ⟨15190383520050884289905429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10126922346700589526603619 15190383520050884289905429)
            ·
              refine ⟨712049227502385201089317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15190383520050884289905429 712049227502385201089317)
              ·
                refine ⟨133509230156697225204247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 712049227502385201089317 133509230156697225204247)
                ·
                  rfl

theorem cell19_438764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_438764 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438764 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438764 prefixEnd_438764 := by exact prefixLift 438764
  have htrace : WordTrace (prefixWord ++ tailWord_438764) baseStart_438764 baseEnd_438764 := by
    simpa [prefixWord, tailWord_438764, baseEnd_438764] using wordTrace_append hprefix tailTrace_438764
  have hstable : (prefixWord ++ tailWord_438764).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438764).length < 2 ^ (prefixWord ++ tailWord_438764).sum := by decide
  have hdescent : baseEnd_438764 < baseStart_438764 := by decide
  rcases family_descends (prefixWord ++ tailWord_438764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438819 : List Nat := [1, 1, 1, 4, 4, 3, 1, 4]
def baseStart_438819 : Nat := 118140960795 + 438819 * 2 ^ 59
def prefixEnd_438819 : Nat := 4983230072969 + 3 ^ 40 * 438819 * 2
def baseEnd_438819 : Nat := 133525965822473393981875

theorem tailTrace_438819 : CollatzResearch.WordTrace tailWord_438819 prefixEnd_438819 133525965822473393981875 := by
  unfold tailWord_438819
  simp only [CollatzResearch.WordTrace]
  refine ⟨16005043797241182163687511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10670029198160788109125007 16005043797241182163687511)
  ·
    refine ⟨24007565695861773245531267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16005043797241182163687511 24007565695861773245531267)
    ·
      refine ⟨36011348543792659868296901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24007565695861773245531267 36011348543792659868296901)
      ·
        refine ⟨6752127851961123725305669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36011348543792659868296901 6752127851961123725305669)
        ·
          refine ⟨1266023972242710698494813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6752127851961123725305669 1266023972242710698494813)
          ·
            refine ⟨474758989591016511935555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1266023972242710698494813 474758989591016511935555)
            ·
              refine ⟨712138484386524767903333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474758989591016511935555 712138484386524767903333)
              ·
                refine ⟨133525965822473393981875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 712138484386524767903333 133525965822473393981875)
                ·
                  rfl

theorem cell19_438819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 4].length) (baseStart_438819 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438819 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438819 prefixEnd_438819 := by exact prefixLift 438819
  have htrace : WordTrace (prefixWord ++ tailWord_438819) baseStart_438819 baseEnd_438819 := by
    simpa [prefixWord, tailWord_438819, baseEnd_438819] using wordTrace_append hprefix tailTrace_438819
  have hstable : (prefixWord ++ tailWord_438819).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438819).length < 2 ^ (prefixWord ++ tailWord_438819).sum := by decide
  have hdescent : baseEnd_438819 < baseStart_438819 := by decide
  rcases family_descends (prefixWord ++ tailWord_438819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438821 : List Nat := [1, 3, 1, 2, 2, 1, 5, 4]
def baseStart_438821 : Nat := 118140960795 + 438821 * 2 ^ 59
def prefixEnd_438821 : Nat := 4983230072969 + 3 ^ 40 * 438821 * 2
def baseEnd_438821 : Nat := 133526574392137981937425

theorem tailTrace_438821 : CollatzResearch.WordTrace tailWord_438821 prefixEnd_438821 133526574392137981937425 := by
  unfold tailWord_438821
  simp only [CollatzResearch.WordTrace]
  refine ⟨16005116743233936505260317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10670077828822624336840211 16005116743233936505260317)
  ·
    refine ⟨6001918778712726189472619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16005116743233936505260317 6001918778712726189472619)
    ·
      refine ⟨9002878168069089284208929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6001918778712726189472619 9002878168069089284208929)
      ·
        refine ⟨6752158626051816963156697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9002878168069089284208929 6752158626051816963156697)
        ·
          refine ⟨5064118969538862722367523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6752158626051816963156697 5064118969538862722367523)
          ·
            refine ⟨7596178454308294083551285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5064118969538862722367523 7596178454308294083551285)
            ·
              refine ⟨712141730091402570332933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7596178454308294083551285 712141730091402570332933)
              ·
                refine ⟨133526574392137981937425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 712141730091402570332933 133526574392137981937425)
                ·
                  rfl

theorem cell19_438821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_438821 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438821 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438821 prefixEnd_438821 := by exact prefixLift 438821
  have htrace : WordTrace (prefixWord ++ tailWord_438821) baseStart_438821 baseEnd_438821 := by
    simpa [prefixWord, tailWord_438821, baseEnd_438821] using wordTrace_append hprefix tailTrace_438821
  have hstable : (prefixWord ++ tailWord_438821).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438821).length < 2 ^ (prefixWord ++ tailWord_438821).sum := by decide
  have hdescent : baseEnd_438821 < baseStart_438821 := by decide
  rcases family_descends (prefixWord ++ tailWord_438821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438893 : List Nat := [1, 5, 1, 1, 3, 3, 2, 3]
def baseStart_438893 : Nat := 118140960795 + 438893 * 2 ^ 59
def prefixEnd_438893 : Nat := 4983230072969 + 3 ^ 40 * 438893 * 2
def baseEnd_438893 : Nat := 133548482900063148337229

theorem tailTrace_438893 : CollatzResearch.WordTrace tailWord_438893 prefixEnd_438893 133548482900063148337229 := by
  unfold tailWord_438893
  simp only [CollatzResearch.WordTrace]
  refine ⟨16007742798973092801881333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10671828532648728534587555 16007742798973092801881333)
  ·
    refine ⟨1500725887403727450176375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16007742798973092801881333 1500725887403727450176375)
    ·
      refine ⟨2251088831105591175264563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1500725887403727450176375 2251088831105591175264563)
      ·
        refine ⟨3376633246658386762896845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2251088831105591175264563 3376633246658386762896845)
        ·
          refine ⟨1266237467496895036086317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3376633246658386762896845 1266237467496895036086317)
          ·
            refine ⟨474839050311335638532369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1266237467496895036086317 474839050311335638532369)
            ·
              refine ⟨356129287733501728899277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474839050311335638532369 356129287733501728899277)
              ·
                refine ⟨133548482900063148337229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 356129287733501728899277 133548482900063148337229)
                ·
                  rfl

theorem cell19_438893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 3].length) (baseStart_438893 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438893 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438893 prefixEnd_438893 := by exact prefixLift 438893
  have htrace : WordTrace (prefixWord ++ tailWord_438893) baseStart_438893 baseEnd_438893 := by
    simpa [prefixWord, tailWord_438893, baseEnd_438893] using wordTrace_append hprefix tailTrace_438893
  have hstable : (prefixWord ++ tailWord_438893).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438893).length < 2 ^ (prefixWord ++ tailWord_438893).sum := by decide
  have hdescent : baseEnd_438893 < baseStart_438893 := by decide
  rcases family_descends (prefixWord ++ tailWord_438893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438916 : List Nat := [2, 3, 2, 1, 3, 1, 7]
def baseStart_438916 : Nat := 118140960795 + 438916 * 2 ^ 59
def prefixEnd_438916 : Nat := 4983230072969 + 3 ^ 40 * 438916 * 2
def baseEnd_438916 : Nat := 44518493817068636608685

theorem tailTrace_438916 : CollatzResearch.WordTrace tailWord_438916 prefixEnd_438916 44518493817068636608685 := by
  unfold tailWord_438916
  simp only [CollatzResearch.WordTrace]
  refine ⟨8004290838944883864984301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10672387785259845153312401 8004290838944883864984301)
  ·
    refine ⟨3001609064604331449369113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8004290838944883864984301 3001609064604331449369113)
    ·
      refine ⟨2251206798453248587026835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3001609064604331449369113 2251206798453248587026835)
      ·
        refine ⟨3376810197679872880540253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2251206798453248587026835 3376810197679872880540253)
        ·
          refine ⟨1266303824129952330202595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3376810197679872880540253 1266303824129952330202595)
          ·
            refine ⟨1899455736194928495303893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266303824129952330202595 1899455736194928495303893)
            ·
              refine ⟨44518493817068636608685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1899455736194928495303893 44518493817068636608685)
              ·
                rfl

theorem cell19_438916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 7].length) (baseStart_438916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438916 prefixEnd_438916 := by exact prefixLift 438916
  have htrace : WordTrace (prefixWord ++ tailWord_438916) baseStart_438916 baseEnd_438916 := by
    simpa [prefixWord, tailWord_438916, baseEnd_438916] using wordTrace_append hprefix tailTrace_438916
  have hstable : (prefixWord ++ tailWord_438916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438916).length < 2 ^ (prefixWord ++ tailWord_438916).sum := by decide
  have hdescent : baseEnd_438916 < baseStart_438916 := by decide
  rcases family_descends (prefixWord ++ tailWord_438916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438935 : List Nat := [1, 1, 3, 3, 2, 1, 4, 4]
def baseStart_438935 : Nat := 118140960795 + 438935 * 2 ^ 59
def prefixEnd_438935 : Nat := 4983230072969 + 3 ^ 40 * 438935 * 2
def baseEnd_438935 : Nat := 133561262863019495403781

theorem tailTrace_438935 : CollatzResearch.WordTrace tailWord_438935 prefixEnd_438935 133561262863019495403781 := by
  unfold tailWord_438935
  simp only [CollatzResearch.WordTrace]
  refine ⟨16009274664820933974910259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10672849776547289316606839 16009274664820933974910259)
  ·
    refine ⟨24013911997231400962365389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16009274664820933974910259 24013911997231400962365389)
    ·
      refine ⟨9005216998961775360887021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24013911997231400962365389 9005216998961775360887021)
      ·
        refine ⟨3376956374610665760332633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9005216998961775360887021 3376956374610665760332633)
        ·
          refine ⟨2532717280957999320249475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3376956374610665760332633 2532717280957999320249475)
          ·
            refine ⟨3799075921436998980374213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2532717280957999320249475 3799075921436998980374213)
            ·
              refine ⟨712326735269437308820165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3799075921436998980374213 712326735269437308820165)
              ·
                refine ⟨133561262863019495403781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 712326735269437308820165 133561262863019495403781)
                ·
                  rfl

theorem cell19_438935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_438935 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438935 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438935 prefixEnd_438935 := by exact prefixLift 438935
  have htrace : WordTrace (prefixWord ++ tailWord_438935) baseStart_438935 baseEnd_438935 := by
    simpa [prefixWord, tailWord_438935, baseEnd_438935] using wordTrace_append hprefix tailTrace_438935
  have hstable : (prefixWord ++ tailWord_438935).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438935).length < 2 ^ (prefixWord ++ tailWord_438935).sum := by decide
  have hdescent : baseEnd_438935 < baseStart_438935 := by decide
  rcases family_descends (prefixWord ++ tailWord_438935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438975 : List Nat := [1, 1, 2, 2, 2, 11]
def baseStart_438975 : Nat := 118140960795 + 438975 * 2 ^ 59
def prefixEnd_438975 : Nat := 4983230072969 + 3 ^ 40 * 438975 * 2
def baseEnd_438975 : Nat := 14841492695145694946087

theorem tailTrace_438975 : CollatzResearch.WordTrace tailWord_438975 prefixEnd_438975 14841492695145694946087 := by
  unfold tailWord_438975
  simp only [CollatzResearch.WordTrace]
  refine ⟨16010733584676020806366379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10673822389784013870910919 16010733584676020806366379)
  ·
    refine ⟨24016100377014031209549569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16010733584676020806366379 24016100377014031209549569)
    ·
      refine ⟨18012075282760523407162177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24016100377014031209549569 18012075282760523407162177)
      ·
        refine ⟨13509056462070392555371633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18012075282760523407162177 13509056462070392555371633)
        ·
          refine ⟨10131792346552794416528725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13509056462070392555371633 10131792346552794416528725)
          ·
            refine ⟨14841492695145694946087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10131792346552794416528725 14841492695145694946087)
            ·
              rfl

theorem cell19_438975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 11].length) (baseStart_438975 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438975 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438975 prefixEnd_438975 := by exact prefixLift 438975
  have htrace : WordTrace (prefixWord ++ tailWord_438975) baseStart_438975 baseEnd_438975 := by
    simpa [prefixWord, tailWord_438975, baseEnd_438975] using wordTrace_append hprefix tailTrace_438975
  have hstable : (prefixWord ++ tailWord_438975).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438975).length < 2 ^ (prefixWord ++ tailWord_438975).sum := by decide
  have hdescent : baseEnd_438975 < baseStart_438975 := by decide
  rcases family_descends (prefixWord ++ tailWord_438975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_438990 : List Nat := [4, 1, 1, 1, 3, 4, 1, 4]
def baseStart_438990 : Nat := 118140960795 + 438990 * 2 ^ 59
def prefixEnd_438990 : Nat := 4983230072969 + 3 ^ 40 * 438990 * 2
def baseEnd_438990 : Nat := 133577998528795664181409

theorem tailTrace_438990 : CollatzResearch.WordTrace tailWord_438990 prefixEnd_438990 133577998528795664181409 := by
  unfold tailWord_438990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2001410084952709796020303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10674187119747785578774949 2001410084952709796020303)
  ·
    refine ⟨3002115127429064694030455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2001410084952709796020303 3002115127429064694030455)
    ·
      refine ⟨4503172691143597041045683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3002115127429064694030455 4503172691143597041045683)
      ·
        refine ⟨6754759036715395561568525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4503172691143597041045683 6754759036715395561568525)
        ·
          refine ⟨2533034638768273335588197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6754759036715395561568525 2533034638768273335588197)
          ·
            refine ⟨474943994769051250422787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2533034638768273335588197 474943994769051250422787)
            ·
              refine ⟨712415992153576875634181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474943994769051250422787 712415992153576875634181)
              ·
                refine ⟨133577998528795664181409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 712415992153576875634181 133577998528795664181409)
                ·
                  rfl

theorem cell19_438990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_438990 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_438990 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_438990 prefixEnd_438990 := by exact prefixLift 438990
  have htrace : WordTrace (prefixWord ++ tailWord_438990) baseStart_438990 baseEnd_438990 := by
    simpa [prefixWord, tailWord_438990, baseEnd_438990] using wordTrace_append hprefix tailTrace_438990
  have hstable : (prefixWord ++ tailWord_438990).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_438990).length < 2 ^ (prefixWord ++ tailWord_438990).sum := by decide
  have hdescent : baseEnd_438990 < baseStart_438990 := by decide
  rcases family_descends (prefixWord ++ tailWord_438990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439009 : List Nat := [1, 2, 3, 1, 4, 2, 3, 3]
def baseStart_439009 : Nat := 118140960795 + 439009 * 2 ^ 59
def prefixEnd_439009 : Nat := 4983230072969 + 3 ^ 40 * 439009 * 2
def baseEnd_439009 : Nat := 133583779940609249759135

theorem tailTrace_439009 : CollatzResearch.WordTrace tailWord_439009 prefixEnd_439009 133583779940609249759135 := by
  unfold tailWord_439009
  simp only [CollatzResearch.WordTrace]
  refine ⟨16011973666552844613104081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10674649111035229742069387 16011973666552844613104081)
  ·
    refine ⟨12008980249914633459828061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16011973666552844613104081 12008980249914633459828061)
    ·
      refine ⟨4503367593717987547435523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12008980249914633459828061 4503367593717987547435523)
      ·
        refine ⟨6755051390576981321153285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4503367593717987547435523 6755051390576981321153285)
        ·
          refine ⟨1266572135733183997716241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6755051390576981321153285 1266572135733183997716241)
          ·
            refine ⟨949929101799887998287181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1266572135733183997716241 949929101799887998287181)
            ·
              refine ⟨356223413174957999357693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 949929101799887998287181 356223413174957999357693)
              ·
                refine ⟨133583779940609249759135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 356223413174957999357693 133583779940609249759135)
                ·
                  rfl

theorem cell19_439009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 3].length) (baseStart_439009 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439009 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439009 prefixEnd_439009 := by exact prefixLift 439009
  have htrace : WordTrace (prefixWord ++ tailWord_439009) baseStart_439009 baseEnd_439009 := by
    simpa [prefixWord, tailWord_439009, baseEnd_439009] using wordTrace_append hprefix tailTrace_439009
  have hstable : (prefixWord ++ tailWord_439009).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439009).length < 2 ^ (prefixWord ++ tailWord_439009).sum := by decide
  have hdescent : baseEnd_439009 < baseStart_439009 := by decide
  rcases family_descends (prefixWord ++ tailWord_439009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439030 : List Nat := [5, 1, 1, 1, 1, 2, 8]
def baseStart_439030 : Nat := 118140960795 + 439030 * 2 ^ 59
def prefixEnd_439030 : Nat := 4983230072969 + 3 ^ 40 * 439030 * 2
def baseEnd_439030 : Nat := 44530056640695807764137

theorem tailTrace_439030 : CollatzResearch.WordTrace tailWord_439030 prefixEnd_439030 44530056640695807764137 := by
  unfold tailWord_439030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1000796224967297824976159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10675159732984510133079029 1000796224967297824976159)
  ·
    refine ⟨1501194337450946737464239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1000796224967297824976159 1501194337450946737464239)
    ·
      refine ⟨2251791506176420106196359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1501194337450946737464239 2251791506176420106196359)
      ·
        refine ⟨3377687259264630159294539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2251791506176420106196359 3377687259264630159294539)
        ·
          refine ⟨5066530888896945238941809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3377687259264630159294539 5066530888896945238941809)
          ·
            refine ⟨3799898166672708929206357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5066530888896945238941809 3799898166672708929206357)
            ·
              refine ⟨44530056640695807764137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3799898166672708929206357 44530056640695807764137)
              ·
                rfl

theorem cell19_439030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 8].length) (baseStart_439030 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439030 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439030 prefixEnd_439030 := by exact prefixLift 439030
  have htrace : WordTrace (prefixWord ++ tailWord_439030) baseStart_439030 baseEnd_439030 := by
    simpa [prefixWord, tailWord_439030, baseEnd_439030] using wordTrace_append hprefix tailTrace_439030
  have hstable : (prefixWord ++ tailWord_439030).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439030).length < 2 ^ (prefixWord ++ tailWord_439030).sum := by decide
  have hdescent : baseEnd_439030 < baseStart_439030 := by decide
  rcases family_descends (prefixWord ++ tailWord_439030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439032 : List Nat := [2, 1, 2, 1, 1, 2, 10]
def baseStart_439032 : Nat := 118140960795 + 439032 * 2 ^ 59
def prefixEnd_439032 : Nat := 4983230072969 + 3 ^ 40 * 439032 * 2
def baseEnd_439032 : Nat := 44530259497250670415987

theorem tailTrace_439032 : CollatzResearch.WordTrace tailWord_439032 prefixEnd_439032 44530259497250670415987 := by
  unfold tailWord_439032
  simp only [CollatzResearch.WordTrace]
  refine ⟨8006406272734759770595675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10675208363646346360794233 8006406272734759770595675)
  ·
    refine ⟨12009609409102139655893513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8006406272734759770595675 12009609409102139655893513)
    ·
      refine ⟨9007207056826604741920135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12009609409102139655893513 9007207056826604741920135)
      ·
        refine ⟨13510810585239907112880203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9007207056826604741920135 13510810585239907112880203)
        ·
          refine ⟨20266215877859860669320305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13510810585239907112880203 20266215877859860669320305)
          ·
            refine ⟨15199661908394895501990229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20266215877859860669320305 15199661908394895501990229)
            ·
              refine ⟨44530259497250670415987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15199661908394895501990229 44530259497250670415987)
              ·
                rfl

theorem cell19_439032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 10].length) (baseStart_439032 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439032 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439032 prefixEnd_439032 := by exact prefixLift 439032
  have htrace : WordTrace (prefixWord ++ tailWord_439032) baseStart_439032 baseEnd_439032 := by
    simpa [prefixWord, tailWord_439032, baseEnd_439032] using wordTrace_append hprefix tailTrace_439032
  have hstable : (prefixWord ++ tailWord_439032).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439032).length < 2 ^ (prefixWord ++ tailWord_439032).sum := by decide
  have hdescent : baseEnd_439032 < baseStart_439032 := by decide
  rcases family_descends (prefixWord ++ tailWord_439032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439051 : List Nat := [1, 1, 1, 1, 5, 1, 1, 8]
def baseStart_439051 : Nat := 118140960795 + 439051 * 2 ^ 59
def prefixEnd_439051 : Nat := 4983230072969 + 3 ^ 40 * 439051 * 2
def baseEnd_439051 : Nat := 133596559903565596825687

theorem tailTrace_439051 : CollatzResearch.WordTrace tailWord_439051 prefixEnd_439051 133596559903565596825687 := by
  unfold tailWord_439051
  simp only [CollatzResearch.WordTrace]
  refine ⟨16013505532400685786133007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10675670354933790524088671 16013505532400685786133007)
  ·
    refine ⟨24020258298601028679199511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16013505532400685786133007 24020258298601028679199511)
    ·
      refine ⟨36030387447901543018799267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24020258298601028679199511 36030387447901543018799267)
      ·
        refine ⟨54045581171852314528198901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36030387447901543018799267 54045581171852314528198901)
        ·
          refine ⟨5066773234861154487018647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54045581171852314528198901 5066773234861154487018647)
          ·
            refine ⟨7600159852291731730527971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5066773234861154487018647 7600159852291731730527971)
            ·
              refine ⟨11400239778437597595791957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7600159852291731730527971 11400239778437597595791957)
              ·
                refine ⟨133596559903565596825687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11400239778437597595791957 133596559903565596825687)
                ·
                  rfl

theorem cell19_439051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_439051 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439051 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439051 prefixEnd_439051 := by exact prefixLift 439051
  have htrace : WordTrace (prefixWord ++ tailWord_439051) baseStart_439051 baseEnd_439051 := by
    simpa [prefixWord, tailWord_439051, baseEnd_439051] using wordTrace_append hprefix tailTrace_439051
  have hstable : (prefixWord ++ tailWord_439051).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439051).length < 2 ^ (prefixWord ++ tailWord_439051).sum := by decide
  have hdescent : baseEnd_439051 < baseStart_439051 := by decide
  rcases family_descends (prefixWord ++ tailWord_439051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439068 : List Nat := [2, 2, 3, 1, 1, 4, 1, 5]
def baseStart_439068 : Nat := 118140960795 + 439068 * 2 ^ 59
def prefixEnd_439068 : Nat := 4983230072969 + 3 ^ 40 * 439068 * 2
def baseEnd_439068 : Nat := 133601732745714594447863

theorem tailTrace_439068 : CollatzResearch.WordTrace tailWord_439068 prefixEnd_439068 133601732745714594447863 := by
  unfold tailWord_439068
  simp only [CollatzResearch.WordTrace]
  refine ⟨8007062786669548844750929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10676083715559398459667905 8007062786669548844750929)
  ·
    refine ⟨6005297090002161633563197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8007062786669548844750929 6005297090002161633563197)
    ·
      refine ⟨2251986408750810612586199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6005297090002161633563197 2251986408750810612586199)
      ·
        refine ⟨3377979613126215918879299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2251986408750810612586199 3377979613126215918879299)
        ·
          refine ⟨5066969419689323878318949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3377979613126215918879299 5066969419689323878318949)
          ·
            refine ⟨950056766191748227184803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5066969419689323878318949 950056766191748227184803)
            ·
              refine ⟨1425085149287622340777205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 950056766191748227184803 1425085149287622340777205)
              ·
                refine ⟨133601732745714594447863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1425085149287622340777205 133601732745714594447863)
                ·
                  rfl

theorem cell19_439068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_439068 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439068 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439068 prefixEnd_439068 := by exact prefixLift 439068
  have htrace : WordTrace (prefixWord ++ tailWord_439068) baseStart_439068 baseEnd_439068 := by
    simpa [prefixWord, tailWord_439068, baseEnd_439068] using wordTrace_append hprefix tailTrace_439068
  have hstable : (prefixWord ++ tailWord_439068).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439068).length < 2 ^ (prefixWord ++ tailWord_439068).sum := by decide
  have hdescent : baseEnd_439068 < baseStart_439068 := by decide
  rcases family_descends (prefixWord ++ tailWord_439068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439146 : List Nat := [3, 1, 3, 12]
def baseStart_439146 : Nat := 118140960795 + 439146 * 2 ^ 59
def prefixEnd_439146 : Nat := 4983230072969 + 3 ^ 40 * 439146 * 2
def baseEnd_439146 : Nat := 1649697122995475613757

theorem tailTrace_439146 : CollatzResearch.WordTrace tailWord_439146 prefixEnd_439146 1649697122995475613757 := by
  unfold tailWord_439146
  simp only [CollatzResearch.WordTrace]
  refine ⟨4004242616764129252710323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10677980311371011340560861 4004242616764129252710323)
  ·
    refine ⟨6006363925146193879065485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4004242616764129252710323 6006363925146193879065485)
    ·
      refine ⟨2252386471929822704649557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6006363925146193879065485 2252386471929822704649557)
      ·
        refine ⟨1649697122995475613757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 2252386471929822704649557 1649697122995475613757)
        ·
          rfl

theorem cell19_439146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 12].length) (baseStart_439146 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439146 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439146 prefixEnd_439146 := by exact prefixLift 439146
  have htrace : WordTrace (prefixWord ++ tailWord_439146) baseStart_439146 baseEnd_439146 := by
    simpa [prefixWord, tailWord_439146, baseEnd_439146] using wordTrace_append hprefix tailTrace_439146
  have hstable : (prefixWord ++ tailWord_439146).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439146).length < 2 ^ (prefixWord ++ tailWord_439146).sum := by decide
  have hdescent : baseEnd_439146 < baseStart_439146 := by decide
  rcases family_descends (prefixWord ++ tailWord_439146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439201 : List Nat := [1, 2, 3, 4, 1, 2, 6]
def baseStart_439201 : Nat := 118140960795 + 439201 * 2 ^ 59
def prefixEnd_439201 : Nat := 4983230072969 + 3 ^ 40 * 439201 * 2
def baseEnd_439201 : Nat := 44547400876136564497315

theorem tailTrace_439201 : CollatzResearch.WordTrace tailWord_439201 prefixEnd_439201 44547400876136564497315 := by
  unfold tailWord_439201
  simp only [CollatzResearch.WordTrace]
  refine ⟨16018976481857261404093457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10679317654571507602728971 16018976481857261404093457)
  ·
    refine ⟨12014232361392946053070093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16018976481857261404093457 12014232361392946053070093)
    ·
      refine ⟨4505337135522354769901285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12014232361392946053070093 4505337135522354769901285)
      ·
        refine ⟨844750712910441519356491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4505337135522354769901285 844750712910441519356491)
        ·
          refine ⟨1267126069365662279034737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844750712910441519356491 1267126069365662279034737)
          ·
            refine ⟨950344552024246709276053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1267126069365662279034737 950344552024246709276053)
            ·
              refine ⟨44547400876136564497315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 950344552024246709276053 44547400876136564497315)
              ·
                rfl

theorem cell19_439201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 6].length) (baseStart_439201 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439201 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439201 prefixEnd_439201 := by exact prefixLift 439201
  have htrace : WordTrace (prefixWord ++ tailWord_439201) baseStart_439201 baseEnd_439201 := by
    simpa [prefixWord, tailWord_439201, baseEnd_439201] using wordTrace_append hprefix tailTrace_439201
  have hstable : (prefixWord ++ tailWord_439201).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439201).length < 2 ^ (prefixWord ++ tailWord_439201).sum := by decide
  have hdescent : baseEnd_439201 < baseStart_439201 := by decide
  rcases family_descends (prefixWord ++ tailWord_439201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439239 : List Nat := [1, 1, 4, 1, 1, 2, 6, 3]
def baseStart_439239 : Nat := 118140960795 + 439239 * 2 ^ 59
def prefixEnd_439239 : Nat := 4983230072969 + 3 ^ 40 * 439239 * 2
def baseEnd_439239 : Nat := 133653765452036864647397

theorem tailTrace_439239 : CollatzResearch.WordTrace tailWord_439239 prefixEnd_439239 133653765452036864647397 := by
  unfold tailWord_439239
  simp only [CollatzResearch.WordTrace]
  refine ⟨16020362455719593893976771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10680241637146395929317847 16020362455719593893976771)
  ·
    refine ⟨24030543683579390840965157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16020362455719593893976771 24030543683579390840965157)
    ·
      refine ⟨4505726940671135782680967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24030543683579390840965157 4505726940671135782680967)
      ·
        refine ⟨6758590411006703674021451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4505726940671135782680967 6758590411006703674021451)
        ·
          refine ⟨10137885616510055511032177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6758590411006703674021451 10137885616510055511032177)
          ·
            refine ⟨7603414212382541633274133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10137885616510055511032177 7603414212382541633274133)
            ·
              refine ⟨356410041205431639059725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7603414212382541633274133 356410041205431639059725)
              ·
                refine ⟨133653765452036864647397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 356410041205431639059725 133653765452036864647397)
                ·
                  rfl

theorem cell19_439239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 3].length) (baseStart_439239 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439239 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439239 prefixEnd_439239 := by exact prefixLift 439239
  have htrace : WordTrace (prefixWord ++ tailWord_439239) baseStart_439239 baseEnd_439239 := by
    simpa [prefixWord, tailWord_439239, baseEnd_439239] using wordTrace_append hprefix tailTrace_439239
  have hstable : (prefixWord ++ tailWord_439239).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439239).length < 2 ^ (prefixWord ++ tailWord_439239).sum := by decide
  have hdescent : baseEnd_439239 < baseStart_439239 := by decide
  rcases family_descends (prefixWord ++ tailWord_439239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439258 : List Nat := [3, 1, 1, 2, 4, 3, 5]
def baseStart_439258 : Nat := 118140960795 + 439258 * 2 ^ 59
def prefixEnd_439258 : Nat := 4983230072969 + 3 ^ 40 * 439258 * 2
def baseEnd_439258 : Nat := 44553182287950150075041

theorem tailTrace_439258 : CollatzResearch.WordTrace tailWord_439258 prefixEnd_439258 44553182287950150075041 := by
  unfold tailWord_439258
  simp only [CollatzResearch.WordTrace]
  refine ⟨4005263860662690034729607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10680703628433840092612285 4005263860662690034729607)
  ·
    refine ⟨6007895790994035052094411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4005263860662690034729607 6007895790994035052094411)
    ·
      refine ⟨9011843686491052578141617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6007895790994035052094411 9011843686491052578141617)
      ·
        refine ⟨6758882764868289433606213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9011843686491052578141617 6758882764868289433606213)
        ·
          refine ⟨1267290518412804268801165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6758882764868289433606213 1267290518412804268801165)
          ·
            refine ⟨475233944404801600800437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1267290518412804268801165 475233944404801600800437)
            ·
              refine ⟨44553182287950150075041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 475233944404801600800437 44553182287950150075041)
              ·
                rfl

theorem cell19_439258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 5].length) (baseStart_439258 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439258 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439258 prefixEnd_439258 := by exact prefixLift 439258
  have htrace : WordTrace (prefixWord ++ tailWord_439258) baseStart_439258 baseEnd_439258 := by
    simpa [prefixWord, tailWord_439258, baseEnd_439258] using wordTrace_append hprefix tailTrace_439258
  have hstable : (prefixWord ++ tailWord_439258).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439258).length < 2 ^ (prefixWord ++ tailWord_439258).sum := by decide
  have hdescent : baseEnd_439258 < baseStart_439258 := by decide
  rcases family_descends (prefixWord ++ tailWord_439258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439279 : List Nat := [1, 1, 2, 1, 4, 3, 1, 6]
def baseStart_439279 : Nat := 118140960795 + 439279 * 2 ^ 59
def prefixEnd_439279 : Nat := 4983230072969 + 3 ^ 40 * 439279 * 2
def baseEnd_439279 : Nat := 133665936845328623758399

theorem tailTrace_439279 : CollatzResearch.WordTrace tailWord_439279 prefixEnd_439279 133665936845328623758399 := by
  unfold tailWord_439279
  simp only [CollatzResearch.WordTrace]
  refine ⟨16021821375574680725432891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10681214250383120483621927 16021821375574680725432891)
  ·
    refine ⟨24032732063362021088149337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16021821375574680725432891 24032732063362021088149337)
    ·
      refine ⟨18024549047521515816112003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24032732063362021088149337 18024549047521515816112003)
      ·
        refine ⟨27036823571282273724168005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18024549047521515816112003 27036823571282273724168005)
        ·
          refine ⟨5069404419615426323281501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27036823571282273724168005 5069404419615426323281501)
          ·
            refine ⟨1901026657355784871230563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5069404419615426323281501 1901026657355784871230563)
            ·
              refine ⟨2851539986033677306845845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1901026657355784871230563 2851539986033677306845845)
              ·
                refine ⟨133665936845328623758399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2851539986033677306845845 133665936845328623758399)
                ·
                  rfl

theorem cell19_439279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_439279 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439279 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439279 prefixEnd_439279 := by exact prefixLift 439279
  have htrace : WordTrace (prefixWord ++ tailWord_439279) baseStart_439279 baseEnd_439279 := by
    simpa [prefixWord, tailWord_439279, baseEnd_439279] using wordTrace_append hprefix tailTrace_439279
  have hstable : (prefixWord ++ tailWord_439279).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439279).length < 2 ^ (prefixWord ++ tailWord_439279).sum := by decide
  have hdescent : baseEnd_439279 < baseStart_439279 := by decide
  rcases family_descends (prefixWord ++ tailWord_439279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439317 : List Nat := [1, 3, 2, 1, 4, 8]
def baseStart_439317 : Nat := 118140960795 + 439317 * 2 ^ 59
def prefixEnd_439317 : Nat := 4983230072969 + 3 ^ 40 * 439317 * 2
def baseEnd_439317 : Nat := 14853055518772866101539

theorem tailTrace_439317 : CollatzResearch.WordTrace tailWord_439317 prefixEnd_439317 14853055518772866101539 := by
  unfold tailWord_439317
  simp only [CollatzResearch.WordTrace]
  refine ⟨16023207349437013215316205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10682138232958008810210803 16023207349437013215316205)
  ·
    refine ⟨6008702756038879955743577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16023207349437013215316205 6008702756038879955743577)
    ·
      refine ⟨4506527067029159966807683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6008702756038879955743577 4506527067029159966807683)
      ·
        refine ⟨6759790600543739950211525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4506527067029159966807683 6759790600543739950211525)
        ·
          refine ⟨1267460737601951240664661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6759790600543739950211525 1267460737601951240664661)
          ·
            refine ⟨14853055518772866101539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1267460737601951240664661 14853055518772866101539)
            ·
              rfl

theorem cell19_439317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 8].length) (baseStart_439317 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439317 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439317 prefixEnd_439317 := by exact prefixLift 439317
  have htrace : WordTrace (prefixWord ++ tailWord_439317) baseStart_439317 baseEnd_439317 := by
    simpa [prefixWord, tailWord_439317, baseEnd_439317] using wordTrace_append hprefix tailTrace_439317
  have hstable : (prefixWord ++ tailWord_439317).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439317).length < 2 ^ (prefixWord ++ tailWord_439317).sum := by decide
  have hdescent : baseEnd_439317 < baseStart_439317 := by decide
  rcases family_descends (prefixWord ++ tailWord_439317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439332 : List Nat := [2, 3, 1, 4, 1, 3, 1, 4]
def baseStart_439332 : Nat := 118140960795 + 439332 * 2 ^ 59
def prefixEnd_439332 : Nat := 4983230072969 + 3 ^ 40 * 439332 * 2
def baseEnd_439332 : Nat := 133682063941440204580477

theorem tailTrace_439332 : CollatzResearch.WordTrace tailWord_439332 prefixEnd_439332 133682063941440204580477 := by
  unfold tailWord_439332
  simp only [CollatzResearch.WordTrace]
  refine ⟨8011877222191335388556125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10682502962921780518074833 8011877222191335388556125)
  ·
    refine ⟨3004453958321750770708547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8011877222191335388556125 3004453958321750770708547)
    ·
      refine ⟨4506680937482626156062821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3004453958321750770708547 4506680937482626156062821)
      ·
        refine ⟨845002675777992404261779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4506680937482626156062821 845002675777992404261779)
        ·
          refine ⟨1267504013666988606392669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845002675777992404261779 1267504013666988606392669)
          ·
            refine ⟨475314005125120727397251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1267504013666988606392669 475314005125120727397251)
            ·
              refine ⟨712971007687681091095877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475314005125120727397251 712971007687681091095877)
              ·
                refine ⟨133682063941440204580477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 712971007687681091095877 133682063941440204580477)
                ·
                  rfl

theorem cell19_439332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_439332 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439332 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439332 prefixEnd_439332 := by exact prefixLift 439332
  have htrace : WordTrace (prefixWord ++ tailWord_439332) baseStart_439332 baseEnd_439332 := by
    simpa [prefixWord, tailWord_439332, baseEnd_439332] using wordTrace_append hprefix tailTrace_439332
  have hstable : (prefixWord ++ tailWord_439332).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439332).length < 2 ^ (prefixWord ++ tailWord_439332).sum := by decide
  have hdescent : baseEnd_439332 < baseStart_439332 := by decide
  rcases family_descends (prefixWord ++ tailWord_439332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439374 : List Nat := [4, 1, 1, 1, 1, 3, 8]
def baseStart_439374 : Nat := 118140960795 + 439374 * 2 ^ 59
def prefixEnd_439374 : Nat := 4983230072969 + 3 ^ 40 * 439374 * 2
def baseEnd_439374 : Nat := 44564947968132183882343

theorem tailTrace_439374 : CollatzResearch.WordTrace tailWord_439374 prefixEnd_439374 44564947968132183882343 := by
  unfold tailWord_439374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2003160788778813993767647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10683524206820341300094117 2003160788778813993767647)
  ·
    refine ⟨3004741183168220990651471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2003160788778813993767647 3004741183168220990651471)
    ·
      refine ⟨4507111774752331485977207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3004741183168220990651471 4507111774752331485977207)
      ·
        refine ⟨6760667662128497228965811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4507111774752331485977207 6760667662128497228965811)
        ·
          refine ⟨10141001493192745843448717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6760667662128497228965811 10141001493192745843448717)
          ·
            refine ⟨3802875559947279691293269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10141001493192745843448717 3802875559947279691293269)
            ·
              refine ⟨44564947968132183882343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3802875559947279691293269 44564947968132183882343)
              ·
                rfl

theorem cell19_439374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 8].length) (baseStart_439374 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439374 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439374 prefixEnd_439374 := by exact prefixLift 439374
  have htrace : WordTrace (prefixWord ++ tailWord_439374) baseStart_439374 baseEnd_439374 := by
    simpa [prefixWord, tailWord_439374, baseEnd_439374] using wordTrace_append hprefix tailTrace_439374
  have hstable : (prefixWord ++ tailWord_439374).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439374).length < 2 ^ (prefixWord ++ tailWord_439374).sum := by decide
  have hdescent : baseEnd_439374 < baseStart_439374 := by decide
  rcases family_descends (prefixWord ++ tailWord_439374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439429 : List Nat := [1, 3, 1, 1, 6, 2, 5]
def baseStart_439429 : Nat := 118140960795 + 439429 * 2 ^ 59
def prefixEnd_439429 : Nat := 4983230072969 + 3 ^ 40 * 439429 * 2
def baseEnd_439429 : Nat := 44570526523390906808219

theorem tailTrace_439429 : CollatzResearch.WordTrace tailWord_439429 prefixEnd_439429 44570526523390906808219 := by
  unfold tailWord_439429
  simp only [CollatzResearch.WordTrace]
  refine ⟨16027292325031256343393341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10684861550020837562262227 16027292325031256343393341)
  ·
    refine ⟨6010234621886721128772503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16027292325031256343393341 6010234621886721128772503)
    ·
      refine ⟨9015351932830081693158755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6010234621886721128772503 9015351932830081693158755)
      ·
        refine ⟨13523027899245122539738133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9015351932830081693158755 13523027899245122539738133)
        ·
          refine ⟨633891932777115119050225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13523027899245122539738133 633891932777115119050225)
          ·
            refine ⟨475418949582836339287669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 633891932777115119050225 475418949582836339287669)
            ·
              refine ⟨44570526523390906808219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 475418949582836339287669 44570526523390906808219)
              ·
                rfl

theorem cell19_439429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 5].length) (baseStart_439429 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439429 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439429 prefixEnd_439429 := by exact prefixLift 439429
  have htrace : WordTrace (prefixWord ++ tailWord_439429) baseStart_439429 baseEnd_439429 := by
    simpa [prefixWord, tailWord_439429, baseEnd_439429] using wordTrace_append hprefix tailTrace_439429
  have hstable : (prefixWord ++ tailWord_439429).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439429).length < 2 ^ (prefixWord ++ tailWord_439429).sum := by decide
  have hdescent : baseEnd_439429 < baseStart_439429 := by decide
  rcases family_descends (prefixWord ++ tailWord_439429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439448 : List Nat := [2, 1, 2, 4, 2, 2, 2, 4]
def baseStart_439448 : Nat := 118140960795 + 439448 * 2 ^ 59
def prefixEnd_439448 : Nat := 4983230072969 + 3 ^ 40 * 439448 * 2
def baseEnd_439448 : Nat := 133717360981986306002383

theorem tailTrace_439448 : CollatzResearch.WordTrace tailWord_439448 prefixEnd_439448 133717360981986306002383 := by
  unfold tailWord_439448
  simp only [CollatzResearch.WordTrace]
  refine ⟨8013992655981211294167499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10685323541308281725556665 8013992655981211294167499)
  ·
    refine ⟨12020988983971816941251249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8013992655981211294167499 12020988983971816941251249)
    ·
      refine ⟨9015741737978862705938437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12020988983971816941251249 9015741737978862705938437)
      ·
        refine ⟨1690451575871036757363457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9015741737978862705938437 1690451575871036757363457)
        ·
          refine ⟨1267838681903277568022593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1690451575871036757363457 1267838681903277568022593)
          ·
            refine ⟨950879011427458176016945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1267838681903277568022593 950879011427458176016945)
            ·
              refine ⟨713159258570593632012709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 950879011427458176016945 713159258570593632012709)
              ·
                refine ⟨133717360981986306002383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 713159258570593632012709 133717360981986306002383)
                ·
                  rfl

theorem cell19_439448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_439448 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439448 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439448 prefixEnd_439448 := by exact prefixLift 439448
  have htrace : WordTrace (prefixWord ++ tailWord_439448) baseStart_439448 baseEnd_439448 := by
    simpa [prefixWord, tailWord_439448, baseEnd_439448] using wordTrace_append hprefix tailTrace_439448
  have hstable : (prefixWord ++ tailWord_439448).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439448).length < 2 ^ (prefixWord ++ tailWord_439448).sum := by decide
  have hdescent : baseEnd_439448 < baseStart_439448 := by decide
  rcases family_descends (prefixWord ++ tailWord_439448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439488 : List Nat := [2, 1, 1, 2, 6, 7]
def baseStart_439488 : Nat := 118140960795 + 439488 * 2 ^ 59
def prefixEnd_439488 : Nat := 4983230072969 + 3 ^ 40 * 439488 * 2
def baseEnd_439488 : Nat := 14858836930586451679265

theorem tailTrace_439488 : CollatzResearch.WordTrace tailWord_439488 prefixEnd_439488 14858836930586451679265 := by
  unfold tailWord_439488
  simp only [CollatzResearch.WordTrace]
  refine ⟨8014722115908754709895559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10686296154545006279860745 8014722115908754709895559)
  ·
    refine ⟨12022083173863132064843339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8014722115908754709895559 12022083173863132064843339)
    ·
      refine ⟨18033124760794698097265009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12022083173863132064843339 18033124760794698097265009)
      ·
        refine ⟨13524843570596023572948757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18033124760794698097265009 13524843570596023572948757)
        ·
          refine ⟨633977042371688604981973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13524843570596023572948757 633977042371688604981973)
          ·
            refine ⟨14858836930586451679265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 633977042371688604981973 14858836930586451679265)
            ·
              rfl

theorem cell19_439488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 7].length) (baseStart_439488 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439488 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439488 prefixEnd_439488 := by exact prefixLift 439488
  have htrace : WordTrace (prefixWord ++ tailWord_439488) baseStart_439488 baseEnd_439488 := by
    simpa [prefixWord, tailWord_439488, baseEnd_439488] using wordTrace_append hprefix tailTrace_439488
  have hstable : (prefixWord ++ tailWord_439488).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439488).length < 2 ^ (prefixWord ++ tailWord_439488).sum := by decide
  have hdescent : baseEnd_439488 < baseStart_439488 := by decide
  rcases family_descends (prefixWord ++ tailWord_439488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439581 : List Nat := [1, 4, 2, 3, 1, 2, 1, 5]
def baseStart_439581 : Nat := 118140960795 + 439581 * 2 ^ 59
def prefixEnd_439581 : Nat := 4983230072969 + 3 ^ 40 * 439581 * 2
def baseEnd_439581 : Nat := 133757830864681405046465

theorem tailTrace_439581 : CollatzResearch.WordTrace tailWord_439581 prefixEnd_439581 133757830864681405046465 := by
  unfold tailWord_439581
  simp only [CollatzResearch.WordTrace]
  refine ⟨16032836220480586302926597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10688557480320390868617731 16032836220480586302926597)
  ·
    refine ⟨3006156791340109931798737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16032836220480586302926597 3006156791340109931798737)
    ·
      refine ⟨2254617593505082448849053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3006156791340109931798737 2254617593505082448849053)
      ·
        refine ⟨845481597564405918318395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2254617593505082448849053 845481597564405918318395)
        ·
          refine ⟨1268222396346608877477593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845481597564405918318395 1268222396346608877477593)
          ·
            refine ⟨951166797259956658108195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1268222396346608877477593 951166797259956658108195)
            ·
              refine ⟨1426750195889934987162293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 951166797259956658108195 1426750195889934987162293)
              ·
                refine ⟨133757830864681405046465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1426750195889934987162293 133757830864681405046465)
                ·
                  rfl

theorem cell19_439581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_439581 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439581 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439581 prefixEnd_439581 := by exact prefixLift 439581
  have htrace : WordTrace (prefixWord ++ tailWord_439581) baseStart_439581 baseEnd_439581 := by
    simpa [prefixWord, tailWord_439581, baseEnd_439581] using wordTrace_append hprefix tailTrace_439581
  have hstable : (prefixWord ++ tailWord_439581).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439581).length < 2 ^ (prefixWord ++ tailWord_439581).sum := by decide
  have hdescent : baseEnd_439581 < baseStart_439581 := by decide
  rcases family_descends (prefixWord ++ tailWord_439581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439602 : List Nat := [3, 2, 1, 1, 4, 1, 7]
def baseStart_439602 : Nat := 118140960795 + 439602 * 2 ^ 59
def prefixEnd_439602 : Nat := 4983230072969 + 3 ^ 40 * 439602 * 2
def baseEnd_439602 : Nat := 44588073615386526193247

theorem tailTrace_439602 : CollatzResearch.WordTrace tailWord_439602 prefixEnd_439602 44588073615386526193247 := by
  unfold tailWord_439602
  simp only [CollatzResearch.WordTrace]
  refine ⟨4008400538351126722360265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10689068102269671259627373 4008400538351126722360265)
  ·
    refine ⟨3006300403763345041770199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4008400538351126722360265 3006300403763345041770199)
    ·
      refine ⟨4509450605645017562655299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3006300403763345041770199 4509450605645017562655299)
      ·
        refine ⟨6764175908467526343982949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4509450605645017562655299 6764175908467526343982949)
        ·
          refine ⟨1268282982837661189496803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6764175908467526343982949 1268282982837661189496803)
          ·
            refine ⟨1902424474256491784245205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268282982837661189496803 1902424474256491784245205)
            ·
              refine ⟨44588073615386526193247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1902424474256491784245205 44588073615386526193247)
              ·
                rfl

theorem cell19_439602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 7].length) (baseStart_439602 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439602 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439602 prefixEnd_439602 := by exact prefixLift 439602
  have htrace : WordTrace (prefixWord ++ tailWord_439602) baseStart_439602 baseEnd_439602 := by
    simpa [prefixWord, tailWord_439602, baseEnd_439602] using wordTrace_append hprefix tailTrace_439602
  have hstable : (prefixWord ++ tailWord_439602).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439602).length < 2 ^ (prefixWord ++ tailWord_439602).sum := by decide
  have hdescent : baseEnd_439602 < baseStart_439602 := by decide
  rcases family_descends (prefixWord ++ tailWord_439602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439746 : List Nat := [3, 5, 2, 1, 1, 1, 1, 5]
def baseStart_439746 : Nat := 118140960795 + 439746 * 2 ^ 59
def prefixEnd_439746 : Nat := 4983230072969 + 3 ^ 40 * 439746 * 2
def baseEnd_439746 : Nat := 133808037862009911379349

theorem tailTrace_439746 : CollatzResearch.WordTrace tailWord_439746 prefixEnd_439746 133808037862009911379349 := by
  unfold tailWord_439746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4009713566220704870670773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10692569509921879655122061 4009713566220704870670773)
  ·
    refine ⟨375910646833191081625385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4009713566220704870670773 375910646833191081625385)
    ·
      refine ⟨281932985124893311219039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375910646833191081625385 281932985124893311219039)
      ·
        refine ⟨422899477687339966828559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281932985124893311219039 422899477687339966828559)
        ·
          refine ⟨634349216531009950242839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422899477687339966828559 634349216531009950242839)
          ·
            refine ⟨951523824796514925364259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634349216531009950242839 951523824796514925364259)
            ·
              refine ⟨1427285737194772388046389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 951523824796514925364259 1427285737194772388046389)
              ·
                refine ⟨133808037862009911379349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1427285737194772388046389 133808037862009911379349)
                ·
                  rfl

theorem cell19_439746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_439746 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439746 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439746 prefixEnd_439746 := by exact prefixLift 439746
  have htrace : WordTrace (prefixWord ++ tailWord_439746) baseStart_439746 baseEnd_439746 := by
    simpa [prefixWord, tailWord_439746, baseEnd_439746] using wordTrace_append hprefix tailTrace_439746
  have hstable : (prefixWord ++ tailWord_439746).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439746).length < 2 ^ (prefixWord ++ tailWord_439746).sum := by decide
  have hdescent : baseEnd_439746 < baseStart_439746 := by decide
  rcases family_descends (prefixWord ++ tailWord_439746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439754 : List Nat := [3, 1, 2, 1, 2, 4, 1, 5]
def baseStart_439754 : Nat := 118140960795 + 439754 * 2 ^ 59
def prefixEnd_439754 : Nat := 4983230072969 + 3 ^ 40 * 439754 * 2
def baseEnd_439754 : Nat := 133810472140668263201549

theorem tailTrace_439754 : CollatzResearch.WordTrace tailWord_439754 prefixEnd_439754 133810472140668263201549 := by
  unfold tailWord_439754
  simp only [CollatzResearch.WordTrace]
  refine ⟨4009786512213459212243579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10692764032569224565982877 4009786512213459212243579)
  ·
    refine ⟨6014679768320188818365369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4009786512213459212243579 6014679768320188818365369)
    ·
      refine ⟨4511009826240141613774027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6014679768320188818365369 4511009826240141613774027)
      ·
        refine ⟨6766514739360212420661041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4511009826240141613774027 6766514739360212420661041)
        ·
          refine ⟨5074886054520159315495781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6766514739360212420661041 5074886054520159315495781)
          ·
            refine ⟨951541135222529871655459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5074886054520159315495781 951541135222529871655459)
            ·
              refine ⟨1427311702833794807483189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 951541135222529871655459 1427311702833794807483189)
              ·
                refine ⟨133810472140668263201549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1427311702833794807483189 133810472140668263201549)
                ·
                  rfl

theorem cell19_439754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_439754 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439754 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439754 prefixEnd_439754 := by exact prefixLift 439754
  have htrace : WordTrace (prefixWord ++ tailWord_439754) baseStart_439754 baseEnd_439754 := by
    simpa [prefixWord, tailWord_439754, baseEnd_439754] using wordTrace_append hprefix tailTrace_439754
  have hstable : (prefixWord ++ tailWord_439754).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439754).length < 2 ^ (prefixWord ++ tailWord_439754).sum := by decide
  have hdescent : baseEnd_439754 < baseStart_439754 := by decide
  rcases family_descends (prefixWord ++ tailWord_439754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439773 : List Nat := [1, 4, 3, 1, 1, 2, 7]
def baseStart_439773 : Nat := 118140960795 + 439773 * 2 ^ 59
def prefixEnd_439773 : Nat := 4983230072969 + 3 ^ 40 * 439773 * 2
def baseEnd_439773 : Nat := 44605417850827282926425

theorem tailTrace_439773 : CollatzResearch.WordTrace tailWord_439773 prefixEnd_439773 44605417850827282926425 := by
  unfold tailWord_439773
  simp only [CollatzResearch.WordTrace]
  refine ⟨16039839035785003093915973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10693226023856668729277315 16039839035785003093915973)
  ·
    refine ⟨3007469819209688080109245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16039839035785003093915973 3007469819209688080109245)
    ·
      refine ⟨1127801182203633030040967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3007469819209688080109245 1127801182203633030040967)
      ·
        refine ⟨1691701773305449545061451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1127801182203633030040967 1691701773305449545061451)
        ·
          refine ⟨2537552659958174317592177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1691701773305449545061451 2537552659958174317592177)
          ·
            refine ⟨1903164494968630738194133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2537552659958174317592177 1903164494968630738194133)
            ·
              refine ⟨44605417850827282926425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1903164494968630738194133 44605417850827282926425)
              ·
                rfl

theorem cell19_439773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 7].length) (baseStart_439773 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439773 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439773 prefixEnd_439773 := by exact prefixLift 439773
  have htrace : WordTrace (prefixWord ++ tailWord_439773) baseStart_439773 baseEnd_439773 := by
    simpa [prefixWord, tailWord_439773, baseEnd_439773] using wordTrace_append hprefix tailTrace_439773
  have hstable : (prefixWord ++ tailWord_439773).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439773).length < 2 ^ (prefixWord ++ tailWord_439773).sum := by decide
  have hdescent : baseEnd_439773 < baseStart_439773 := by decide
  rcases family_descends (prefixWord ++ tailWord_439773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439792 : List Nat := [2, 1, 1, 1, 3, 5, 2, 4]
def baseStart_439792 : Nat := 118140960795 + 439792 * 2 ^ 59
def prefixEnd_439792 : Nat := 4983230072969 + 3 ^ 40 * 439792 * 2
def baseEnd_439792 : Nat := 133822034964295434357001

theorem tailTrace_439792 : CollatzResearch.WordTrace tailWord_439792 prefixEnd_439792 133822034964295434357001 := by
  unfold tailWord_439792
  simp only [CollatzResearch.WordTrace]
  refine ⟨8020266011358084669428815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10693688015144112892571753 8020266011358084669428815)
  ·
    refine ⟨12030399017037127004143223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8020266011358084669428815 12030399017037127004143223)
    ·
      refine ⟨18045598525555690506214835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12030399017037127004143223 18045598525555690506214835)
      ·
        refine ⟨27068397788333535759322253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18045598525555690506214835 27068397788333535759322253)
        ·
          refine ⟨10150649170625075909745845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27068397788333535759322253 10150649170625075909745845)
          ·
            refine ⟨951623359746100866538673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10150649170625075909745845 951623359746100866538673)
            ·
              refine ⟨713717519809575649904005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951623359746100866538673 713717519809575649904005)
              ·
                refine ⟨133822034964295434357001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 713717519809575649904005 133822034964295434357001)
                ·
                  rfl

theorem cell19_439792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_439792 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439792 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439792 prefixEnd_439792 := by exact prefixLift 439792
  have htrace : WordTrace (prefixWord ++ tailWord_439792) baseStart_439792 baseEnd_439792 := by
    simpa [prefixWord, tailWord_439792, baseEnd_439792] using wordTrace_append hprefix tailTrace_439792
  have hstable : (prefixWord ++ tailWord_439792).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439792).length < 2 ^ (prefixWord ++ tailWord_439792).sum := by decide
  have hdescent : baseEnd_439792 < baseStart_439792 := by decide
  rcases family_descends (prefixWord ++ tailWord_439792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439828 : List Nat := [2, 4, 3, 1, 2, 7]
def baseStart_439828 : Nat := 118140960795 + 439828 * 2 ^ 59
def prefixEnd_439828 : Nat := 4983230072969 + 3 ^ 40 * 439828 * 2
def baseEnd_439828 : Nat := 14870332135362001950767

theorem tailTrace_439828 : CollatzResearch.WordTrace tailWord_439828 prefixEnd_439828 14870332135362001950767 := by
  unfold tailWord_439828
  simp only [CollatzResearch.WordTrace]
  refine ⟨8020922525292873743584069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10694563367057164991445425 8020922525292873743584069)
  ·
    refine ⟨1503922973492413826922013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8020922525292873743584069 1503922973492413826922013)
    ·
      refine ⟨563971115059655185095755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1503922973492413826922013 563971115059655185095755)
      ·
        refine ⟨845956672589482777643633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563971115059655185095755 845956672589482777643633)
        ·
          refine ⟨634467504442112083232725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 845956672589482777643633 634467504442112083232725)
          ·
            refine ⟨14870332135362001950767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 634467504442112083232725 14870332135362001950767)
            ·
              rfl

theorem cell19_439828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 7].length) (baseStart_439828 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439828 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439828 prefixEnd_439828 := by exact prefixLift 439828
  have htrace : WordTrace (prefixWord ++ tailWord_439828) baseStart_439828 baseEnd_439828 := by
    simpa [prefixWord, tailWord_439828, baseEnd_439828] using wordTrace_append hprefix tailTrace_439828
  have hstable : (prefixWord ++ tailWord_439828).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439828).length < 2 ^ (prefixWord ++ tailWord_439828).sum := by decide
  have hdescent : baseEnd_439828 < baseStart_439828 := by decide
  rcases family_descends (prefixWord ++ tailWord_439828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439832 : List Nat := [2, 1, 2, 3, 11]
def baseStart_439832 : Nat := 118140960795 + 439832 * 2 ^ 59
def prefixEnd_439832 : Nat := 4983230072969 + 3 ^ 40 * 439832 * 2
def baseEnd_439832 : Nat := 4956822457688414572889

theorem tailTrace_439832 : CollatzResearch.WordTrace tailWord_439832 prefixEnd_439832 4956822457688414572889 := by
  unfold tailWord_439832
  simp only [CollatzResearch.WordTrace]
  refine ⟨8020995471285628085156875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10694660628380837446875833 8020995471285628085156875)
  ·
    refine ⟨12031493206928442127735313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8020995471285628085156875 12031493206928442127735313)
    ·
      refine ⟨9023619905196331595801485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12031493206928442127735313 9023619905196331595801485)
      ·
        refine ⟨3383857464448624348425557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9023619905196331595801485 3383857464448624348425557)
        ·
          refine ⟨4956822457688414572889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3383857464448624348425557 4956822457688414572889)
          ·
            rfl

theorem cell19_439832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 11].length) (baseStart_439832 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439832 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439832 prefixEnd_439832 := by exact prefixLift 439832
  have htrace : WordTrace (prefixWord ++ tailWord_439832) baseStart_439832 baseEnd_439832 := by
    simpa [prefixWord, tailWord_439832, baseEnd_439832] using wordTrace_append hprefix tailTrace_439832
  have hstable : (prefixWord ++ tailWord_439832).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439832).length < 2 ^ (prefixWord ++ tailWord_439832).sum := by decide
  have hdescent : baseEnd_439832 < baseStart_439832 := by decide
  rcases family_descends (prefixWord ++ tailWord_439832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439885 : List Nat := [1, 6, 1, 1, 3, 1, 6]
def baseStart_439885 : Nat := 118140960795 + 439885 * 2 ^ 59
def prefixEnd_439885 : Nat := 4983230072969 + 3 ^ 40 * 439885 * 2
def baseEnd_439885 : Nat := 44616777817899591430027

theorem tailTrace_439885 : CollatzResearch.WordTrace tailWord_439885 prefixEnd_439885 44616777817899591430027 := by
  unfold tailWord_439885
  simp only [CollatzResearch.WordTrace]
  refine ⟨16043924011379246221993109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10695949340919497481328739 16043924011379246221993109)
  ·
    refine ⟨752058938033402166655927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16043924011379246221993109 752058938033402166655927)
    ·
      refine ⟨1128088407050103249983891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 752058938033402166655927 1128088407050103249983891)
      ·
        refine ⟨1692132610575154874975837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1128088407050103249983891 1692132610575154874975837)
        ·
          refine ⟨634549728965683078115939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1692132610575154874975837 634549728965683078115939)
          ·
            refine ⟨951824593448524617173909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634549728965683078115939 951824593448524617173909)
            ·
              refine ⟨44616777817899591430027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 951824593448524617173909 44616777817899591430027)
              ·
                rfl

theorem cell19_439885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 6].length) (baseStart_439885 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439885 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439885 prefixEnd_439885 := by exact prefixLift 439885
  have htrace : WordTrace (prefixWord ++ tailWord_439885) baseStart_439885 baseEnd_439885 := by
    simpa [prefixWord, tailWord_439885, baseEnd_439885] using wordTrace_append hprefix tailTrace_439885
  have hstable : (prefixWord ++ tailWord_439885).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439885).length < 2 ^ (prefixWord ++ tailWord_439885).sum := by decide
  have hdescent : baseEnd_439885 < baseStart_439885 := by decide
  rcases family_descends (prefixWord ++ tailWord_439885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439889 : List Nat := [1, 2, 2, 1, 3, 2, 8]
def baseStart_439889 : Nat := 118140960795 + 439889 * 2 ^ 59
def prefixEnd_439889 : Nat := 4983230072969 + 3 ^ 40 * 439889 * 2
def baseEnd_439889 : Nat := 44617183531009316733727

theorem tailTrace_439889 : CollatzResearch.WordTrace tailWord_439889 prefixEnd_439889 44617183531009316733727 := by
  unfold tailWord_439889
  simp only [CollatzResearch.WordTrace]
  refine ⟨16044069903364754905138721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10696046602243169936759147 16044069903364754905138721)
  ·
    refine ⟨12033052427523566178854041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16044069903364754905138721 12033052427523566178854041)
    ·
      refine ⟨9024789320642674634140531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12033052427523566178854041 9024789320642674634140531)
      ·
        refine ⟨13537183980964011951210797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9024789320642674634140531 13537183980964011951210797)
        ·
          refine ⟨5076443992861504481704049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13537183980964011951210797 5076443992861504481704049)
          ·
            refine ⟨3807332994646128361278037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5076443992861504481704049 3807332994646128361278037)
            ·
              refine ⟨44617183531009316733727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3807332994646128361278037 44617183531009316733727)
              ·
                rfl

theorem cell19_439889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 8].length) (baseStart_439889 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439889 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439889 prefixEnd_439889 := by exact prefixLift 439889
  have htrace : WordTrace (prefixWord ++ tailWord_439889) baseStart_439889 baseEnd_439889 := by
    simpa [prefixWord, tailWord_439889, baseEnd_439889] using wordTrace_append hprefix tailTrace_439889
  have hstable : (prefixWord ++ tailWord_439889).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439889).length < 2 ^ (prefixWord ++ tailWord_439889).sum := by decide
  have hdescent : baseEnd_439889 < baseStart_439889 := by decide
  rcases family_descends (prefixWord ++ tailWord_439889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_439984 : List Nat := [2, 1, 1, 1, 2, 1, 6, 5]
def baseStart_439984 : Nat := 118140960795 + 439984 * 2 ^ 59
def prefixEnd_439984 : Nat := 4983230072969 + 3 ^ 40 * 439984 * 2
def baseEnd_439984 : Nat := 133880457652095878089811

theorem tailTrace_439984 : CollatzResearch.WordTrace tailWord_439984 prefixEnd_439984 133880457652095878089811 := by
  unfold tailWord_439984
  simp only [CollatzResearch.WordTrace]
  refine ⟨8023767419010293064923503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10698356558680390753231337 8023767419010293064923503)
  ·
    refine ⟨12035651128515439597385255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8023767419010293064923503 12035651128515439597385255)
    ·
      refine ⟨18053476692773159396077883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12035651128515439597385255 18053476692773159396077883)
      ·
        refine ⟨27080215039159739094116825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18053476692773159396077883 27080215039159739094116825)
        ·
          refine ⟨20310161279369804320587619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27080215039159739094116825 20310161279369804320587619)
          ·
            refine ⟨30465241919054706480881429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20310161279369804320587619 30465241919054706480881429)
            ·
              refine ⟨1428058214955689366291317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30465241919054706480881429 1428058214955689366291317)
              ·
                refine ⟨133880457652095878089811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1428058214955689366291317 133880457652095878089811)
                ·
                  rfl

theorem cell19_439984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_439984 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_439984 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_439984 prefixEnd_439984 := by exact prefixLift 439984
  have htrace : WordTrace (prefixWord ++ tailWord_439984) baseStart_439984 baseEnd_439984 := by
    simpa [prefixWord, tailWord_439984, baseEnd_439984] using wordTrace_append hprefix tailTrace_439984
  have hstable : (prefixWord ++ tailWord_439984).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_439984).length < 2 ^ (prefixWord ++ tailWord_439984).sum := by decide
  have hdescent : baseEnd_439984 < baseStart_439984 := by decide
  rcases family_descends (prefixWord ++ tailWord_439984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440018 : List Nat := [3, 2, 2, 2, 2, 3, 1, 4]
def baseStart_440018 : Nat := 118140960795 + 440018 * 2 ^ 59
def prefixEnd_440018 : Nat := 4983230072969 + 3 ^ 40 * 440018 * 2
def baseEnd_440018 : Nat := 133890803336393873334163

theorem tailTrace_440018 : CollatzResearch.WordTrace tailWord_440018 prefixEnd_440018 133890803336393873334163 := by
  unfold tailWord_440018
  simp only [CollatzResearch.WordTrace]
  refine ⟨4012193729974352484146177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10699183279931606624389805 4012193729974352484146177)
  ·
    refine ⟨3009145297480764363109633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4012193729974352484146177 3009145297480764363109633)
    ·
      refine ⟨2256858973110573272332225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3009145297480764363109633 2256858973110573272332225)
      ·
        refine ⟨1692644229832929954249169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2256858973110573272332225 1692644229832929954249169)
        ·
          refine ⟨1269483172374697465686877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1692644229832929954249169 1269483172374697465686877)
          ·
            refine ⟨476056189640511549632579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1269483172374697465686877 476056189640511549632579)
            ·
              refine ⟨714084284460767324448869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476056189640511549632579 714084284460767324448869)
              ·
                refine ⟨133890803336393873334163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 714084284460767324448869 133890803336393873334163)
                ·
                  rfl

theorem cell19_440018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_440018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440018 prefixEnd_440018 := by exact prefixLift 440018
  have htrace : WordTrace (prefixWord ++ tailWord_440018) baseStart_440018 baseEnd_440018 := by
    simpa [prefixWord, tailWord_440018, baseEnd_440018] using wordTrace_append hprefix tailTrace_440018
  have hstable : (prefixWord ++ tailWord_440018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440018).length < 2 ^ (prefixWord ++ tailWord_440018).sum := by decide
  have hdescent : baseEnd_440018 < baseStart_440018 := by decide
  rcases family_descends (prefixWord ++ tailWord_440018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440060 : List Nat := [2, 2, 2, 1, 3, 1, 8]
def baseStart_440060 : Nat := 118140960795 + 440060 * 2 ^ 59
def prefixEnd_440060 : Nat := 4983230072969 + 3 ^ 40 * 440060 * 2
def baseEnd_440060 : Nat := 44634527766450073466905

theorem tailTrace_440060 : CollatzResearch.WordTrace tailWord_440060 prefixEnd_440060 44634527766450073466905 := by
  unfold tailWord_440060
  simp only [CollatzResearch.WordTrace]
  refine ⟨8025153392872625554806817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10700204523830167406409089 8025153392872625554806817)
  ·
    refine ⟨6018865044654469166105113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8025153392872625554806817 6018865044654469166105113)
    ·
      refine ⟨4514148783490851874578835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6018865044654469166105113 4514148783490851874578835)
      ·
        refine ⟨6771223175236277811868253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4514148783490851874578835 6771223175236277811868253)
        ·
          refine ⟨2539208690713604179450595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6771223175236277811868253 2539208690713604179450595)
          ·
            refine ⟨3808813036070406269175893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2539208690713604179450595 3808813036070406269175893)
            ·
              refine ⟨44634527766450073466905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3808813036070406269175893 44634527766450073466905)
              ·
                rfl

theorem cell19_440060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 8].length) (baseStart_440060 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440060 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440060 prefixEnd_440060 := by exact prefixLift 440060
  have htrace : WordTrace (prefixWord ++ tailWord_440060) baseStart_440060 baseEnd_440060 := by
    simpa [prefixWord, tailWord_440060, baseEnd_440060] using wordTrace_append hprefix tailTrace_440060
  have hstable : (prefixWord ++ tailWord_440060).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440060).length < 2 ^ (prefixWord ++ tailWord_440060).sum := by decide
  have hdescent : baseEnd_440060 < baseStart_440060 := by decide
  rcases family_descends (prefixWord ++ tailWord_440060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440115 : List Nat := [1, 1, 1, 2, 7, 2, 5]
def baseStart_440115 : Nat := 118140960795 + 440115 * 2 ^ 59
def prefixEnd_440115 : Nat := 4983230072969 + 3 ^ 40 * 440115 * 2
def baseEnd_440115 : Nat := 44640106321708796392781

theorem tailTrace_440115 : CollatzResearch.WordTrace tailWord_440115 prefixEnd_440115 44640106321708796392781 := by
  unfold tailWord_440115
  simp only [CollatzResearch.WordTrace]
  refine ⟨16052312800545995502865799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10701541867030663668577199 16052312800545995502865799)
  ·
    refine ⟨24078469200818993254298699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16052312800545995502865799 24078469200818993254298699)
    ·
      refine ⟨36117703801228489881448049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24078469200818993254298699 36117703801228489881448049)
      ·
        refine ⟨27088277850921367411086037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36117703801228489881448049 27088277850921367411086037)
        ·
          refine ⟨634881512130969548697329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 27088277850921367411086037 634881512130969548697329)
          ·
            refine ⟨476161134098227161522997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 634881512130969548697329 476161134098227161522997)
            ·
              refine ⟨44640106321708796392781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 476161134098227161522997 44640106321708796392781)
              ·
                rfl

theorem cell19_440115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 5].length) (baseStart_440115 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440115 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440115 prefixEnd_440115 := by exact prefixLift 440115
  have htrace : WordTrace (prefixWord ++ tailWord_440115) baseStart_440115 baseEnd_440115 := by
    simpa [prefixWord, tailWord_440115, baseEnd_440115] using wordTrace_append hprefix tailTrace_440115
  have hstable : (prefixWord ++ tailWord_440115).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440115).length < 2 ^ (prefixWord ++ tailWord_440115).sum := by decide
  have hdescent : baseEnd_440115 < baseStart_440115 := by decide
  rcases family_descends (prefixWord ++ tailWord_440115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440136 : List Nat := [2, 1, 3, 1, 1, 4, 1, 6]
def baseStart_440136 : Nat := 118140960795 + 440136 * 2 ^ 59
def prefixEnd_440136 : Nat := 4983230072969 + 3 ^ 40 * 440136 * 2
def baseEnd_440136 : Nat := 133926708946604562711619

theorem tailTrace_440136 : CollatzResearch.WordTrace tailWord_440136 prefixEnd_440136 133926708946604562711619 := by
  unfold tailWord_440136
  simp only [CollatzResearch.WordTrace]
  refine ⟨8026539366734958044690131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10702052488979944059586841 8026539366734958044690131)
  ·
    refine ⟨12039809050102437067035197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8026539366734958044690131 12039809050102437067035197)
    ·
      refine ⟨4514928393788413900138199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12039809050102437067035197 4514928393788413900138199)
      ·
        refine ⟨6772392590682620850207299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4514928393788413900138199 6772392590682620850207299)
        ·
          refine ⟨10158588886023931275310949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6772392590682620850207299 10158588886023931275310949)
          ·
            refine ⟨1904735416129487114120803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10158588886023931275310949 1904735416129487114120803)
            ·
              refine ⟨2857103124194230671181205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1904735416129487114120803 2857103124194230671181205)
              ·
                refine ⟨133926708946604562711619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2857103124194230671181205 133926708946604562711619)
                ·
                  rfl

theorem cell19_440136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_440136 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440136 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440136 prefixEnd_440136 := by exact prefixLift 440136
  have htrace : WordTrace (prefixWord ++ tailWord_440136) baseStart_440136 baseEnd_440136 := by
    simpa [prefixWord, tailWord_440136, baseEnd_440136] using wordTrace_append hprefix tailTrace_440136
  have hstable : (prefixWord ++ tailWord_440136).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440136).length < 2 ^ (prefixWord ++ tailWord_440136).sum := by decide
  have hdescent : baseEnd_440136 < baseStart_440136 := by decide
  rcases family_descends (prefixWord ++ tailWord_440136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440170 : List Nat := [3, 1, 3, 4, 2, 6]
def baseStart_440170 : Nat := 118140960795 + 440170 * 2 ^ 59
def prefixEnd_440170 : Nat := 4983230072969 + 3 ^ 40 * 440170 * 2
def baseEnd_440170 : Nat := 14881894958989173106219

theorem tailTrace_440170 : CollatzResearch.WordTrace tailWord_440170 prefixEnd_440170 14881894958989173106219 := by
  unfold tailWord_440170
  simp only [CollatzResearch.WordTrace]
  refine ⟨4013579703836684974029491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10702879210231159930745309 4013579703836684974029491)
  ·
    refine ⟨6020369555755027461044237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4013579703836684974029491 6020369555755027461044237)
    ·
      refine ⟨2257638583408135297891589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6020369555755027461044237 2257638583408135297891589)
      ·
        refine ⟨423307234389025368354673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2257638583408135297891589 423307234389025368354673)
        ·
          refine ⟨317480425791769026266005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423307234389025368354673 317480425791769026266005)
          ·
            refine ⟨14881894958989173106219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 317480425791769026266005 14881894958989173106219)
            ·
              rfl

theorem cell19_440170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 6].length) (baseStart_440170 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440170 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440170 prefixEnd_440170 := by exact prefixLift 440170
  have htrace : WordTrace (prefixWord ++ tailWord_440170) baseStart_440170 baseEnd_440170 := by
    simpa [prefixWord, tailWord_440170, baseEnd_440170] using wordTrace_append hprefix tailTrace_440170
  have hstable : (prefixWord ++ tailWord_440170).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440170).length < 2 ^ (prefixWord ++ tailWord_440170).sum := by decide
  have hdescent : baseEnd_440170 < baseStart_440170 := by decide
  rcases family_descends (prefixWord ++ tailWord_440170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440206 : List Nat := [4, 1, 1, 5, 1, 1, 3, 3]
def baseStart_440206 : Nat := 118140960795 + 440206 * 2 ^ 59
def prefixEnd_440206 : Nat := 4983230072969 + 3 ^ 40 * 440206 * 2
def baseEnd_440206 : Nat := 133948008884865141155873

theorem tailTrace_440206 : CollatzResearch.WordTrace tailWord_440206 prefixEnd_440206 133948008884865141155873 := by
  unfold tailWord_440206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2006953980402039755553559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10703754562144212029618981 2006953980402039755553559)
  ·
    refine ⟨3010430970603059633330339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2006953980402039755553559 3010430970603059633330339)
    ·
      refine ⟨4515646455904589449995509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3010430970603059633330339 4515646455904589449995509)
      ·
        refine ⟨423341855241055260937079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4515646455904589449995509 423341855241055260937079)
        ·
          refine ⟨635012782861582891405619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423341855241055260937079 635012782861582891405619)
          ·
            refine ⟨952519174292374337108429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635012782861582891405619 952519174292374337108429)
            ·
              refine ⟨357194690359640376415661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 952519174292374337108429 357194690359640376415661)
              ·
                refine ⟨133948008884865141155873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357194690359640376415661 133948008884865141155873)
                ·
                  rfl

theorem cell19_440206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_440206 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440206 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440206 prefixEnd_440206 := by exact prefixLift 440206
  have htrace : WordTrace (prefixWord ++ tailWord_440206) baseStart_440206 baseEnd_440206 := by
    simpa [prefixWord, tailWord_440206, baseEnd_440206] using wordTrace_append hprefix tailTrace_440206
  have hstable : (prefixWord ++ tailWord_440206).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440206).length < 2 ^ (prefixWord ++ tailWord_440206).sum := by decide
  have hdescent : baseEnd_440206 < baseStart_440206 := by decide
  rcases family_descends (prefixWord ++ tailWord_440206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440305 : List Nat := [1, 2, 2, 2, 5, 1, 2, 4]
def baseStart_440305 : Nat := 118140960795 + 440305 * 2 ^ 59
def prefixEnd_440305 : Nat := 4983230072969 + 3 ^ 40 * 440305 * 2
def baseEnd_440305 : Nat := 133978133083262244955603

theorem tailTrace_440305 : CollatzResearch.WordTrace tailWord_440305 prefixEnd_440305 133978133083262244955603 := by
  unfold tailWord_440305
  simp only [CollatzResearch.WordTrace]
  refine ⟨16059242669857657952282369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10706161779905105301521579 16059242669857657952282369)
  ·
    refine ⟨12044432002393243464211777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16059242669857657952282369 12044432002393243464211777)
    ·
      refine ⟨9033324001794932598158833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12044432002393243464211777 9033324001794932598158833)
      ·
        refine ⟨6774993001346199448619125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9033324001794932598158833 6774993001346199448619125)
        ·
          refine ⟨635155593876206198308043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6774993001346199448619125 635155593876206198308043)
          ·
            refine ⟨952733390814309297462065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635155593876206198308043 952733390814309297462065)
            ·
              refine ⟨714550043110731973096549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 952733390814309297462065 714550043110731973096549)
              ·
                refine ⟨133978133083262244955603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 714550043110731973096549 133978133083262244955603)
                ·
                  rfl

theorem cell19_440305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 4].length) (baseStart_440305 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440305 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440305 prefixEnd_440305 := by exact prefixLift 440305
  have htrace : WordTrace (prefixWord ++ tailWord_440305) baseStart_440305 baseEnd_440305 := by
    simpa [prefixWord, tailWord_440305, baseEnd_440305] using wordTrace_append hprefix tailTrace_440305
  have hstable : (prefixWord ++ tailWord_440305).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440305).length < 2 ^ (prefixWord ++ tailWord_440305).sum := by decide
  have hdescent : baseEnd_440305 < baseStart_440305 := by decide
  rcases family_descends (prefixWord ++ tailWord_440305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440343 : List Nat := [1, 1, 3, 5, 3, 6]
def baseStart_440343 : Nat := 118140960795 + 440343 * 2 ^ 59
def prefixEnd_440343 : Nat := 4983230072969 + 3 ^ 40 * 440343 * 2
def baseEnd_440343 : Nat := 14887743989654379567895

theorem tailTrace_440343 : CollatzResearch.WordTrace tailWord_440343 prefixEnd_440343 14887743989654379567895 := by
  unfold tailWord_440343
  simp only [CollatzResearch.WordTrace]
  refine ⟨16060628643719990442165683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10707085762479993628110455 16060628643719990442165683)
  ·
    refine ⟨24090942965579985663248525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16060628643719990442165683 24090942965579985663248525)
    ·
      refine ⟨9034103612092494623718197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24090942965579985663248525 9034103612092494623718197)
      ·
        refine ⟨846947213633671370973581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9034103612092494623718197 846947213633671370973581)
        ·
          refine ⟨317605205112626764115093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 846947213633671370973581 317605205112626764115093)
          ·
            refine ⟨14887743989654379567895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 317605205112626764115093 14887743989654379567895)
            ·
              rfl

theorem cell19_440343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 6].length) (baseStart_440343 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440343 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440343 prefixEnd_440343 := by exact prefixLift 440343
  have htrace : WordTrace (prefixWord ++ tailWord_440343) baseStart_440343 baseEnd_440343 := by
    simpa [prefixWord, tailWord_440343, baseEnd_440343] using wordTrace_append hprefix tailTrace_440343
  have hstable : (prefixWord ++ tailWord_440343).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440343).length < 2 ^ (prefixWord ++ tailWord_440343).sum := by decide
  have hdescent : baseEnd_440343 < baseStart_440343 := by decide
  rcases family_descends (prefixWord ++ tailWord_440343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440362 : List Nat := [3, 1, 4, 1, 2, 1, 3, 4]
def baseStart_440362 : Nat := 118140960795 + 440362 * 2 ^ 59
def prefixEnd_440362 : Nat := 4983230072969 + 3 ^ 40 * 440362 * 2
def baseEnd_440362 : Nat := 133995477318703001688781

theorem tailTrace_440362 : CollatzResearch.WordTrace tailWord_440362 prefixEnd_440362 133995477318703001688781 := by
  unfold tailWord_440362
  simp only [CollatzResearch.WordTrace]
  refine ⟨4015330407662789171776835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10707547753767437791404893 4015330407662789171776835)
  ·
    refine ⟨6022995611494183757665253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4015330407662789171776835 6022995611494183757665253)
    ·
      refine ⟨1129311677155159454562235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6022995611494183757665253 1129311677155159454562235)
      ·
        refine ⟨1693967515732739181843353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129311677155159454562235 1693967515732739181843353)
        ·
          refine ⟨1270475636799554386382515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1693967515732739181843353 1270475636799554386382515)
          ·
            refine ⟨1905713455199331579573773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270475636799554386382515 1905713455199331579573773)
            ·
              refine ⟨714642545699749342340165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1905713455199331579573773 714642545699749342340165)
              ·
                refine ⟨133995477318703001688781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 714642545699749342340165 133995477318703001688781)
                ·
                  rfl

theorem cell19_440362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_440362 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440362 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440362 prefixEnd_440362 := by exact prefixLift 440362
  have htrace : WordTrace (prefixWord ++ tailWord_440362) baseStart_440362 baseEnd_440362 := by
    simpa [prefixWord, tailWord_440362, baseEnd_440362] using wordTrace_append hprefix tailTrace_440362
  have hstable : (prefixWord ++ tailWord_440362).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440362).length < 2 ^ (prefixWord ++ tailWord_440362).sum := by decide
  have hdescent : baseEnd_440362 < baseStart_440362 := by decide
  rcases family_descends (prefixWord ++ tailWord_440362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440381 : List Nat := [1, 4, 1, 3, 1, 1, 5, 3]
def baseStart_440381 : Nat := 118140960795 + 440381 * 2 ^ 59
def prefixEnd_440381 : Nat := 4983230072969 + 3 ^ 40 * 440381 * 2
def baseEnd_440381 : Nat := 134001258730516587266507

theorem tailTrace_440381 : CollatzResearch.WordTrace tailWord_440381 prefixEnd_440381 134001258730516587266507 := by
  unfold tailWord_440381
  simp only [CollatzResearch.WordTrace]
  refine ⟨16062014617582322932048997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10708009745054881954699331 16062014617582322932048997)
  ·
    refine ⟨3011627740796685549759187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16062014617582322932048997 3011627740796685549759187)
    ·
      refine ⟨4517441611195028324638781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3011627740796685549759187 4517441611195028324638781)
      ·
        refine ⟨1694040604198135621739543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4517441611195028324638781 1694040604198135621739543)
        ·
          refine ⟨2541060906297203432609315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1694040604198135621739543 2541060906297203432609315)
          ·
            refine ⟨3811591359445805148913973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2541060906297203432609315 3811591359445805148913973)
            ·
              refine ⟨357336689948044232710685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3811591359445805148913973 357336689948044232710685)
              ·
                refine ⟨134001258730516587266507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357336689948044232710685 134001258730516587266507)
                ·
                  rfl

theorem cell19_440381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 3].length) (baseStart_440381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440381 prefixEnd_440381 := by exact prefixLift 440381
  have htrace : WordTrace (prefixWord ++ tailWord_440381) baseStart_440381 baseEnd_440381 := by
    simpa [prefixWord, tailWord_440381, baseEnd_440381] using wordTrace_append hprefix tailTrace_440381
  have hstable : (prefixWord ++ tailWord_440381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440381).length < 2 ^ (prefixWord ++ tailWord_440381).sum := by decide
  have hdescent : baseEnd_440381 < baseStart_440381 := by decide
  rcases family_descends (prefixWord ++ tailWord_440381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440438 : List Nat := [5, 1, 1, 2, 1, 3, 1, 5]
def baseStart_440438 : Nat := 118140960795 + 440438 * 2 ^ 59
def prefixEnd_440438 : Nat := 4983230072969 + 3 ^ 40 * 440438 * 2
def baseEnd_440438 : Nat := 134018602965957343999685

theorem tailTrace_440438 : CollatzResearch.WordTrace tailWord_440438 prefixEnd_440438 134018602965957343999685 := by
  unfold tailWord_440438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1004005848648488854179623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10709395718917214444582645 1004005848648488854179623)
  ·
    refine ⟨1506008772972733281269435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1004005848648488854179623 1506008772972733281269435)
    ·
      refine ⟨2259013159459099921904153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1506008772972733281269435 2259013159459099921904153)
      ·
        refine ⟨1694259869594324941428115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2259013159459099921904153 1694259869594324941428115)
        ·
          refine ⟨2541389804391487412142173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1694259869594324941428115 2541389804391487412142173)
          ·
            refine ⟨953021176646807779553315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2541389804391487412142173 953021176646807779553315)
            ·
              refine ⟨1429531764970211669329973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953021176646807779553315 1429531764970211669329973)
              ·
                refine ⟨134018602965957343999685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1429531764970211669329973 134018602965957343999685)
                ·
                  rfl

theorem cell19_440438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_440438 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440438 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440438 prefixEnd_440438 := by exact prefixLift 440438
  have htrace : WordTrace (prefixWord ++ tailWord_440438) baseStart_440438 baseEnd_440438 := by
    simpa [prefixWord, tailWord_440438, baseEnd_440438] using wordTrace_append hprefix tailTrace_440438
  have hstable : (prefixWord ++ tailWord_440438).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440438).length < 2 ^ (prefixWord ++ tailWord_440438).sum := by decide
  have hdescent : baseEnd_440438 < baseStart_440438 := by decide
  rcases family_descends (prefixWord ++ tailWord_440438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440516 : List Nat := [2, 3, 3, 1, 2, 8]
def baseStart_440516 : Nat := 118140960795 + 440516 * 2 ^ 59
def prefixEnd_440516 : Nat := 4983230072969 + 3 ^ 40 * 440516 * 2
def baseEnd_440516 : Nat := 14893593020319586029571

theorem tailTrace_440516 : CollatzResearch.WordTrace tailWord_440516 prefixEnd_440516 14893593020319586029571 := by
  unfold tailWord_440516
  simp only [CollatzResearch.WordTrace]
  refine ⟨8033469236046620494106701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10711292314728827325475601 8033469236046620494106701)
  ·
    refine ⟨3012550963517482685290013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8033469236046620494106701 3012550963517482685290013)
    ·
      refine ⟨1129706611319056006983755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3012550963517482685290013 1129706611319056006983755)
      ·
        refine ⟨1694559916978584010475633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129706611319056006983755 1694559916978584010475633)
        ·
          refine ⟨1270919937733938007856725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1694559916978584010475633 1270919937733938007856725)
          ·
            refine ⟨14893593020319586029571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1270919937733938007856725 14893593020319586029571)
            ·
              rfl

theorem cell19_440516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 8].length) (baseStart_440516 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440516 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440516 prefixEnd_440516 := by exact prefixLift 440516
  have htrace : WordTrace (prefixWord ++ tailWord_440516) baseStart_440516 baseEnd_440516 := by
    simpa [prefixWord, tailWord_440516, baseEnd_440516] using wordTrace_append hprefix tailTrace_440516
  have hstable : (prefixWord ++ tailWord_440516).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440516).length < 2 ^ (prefixWord ++ tailWord_440516).sum := by decide
  have hdescent : baseEnd_440516 < baseStart_440516 := by decide
  rcases family_descends (prefixWord ++ tailWord_440516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440546 : List Nat := [3, 3, 4, 1, 1, 1, 3, 3]
def baseStart_440546 : Nat := 118140960795 + 440546 * 2 ^ 59
def prefixEnd_440546 : Nat := 4983230072969 + 3 ^ 40 * 440546 * 2
def baseEnd_440546 : Nat := 134051465727845093599391

theorem tailTrace_440546 : CollatzResearch.WordTrace tailWord_440546 prefixEnd_440546 134051465727845093599391 := by
  unfold tailWord_440546
  simp only [CollatzResearch.WordTrace]
  refine ⟨4017008165496139027951373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10712021774656370741203661 4017008165496139027951373)
  ·
    refine ⟨1506378062061052135481765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4017008165496139027951373 1506378062061052135481765)
    ·
      refine ⟨282445886636447275402831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1506378062061052135481765 282445886636447275402831)
      ·
        refine ⟨423668829954670913104247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282445886636447275402831 423668829954670913104247)
        ·
          refine ⟨635503244932006369656371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423668829954670913104247 635503244932006369656371)
          ·
            refine ⟨953254867398009554484557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635503244932006369656371 953254867398009554484557)
            ·
              refine ⟨357470575274253582931709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 953254867398009554484557 357470575274253582931709)
              ·
                refine ⟨134051465727845093599391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357470575274253582931709 134051465727845093599391)
                ·
                  rfl

theorem cell19_440546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_440546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440546 prefixEnd_440546 := by exact prefixLift 440546
  have htrace : WordTrace (prefixWord ++ tailWord_440546) baseStart_440546 baseEnd_440546 := by
    simpa [prefixWord, tailWord_440546, baseEnd_440546] using wordTrace_append hprefix tailTrace_440546
  have hstable : (prefixWord ++ tailWord_440546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440546).length < 2 ^ (prefixWord ++ tailWord_440546).sum := by decide
  have hdescent : baseEnd_440546 < baseStart_440546 := by decide
  rcases family_descends (prefixWord ++ tailWord_440546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440552 : List Nat := [2, 1, 4, 1, 2, 3, 3, 3]
def baseStart_440552 : Nat := 118140960795 + 440552 * 2 ^ 59
def prefixEnd_440552 : Nat := 4983230072969 + 3 ^ 40 * 440552 * 2
def baseEnd_440552 : Nat := 134053291436838857466041

theorem tailTrace_440552 : CollatzResearch.WordTrace tailWord_440552 prefixEnd_440552 134053291436838857466041 := by
  unfold tailWord_440552
  simp only [CollatzResearch.WordTrace]
  refine ⟨8034125749981409568261955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10712167666641879424349273 8034125749981409568261955)
  ·
    refine ⟨12051188624972114352392933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8034125749981409568261955 12051188624972114352392933)
    ·
      refine ⟨2259597867182271441073675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12051188624972114352392933 2259597867182271441073675)
      ·
        refine ⟨3389396800773407161610513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2259597867182271441073675 3389396800773407161610513)
        ·
          refine ⟨2542047600580055371207885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3389396800773407161610513 2542047600580055371207885)
          ·
            refine ⟨953267850217520764202957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2542047600580055371207885 953267850217520764202957)
            ·
              refine ⟨357475443831570286576109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 953267850217520764202957 357475443831570286576109)
              ·
                refine ⟨134053291436838857466041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357475443831570286576109 134053291436838857466041)
                ·
                  rfl

theorem cell19_440552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 3].length) (baseStart_440552 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440552 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440552 prefixEnd_440552 := by exact prefixLift 440552
  have htrace : WordTrace (prefixWord ++ tailWord_440552) baseStart_440552 baseEnd_440552 := by
    simpa [prefixWord, tailWord_440552, baseEnd_440552] using wordTrace_append hprefix tailTrace_440552
  have hstable : (prefixWord ++ tailWord_440552).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440552).length < 2 ^ (prefixWord ++ tailWord_440552).sum := by decide
  have hdescent : baseEnd_440552 < baseStart_440552 := by decide
  rcases family_descends (prefixWord ++ tailWord_440552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440575 : List Nat := [1, 1, 2, 2, 1, 4, 8]
def baseStart_440575 : Nat := 118140960795 + 440575 * 2 ^ 59
def prefixEnd_440575 : Nat := 4983230072969 + 3 ^ 40 * 440575 * 2
def baseEnd_440575 : Nat := 44686763329327206318289

theorem tailTrace_440575 : CollatzResearch.WordTrace tailWord_440575 prefixEnd_440575 44686763329327206318289 := by
  unfold tailWord_440575
  simp only [CollatzResearch.WordTrace]
  refine ⟨16069090378879494064611179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10712726919252996043074119 16069090378879494064611179)
  ·
    refine ⟨24103635568319241096916769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16069090378879494064611179 24103635568319241096916769)
    ·
      refine ⟨18077726676239430822687577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24103635568319241096916769 18077726676239430822687577)
      ·
        refine ⟨13558295007179573117015683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18077726676239430822687577 13558295007179573117015683)
        ·
          refine ⟨20337442510769359675523525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13558295007179573117015683 20337442510769359675523525)
          ·
            refine ⟨3813270470769254939160661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20337442510769359675523525 3813270470769254939160661)
            ·
              refine ⟨44686763329327206318289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3813270470769254939160661 44686763329327206318289)
              ·
                rfl

theorem cell19_440575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 8].length) (baseStart_440575 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440575 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440575 prefixEnd_440575 := by exact prefixLift 440575
  have htrace : WordTrace (prefixWord ++ tailWord_440575) baseStart_440575 baseEnd_440575 := by
    simpa [prefixWord, tailWord_440575, baseEnd_440575] using wordTrace_append hprefix tailTrace_440575
  have hstable : (prefixWord ++ tailWord_440575).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440575).length < 2 ^ (prefixWord ++ tailWord_440575).sum := by decide
  have hdescent : baseEnd_440575 < baseStart_440575 := by decide
  rcases family_descends (prefixWord ++ tailWord_440575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440605 : List Nat := [1, 4, 2, 3, 3, 1, 2, 3]
def baseStart_440605 : Nat := 118140960795 + 440605 * 2 ^ 59
def prefixEnd_440605 : Nat := 4983230072969 + 3 ^ 40 * 440605 * 2
def baseEnd_440605 : Nat := 134069418532950438288119

theorem tailTrace_440605 : CollatzResearch.WordTrace tailWord_440605 prefixEnd_440605 134069418532950438288119 := by
  unfold tailWord_440605
  simp only [CollatzResearch.WordTrace]
  refine ⟨16070184568770809188203269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10713456379180539458802179 16070184568770809188203269)
  ·
    refine ⟨3013159606644526722788113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16070184568770809188203269 3013159606644526722788113)
    ·
      refine ⟨2259869704983395042091085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3013159606644526722788113 2259869704983395042091085)
      ·
        refine ⟨847451139368773140784157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2259869704983395042091085 847451139368773140784157)
        ·
          refine ⟨317794177263289927794059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 847451139368773140784157 317794177263289927794059)
          ·
            refine ⟨476691265894934891691089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317794177263289927794059 476691265894934891691089)
            ·
              refine ⟨357518449421201168768317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476691265894934891691089 357518449421201168768317)
              ·
                refine ⟨134069418532950438288119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357518449421201168768317 134069418532950438288119)
                ·
                  rfl

theorem cell19_440605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 3].length) (baseStart_440605 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440605 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440605 prefixEnd_440605 := by exact prefixLift 440605
  have htrace : WordTrace (prefixWord ++ tailWord_440605) baseStart_440605 baseEnd_440605 := by
    simpa [prefixWord, tailWord_440605, baseEnd_440605] using wordTrace_append hprefix tailTrace_440605
  have hstable : (prefixWord ++ tailWord_440605).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440605).length < 2 ^ (prefixWord ++ tailWord_440605).sum := by decide
  have hdescent : baseEnd_440605 < baseStart_440605 := by decide
  rcases family_descends (prefixWord ++ tailWord_440605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440628 : List Nat := [2, 5, 1, 1, 1, 4, 5]
def baseStart_440628 : Nat := 118140960795 + 440628 * 2 ^ 59
def prefixEnd_440628 : Nat := 4983230072969 + 3 ^ 40 * 440628 * 2
def baseEnd_440628 : Nat := 44692139028031066592315

theorem tailTrace_440628 : CollatzResearch.WordTrace tailWord_440628 prefixEnd_440628 44692139028031066592315 := by
  unfold tailWord_440628
  simp only [CollatzResearch.WordTrace]
  refine ⟨8035511723843742058145269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10714015631791656077527025 8035511723843742058145269)
  ·
    refine ⟨753329224110350817951119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8035511723843742058145269 753329224110350817951119)
    ·
      refine ⟨1129993836165526226926679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 753329224110350817951119 1129993836165526226926679)
      ·
        refine ⟨1694990754248289340390019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129993836165526226926679 1694990754248289340390019)
        ·
          refine ⟨2542486131372434010585029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1694990754248289340390019 2542486131372434010585029)
          ·
            refine ⟨476716149632331376984693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2542486131372434010585029 476716149632331376984693)
            ·
              refine ⟨44692139028031066592315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 476716149632331376984693 44692139028031066592315)
              ·
                rfl

theorem cell19_440628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 5].length) (baseStart_440628 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440628 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440628 prefixEnd_440628 := by exact prefixLift 440628
  have htrace : WordTrace (prefixWord ++ tailWord_440628) baseStart_440628 baseEnd_440628 := by
    simpa [prefixWord, tailWord_440628, baseEnd_440628] using wordTrace_append hprefix tailTrace_440628
  have hstable : (prefixWord ++ tailWord_440628).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440628).length < 2 ^ (prefixWord ++ tailWord_440628).sum := by decide
  have hdescent : baseEnd_440628 < baseStart_440628 := by decide
  rcases family_descends (prefixWord ++ tailWord_440628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440632 : List Nat := [2, 1, 2, 1, 3, 1, 9]
def baseStart_440632 : Nat := 118140960795 + 440632 * 2 ^ 59
def prefixEnd_440632 : Nat := 4983230072969 + 3 ^ 40 * 440632 * 2
def baseEnd_440632 : Nat := 44692544741140791896015

theorem tailTrace_440632 : CollatzResearch.WordTrace tailWord_440632 prefixEnd_440632 44692544741140791896015 := by
  unfold tailWord_440632
  simp only [CollatzResearch.WordTrace]
  refine ⟨8035584669836496399718075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10714112893115328532957433 8035584669836496399718075)
  ·
    refine ⟨12053377004754744599577113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8035584669836496399718075 12053377004754744599577113)
    ·
      refine ⟨9040032753566058449682835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12053377004754744599577113 9040032753566058449682835)
      ·
        refine ⟨13560049130349087674524253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9040032753566058449682835 13560049130349087674524253)
        ·
          refine ⟨5085018423880907877946595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13560049130349087674524253 5085018423880907877946595)
          ·
            refine ⟨7627527635821361816919893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5085018423880907877946595 7627527635821361816919893)
            ·
              refine ⟨44692544741140791896015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7627527635821361816919893 44692544741140791896015)
              ·
                rfl

theorem cell19_440632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 9].length) (baseStart_440632 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440632 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440632 prefixEnd_440632 := by exact prefixLift 440632
  have htrace : WordTrace (prefixWord ++ tailWord_440632) baseStart_440632 baseEnd_440632 := by
    simpa [prefixWord, tailWord_440632, baseEnd_440632] using wordTrace_append hprefix tailTrace_440632
  have hstable : (prefixWord ++ tailWord_440632).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440632).length < 2 ^ (prefixWord ++ tailWord_440632).sum := by decide
  have hdescent : baseEnd_440632 < baseStart_440632 := by decide
  rcases family_descends (prefixWord ++ tailWord_440632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440727 : List Nat := [1, 1, 3, 3, 1, 1, 2, 7]
def baseStart_440727 : Nat := 118140960795 + 440727 * 2 ^ 59
def prefixEnd_440727 : Nat := 4983230072969 + 3 ^ 40 * 440727 * 2
def baseEnd_440727 : Nat := 134106541282490303576675

theorem tailTrace_440727 : CollatzResearch.WordTrace tailWord_440727 prefixEnd_440727 134106541282490303576675 := by
  unfold tailWord_440727
  simp only [CollatzResearch.WordTrace]
  refine ⟨16074634274328824024144435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10716422849552549349429623 16074634274328824024144435)
  ·
    refine ⟨24111951411493236036216653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16074634274328824024144435 24111951411493236036216653)
    ·
      refine ⟨9041981779309963513581245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24111951411493236036216653 9041981779309963513581245)
      ·
        refine ⟨3390743167241236317592967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9041981779309963513581245 3390743167241236317592967)
        ·
          refine ⟨5086114750861854476389451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3390743167241236317592967 5086114750861854476389451)
          ·
            refine ⟨7629172126292781714584177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5086114750861854476389451 7629172126292781714584177)
            ·
              refine ⟨5721879094719586285938133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7629172126292781714584177 5721879094719586285938133)
              ·
                refine ⟨134106541282490303576675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5721879094719586285938133 134106541282490303576675)
                ·
                  rfl

theorem cell19_440727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_440727 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440727 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440727 prefixEnd_440727 := by exact prefixLift 440727
  have htrace : WordTrace (prefixWord ++ tailWord_440727) baseStart_440727 baseEnd_440727 := by
    simpa [prefixWord, tailWord_440727, baseEnd_440727] using wordTrace_append hprefix tailTrace_440727
  have hstable : (prefixWord ++ tailWord_440727).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440727).length < 2 ^ (prefixWord ++ tailWord_440727).sum := by decide
  have hdescent : baseEnd_440727 < baseStart_440727 := by decide
  rcases family_descends (prefixWord ++ tailWord_440727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440818 : List Nat := [3, 2, 1, 4, 2, 1, 2, 4]
def baseStart_440818 : Nat := 118140960795 + 440818 * 2 ^ 59
def prefixEnd_440818 : Nat := 4983230072969 + 3 ^ 40 * 440818 * 2
def baseEnd_440818 : Nat := 134134231202229055554205

theorem tailTrace_440818 : CollatzResearch.WordTrace tailWord_440818 prefixEnd_440818 134134231202229055554205 := by
  unfold tailWord_440818
  simp only [CollatzResearch.WordTrace]
  refine ⟨4019488329249786641426777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10718635544666097710471405 4019488329249786641426777)
  ·
    refine ⟨3014616246937339981070083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4019488329249786641426777 3014616246937339981070083)
    ·
      refine ⟨4521924370406009971605125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3014616246937339981070083 4521924370406009971605125)
      ·
        refine ⟨847860819451126869675961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4521924370406009971605125 847860819451126869675961)
        ·
          refine ⟨635895614588345152256971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 847860819451126869675961 635895614588345152256971)
          ·
            refine ⟨953843421882517728385457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635895614588345152256971 953843421882517728385457)
            ·
              refine ⟨715382566411888296289093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 953843421882517728385457 715382566411888296289093)
              ·
                refine ⟨134134231202229055554205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 715382566411888296289093 134134231202229055554205)
                ·
                  rfl

theorem cell19_440818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_440818 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440818 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440818 prefixEnd_440818 := by exact prefixLift 440818
  have htrace : WordTrace (prefixWord ++ tailWord_440818) baseStart_440818 baseEnd_440818 := by
    simpa [prefixWord, tailWord_440818, baseEnd_440818] using wordTrace_append hprefix tailTrace_440818
  have hstable : (prefixWord ++ tailWord_440818).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440818).length < 2 ^ (prefixWord ++ tailWord_440818).sum := by decide
  have hdescent : baseEnd_440818 < baseStart_440818 := by decide
  rcases family_descends (prefixWord ++ tailWord_440818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440860 : List Nat := [2, 2, 3, 1, 2, 9]
def baseStart_440860 : Nat := 118140960795 + 440860 * 2 ^ 59
def prefixEnd_440860 : Nat := 4983230072969 + 3 ^ 40 * 440860 * 2
def baseEnd_440860 : Nat := 14905223462798378068973

theorem tailTrace_440860 : CollatzResearch.WordTrace tailWord_440860 prefixEnd_440860 14905223462798378068973 := by
  unfold tailWord_440860
  simp only [CollatzResearch.WordTrace]
  refine ⟨8039742591423493869368017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10719656788564658492490689 8039742591423493869368017)
  ·
    refine ⟨6029806943567620402026013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8039742591423493869368017 6029806943567620402026013)
    ·
      refine ⟨2261177603837857650759755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6029806943567620402026013 2261177603837857650759755)
      ·
        refine ⟨3391766405756786476139633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2261177603837857650759755 3391766405756786476139633)
        ·
          refine ⟨2543824804317589857104725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3391766405756786476139633 2543824804317589857104725)
          ·
            refine ⟨14905223462798378068973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2543824804317589857104725 14905223462798378068973)
            ·
              rfl

theorem cell19_440860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 9].length) (baseStart_440860 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440860 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440860 prefixEnd_440860 := by exact prefixLift 440860
  have htrace : WordTrace (prefixWord ++ tailWord_440860) baseStart_440860 baseEnd_440860 := by
    simpa [prefixWord, tailWord_440860, baseEnd_440860] using wordTrace_append hprefix tailTrace_440860
  have hstable : (prefixWord ++ tailWord_440860).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440860).length < 2 ^ (prefixWord ++ tailWord_440860).sum := by decide
  have hdescent : baseEnd_440860 < baseStart_440860 := by decide
  rcases family_descends (prefixWord ++ tailWord_440860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440871 : List Nat := [1, 1, 7, 2, 2, 1, 1, 4]
def baseStart_440871 : Nat := 118140960795 + 440871 * 2 ^ 59
def prefixEnd_440871 : Nat := 4983230072969 + 3 ^ 40 * 440871 * 2
def baseEnd_440871 : Nat := 134150358298340636376283

theorem tailTrace_440871 : CollatzResearch.WordTrace tailWord_440871 prefixEnd_440871 134150358298340636376283 := by
  unfold tailWord_440871
  simp only [CollatzResearch.WordTrace]
  refine ⟨16079886385807136617386467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10719924257204757744924311 16079886385807136617386467)
  ·
    refine ⟨24119829578710704926079701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16079886385807136617386467 24119829578710704926079701)
    ·
      refine ⟨565308505751032146704993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 24119829578710704926079701 565308505751032146704993)
      ·
        refine ⟨423981379313274110028745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 565308505751032146704993 423981379313274110028745)
        ·
          refine ⟨317986034484955582521559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423981379313274110028745 317986034484955582521559)
          ·
            refine ⟨476979051727433373782339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317986034484955582521559 476979051727433373782339)
            ·
              refine ⟨715468577591150060673509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476979051727433373782339 715468577591150060673509)
              ·
                refine ⟨134150358298340636376283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 715468577591150060673509 134150358298340636376283)
                ·
                  rfl

theorem cell19_440871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 4].length) (baseStart_440871 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440871 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440871 prefixEnd_440871 := by exact prefixLift 440871
  have htrace : WordTrace (prefixWord ++ tailWord_440871) baseStart_440871 baseEnd_440871 := by
    simpa [prefixWord, tailWord_440871, baseEnd_440871] using wordTrace_append hprefix tailTrace_440871
  have hstable : (prefixWord ++ tailWord_440871).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440871).length < 2 ^ (prefixWord ++ tailWord_440871).sum := by decide
  have hdescent : baseEnd_440871 < baseStart_440871 := by decide
  rcases family_descends (prefixWord ++ tailWord_440871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440949 : List Nat := [1, 3, 4, 2, 2, 2, 2, 3]
def baseStart_440949 : Nat := 118140960795 + 440949 * 2 ^ 59
def prefixEnd_440949 : Nat := 4983230072969 + 3 ^ 40 * 440949 * 2
def baseEnd_440949 : Nat := 134174092515259566642737

theorem tailTrace_440949 : CollatzResearch.WordTrace tailWord_440949 prefixEnd_440949 134174092515259566642737 := by
  unfold tailWord_440949
  simp only [CollatzResearch.WordTrace]
  refine ⟨16082731279524555938725901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10721820853016370625817267 16082731279524555938725901)
  ·
    refine ⟨6031024229821708477022213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16082731279524555938725901 6031024229821708477022213)
    ·
      refine ⟨1130817043091570339441665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6031024229821708477022213 1130817043091570339441665)
      ·
        refine ⟨848112782318677754581249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1130817043091570339441665 848112782318677754581249)
        ·
          refine ⟨636084586739008315935937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 848112782318677754581249 636084586739008315935937)
          ·
            refine ⟨477063440054256236951953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 636084586739008315935937 477063440054256236951953)
            ·
              refine ⟨357797580040692177713965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477063440054256236951953 357797580040692177713965)
              ·
                refine ⟨134174092515259566642737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357797580040692177713965 134174092515259566642737)
                ·
                  rfl

theorem cell19_440949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 3].length) (baseStart_440949 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440949 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440949 prefixEnd_440949 := by exact prefixLift 440949
  have htrace : WordTrace (prefixWord ++ tailWord_440949) baseStart_440949 baseEnd_440949 := by
    simpa [prefixWord, tailWord_440949, baseEnd_440949] using wordTrace_append hprefix tailTrace_440949
  have hstable : (prefixWord ++ tailWord_440949).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440949).length < 2 ^ (prefixWord ++ tailWord_440949).sum := by decide
  have hdescent : baseEnd_440949 < baseStart_440949 := by decide
  rcases family_descends (prefixWord ++ tailWord_440949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440953 : List Nat := [1, 2, 1, 3, 3, 2, 4, 3]
def baseStart_440953 : Nat := 118140960795 + 440953 * 2 ^ 59
def prefixEnd_440953 : Nat := 4983230072969 + 3 ^ 40 * 440953 * 2
def baseEnd_440953 : Nat := 134175309654588742553837

theorem tailTrace_440953 : CollatzResearch.WordTrace tailWord_440953 prefixEnd_440953 134175309654588742553837 := by
  unfold tailWord_440953
  simp only [CollatzResearch.WordTrace]
  refine ⟨16082877171510064621871513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10721918114340043081247675 16082877171510064621871513)
  ·
    refine ⟨12062157878632548466403635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16082877171510064621871513 12062157878632548466403635)
    ·
      refine ⟨18093236817948822699605453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12062157878632548466403635 18093236817948822699605453)
      ·
        refine ⟨6784963806730808512352045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18093236817948822699605453 6784963806730808512352045)
        ·
          refine ⟨2544361427524053192132017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6784963806730808512352045 2544361427524053192132017)
          ·
            refine ⟨1908271070643039894099013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2544361427524053192132017 1908271070643039894099013)
            ·
              refine ⟨357800825745569980143565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1908271070643039894099013 357800825745569980143565)
              ·
                refine ⟨134175309654588742553837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357800825745569980143565 134175309654588742553837)
                ·
                  rfl

theorem cell19_440953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 3].length) (baseStart_440953 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440953 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440953 prefixEnd_440953 := by exact prefixLift 440953
  have htrace : WordTrace (prefixWord ++ tailWord_440953) baseStart_440953 baseEnd_440953 := by
    simpa [prefixWord, tailWord_440953, baseEnd_440953] using wordTrace_append hprefix tailTrace_440953
  have hstable : (prefixWord ++ tailWord_440953).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440953).length < 2 ^ (prefixWord ++ tailWord_440953).sum := by decide
  have hdescent : baseEnd_440953 < baseStart_440953 := by decide
  rcases family_descends (prefixWord ++ tailWord_440953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_440970 : List Nat := [3, 1, 2, 3, 4, 1, 5]
def baseStart_440970 : Nat := 118140960795 + 440970 * 2 ^ 59
def prefixEnd_440970 : Nat := 4983230072969 + 3 ^ 40 * 440970 * 2
def baseEnd_440970 : Nat := 44726827498912580058671

theorem tailTrace_440970 : CollatzResearch.WordTrace tailWord_440970 prefixEnd_440970 44726827498912580058671 := by
  unfold tailWord_440970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4020874303112119131310091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10722331474965651016826909 4020874303112119131310091)
  ·
    refine ⟨6031311454668178696965137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4020874303112119131310091 6031311454668178696965137)
    ·
      refine ⟨4523483591001134022723853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6031311454668178696965137 4523483591001134022723853)
      ·
        refine ⟨1696306346625425258521445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4523483591001134022723853 1696306346625425258521445)
        ·
          refine ⟨318057439992267235972771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1696306346625425258521445 318057439992267235972771)
          ·
            refine ⟨477086159988400853959157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318057439992267235972771 477086159988400853959157)
            ·
              refine ⟨44726827498912580058671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 477086159988400853959157 44726827498912580058671)
              ·
                rfl

theorem cell19_440970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 5].length) (baseStart_440970 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_440970 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_440970 prefixEnd_440970 := by exact prefixLift 440970
  have htrace : WordTrace (prefixWord ++ tailWord_440970) baseStart_440970 baseEnd_440970 := by
    simpa [prefixWord, tailWord_440970, baseEnd_440970] using wordTrace_append hprefix tailTrace_440970
  have hstable : (prefixWord ++ tailWord_440970).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_440970).length < 2 ^ (prefixWord ++ tailWord_440970).sum := by decide
  have hdescent : baseEnd_440970 < baseStart_440970 := by decide
  rcases family_descends (prefixWord ++ tailWord_440970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441044 : List Nat := [2, 4, 1, 3, 3, 1, 1, 4]
def baseStart_441044 : Nat := 118140960795 + 441044 * 2 ^ 59
def prefixEnd_441044 : Nat := 4983230072969 + 3 ^ 40 * 441044 * 2
def baseEnd_441044 : Nat := 134202999574327494531367

theorem tailTrace_441044 : CollatzResearch.WordTrace tailWord_441044 prefixEnd_441044 134202999574327494531367 := by
  unfold tailWord_441044
  simp only [CollatzResearch.WordTrace]
  refine ⟨8043098107090193581717093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10724130809453591442289457 8043098107090193581717093)
  ·
    refine ⟨1508080895079411296571955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8043098107090193581717093 1508080895079411296571955)
    ·
      refine ⟨2262121342619116944857933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1508080895079411296571955 2262121342619116944857933)
      ·
        refine ⟨848295503482168854321725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2262121342619116944857933 848295503482168854321725)
        ·
          refine ⟨318110813805813320370647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 848295503482168854321725 318110813805813320370647)
          ·
            refine ⟨477166220708719980555971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318110813805813320370647 477166220708719980555971)
            ·
              refine ⟨715749331063079970833957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477166220708719980555971 715749331063079970833957)
              ·
                refine ⟨134202999574327494531367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 715749331063079970833957 134202999574327494531367)
                ·
                  rfl

theorem cell19_441044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 4].length) (baseStart_441044 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441044 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441044 prefixEnd_441044 := by exact prefixLift 441044
  have htrace : WordTrace (prefixWord ++ tailWord_441044) baseStart_441044 baseEnd_441044 := by
    simpa [prefixWord, tailWord_441044, baseEnd_441044] using wordTrace_append hprefix tailTrace_441044
  have hstable : (prefixWord ++ tailWord_441044).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441044).length < 2 ^ (prefixWord ++ tailWord_441044).sum := by decide
  have hdescent : baseEnd_441044 < baseStart_441044 := by decide
  rcases family_descends (prefixWord ++ tailWord_441044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441048 : List Nat := [2, 1, 2, 2, 3, 4, 1, 4]
def baseStart_441048 : Nat := 118140960795 + 441048 * 2 ^ 59
def prefixEnd_441048 : Nat := 4983230072969 + 3 ^ 40 * 441048 * 2
def baseEnd_441048 : Nat := 134204216713656670442467

theorem tailTrace_441048 : CollatzResearch.WordTrace tailWord_441048 prefixEnd_441048 134204216713656670442467 := by
  unfold tailWord_441048
  simp only [CollatzResearch.WordTrace]
  refine ⟨8043171053082947923289899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10724228070777263897719865 8043171053082947923289899)
  ·
    refine ⟨12064756579624421884934849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8043171053082947923289899 12064756579624421884934849)
    ·
      refine ⟨9048567434718316413701137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12064756579624421884934849 9048567434718316413701137)
      ·
        refine ⟨6786425576038737310275853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9048567434718316413701137 6786425576038737310275853)
        ·
          refine ⟨2544909591014526491353445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6786425576038737310275853 2544909591014526491353445)
          ·
            refine ⟨477170548315223717128771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2544909591014526491353445 477170548315223717128771)
            ·
              refine ⟨715755822472835575693157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477170548315223717128771 715755822472835575693157)
              ·
                refine ⟨134204216713656670442467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 715755822472835575693157 134204216713656670442467)
                ·
                  rfl

theorem cell19_441048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_441048 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441048 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441048 prefixEnd_441048 := by exact prefixLift 441048
  have htrace : WordTrace (prefixWord ++ tailWord_441048) baseStart_441048 baseEnd_441048 := by
    simpa [prefixWord, tailWord_441048, baseEnd_441048] using wordTrace_append hprefix tailTrace_441048
  have hstable : (prefixWord ++ tailWord_441048).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441048).length < 2 ^ (prefixWord ++ tailWord_441048).sum := by decide
  have hdescent : baseEnd_441048 < baseStart_441048 := by decide
  rcases family_descends (prefixWord ++ tailWord_441048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441086 : List Nat := [4, 2, 2, 1, 2, 2, 6]
def baseStart_441086 : Nat := 118140960795 + 441086 * 2 ^ 59
def prefixEnd_441086 : Nat := 4983230072969 + 3 ^ 40 * 441086 * 2
def baseEnd_441086 : Nat := 44738593179094613865973

theorem tailTrace_441086 : CollatzResearch.WordTrace tailWord_441086 prefixEnd_441086 44738593179094613865973 := by
  unfold tailWord_441086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2010966010003528542057889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10725152053352152224308741 2010966010003528542057889)
  ·
    refine ⟨1508224507502646406543417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2010966010003528542057889 1508224507502646406543417)
    ·
      refine ⟨1131168380626984804907563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1508224507502646406543417 1131168380626984804907563)
      ·
        refine ⟨1696752570940477207361345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1131168380626984804907563 1696752570940477207361345)
        ·
          refine ⟨1272564428205357905521009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1696752570940477207361345 1272564428205357905521009)
          ·
            refine ⟨954423321154018429140757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1272564428205357905521009 954423321154018429140757)
            ·
              refine ⟨44738593179094613865973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 954423321154018429140757 44738593179094613865973)
              ·
                rfl

theorem cell19_441086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 6].length) (baseStart_441086 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441086 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441086 prefixEnd_441086 := by exact prefixLift 441086
  have htrace : WordTrace (prefixWord ++ tailWord_441086) baseStart_441086 baseEnd_441086 := by
    simpa [prefixWord, tailWord_441086, baseEnd_441086] using wordTrace_append hprefix tailTrace_441086
  have hstable : (prefixWord ++ tailWord_441086).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441086).length < 2 ^ (prefixWord ++ tailWord_441086).sum := by decide
  have hdescent : baseEnd_441086 < baseStart_441086 := by decide
  rcases family_descends (prefixWord ++ tailWord_441086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441122 : List Nat := [3, 3, 1, 1, 2, 4, 2, 3]
def baseStart_441122 : Nat := 118140960795 + 441122 * 2 ^ 59
def prefixEnd_441122 : Nat := 4983230072969 + 3 ^ 40 * 441122 * 2
def baseEnd_441122 : Nat := 134226733791246424797821

theorem tailTrace_441122 : CollatzResearch.WordTrace tailWord_441122 prefixEnd_441122 134226733791246424797821 := by
  unfold tailWord_441122
  simp only [CollatzResearch.WordTrace]
  refine ⟨4022260276974451621193405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10726027405265204323182413 4022260276974451621193405)
  ·
    refine ⟨1508347603865419357947527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4022260276974451621193405 1508347603865419357947527)
    ·
      refine ⟨2262521405798129036921291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1508347603865419357947527 2262521405798129036921291)
      ·
        refine ⟨3393782108697193555381937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2262521405798129036921291 3393782108697193555381937)
        ·
          refine ⟨2545336581522895166536453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3393782108697193555381937 2545336581522895166536453)
          ·
            refine ⟨477250609035542843725585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2545336581522895166536453 477250609035542843725585)
            ·
              refine ⟨357937956776657132794189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477250609035542843725585 357937956776657132794189)
              ·
                refine ⟨134226733791246424797821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357937956776657132794189 134226733791246424797821)
                ·
                  rfl

theorem cell19_441122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_441122 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441122 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441122 prefixEnd_441122 := by exact prefixLift 441122
  have htrace : WordTrace (prefixWord ++ tailWord_441122) baseStart_441122 baseEnd_441122 := by
    simpa [prefixWord, tailWord_441122, baseEnd_441122] using wordTrace_append hprefix tailTrace_441122
  have hstable : (prefixWord ++ tailWord_441122).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441122).length < 2 ^ (prefixWord ++ tailWord_441122).sum := by decide
  have hdescent : baseEnd_441122 < baseStart_441122 := by decide
  rcases family_descends (prefixWord ++ tailWord_441122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441124 : List Nat := [2, 3, 1, 3, 3, 1, 1, 5]
def baseStart_441124 : Nat := 118140960795 + 441124 * 2 ^ 59
def prefixEnd_441124 : Nat := 4983230072969 + 3 ^ 40 * 441124 * 2
def baseEnd_441124 : Nat := 134227342360911012753371

theorem tailTrace_441124 : CollatzResearch.WordTrace tailWord_441124 prefixEnd_441124 134227342360911012753371 := by
  unfold tailWord_441124
  simp only [CollatzResearch.WordTrace]
  refine ⟨8044557026945280413173213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10726076035927040550897617 8044557026945280413173213)
  ·
    refine ⟨3016708885104480154939955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8044557026945280413173213 3016708885104480154939955)
    ·
      refine ⟨4525063327656720232409933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3016708885104480154939955 4525063327656720232409933)
      ·
        refine ⟨1696898747871270087153725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4525063327656720232409933 1696898747871270087153725)
        ·
          refine ⟨636337030451726282682647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1696898747871270087153725 636337030451726282682647)
          ·
            refine ⟨954505545677589424023971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636337030451726282682647 954505545677589424023971)
            ·
              refine ⟨1431758318516384136035957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954505545677589424023971 1431758318516384136035957)
              ·
                refine ⟨134227342360911012753371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1431758318516384136035957 134227342360911012753371)
                ·
                  rfl

theorem cell19_441124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_441124 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441124 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441124 prefixEnd_441124 := by exact prefixLift 441124
  have htrace : WordTrace (prefixWord ++ tailWord_441124) baseStart_441124 baseEnd_441124 := by
    simpa [prefixWord, tailWord_441124, baseEnd_441124] using wordTrace_append hprefix tailTrace_441124
  have hstable : (prefixWord ++ tailWord_441124).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441124).length < 2 ^ (prefixWord ++ tailWord_441124).sum := by decide
  have hdescent : baseEnd_441124 < baseStart_441124 := by decide
  rcases family_descends (prefixWord ++ tailWord_441124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441158 : List Nat := [6, 1, 1, 2, 2, 1, 2, 4]
def baseStart_441158 : Nat := 118140960795 + 441158 * 2 ^ 59
def prefixEnd_441158 : Nat := 4983230072969 + 3 ^ 40 * 441158 * 2
def baseEnd_441158 : Nat := 134237688045209007997723

theorem tailTrace_441158 : CollatzResearch.WordTrace tailWord_441158 prefixEnd_441158 134237688045209007997723 := by
  unfold tailWord_441158
  simp only [CollatzResearch.WordTrace]
  refine ⟨502823566742730769783879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10726902757178256422056085 502823566742730769783879)
  ·
    refine ⟨754235350114096154675819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 502823566742730769783879 754235350114096154675819)
    ·
      refine ⟨1131353025171144232013729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 754235350114096154675819 1131353025171144232013729)
      ·
        refine ⟨848514768878358174010297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1131353025171144232013729 848514768878358174010297)
        ·
          refine ⟨636386076658768630507723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 848514768878358174010297 636386076658768630507723)
          ·
            refine ⟨954579114988152945761585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636386076658768630507723 954579114988152945761585)
            ·
              refine ⟨715934336241114709321189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 954579114988152945761585 715934336241114709321189)
              ·
                refine ⟨134237688045209007997723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 715934336241114709321189 134237688045209007997723)
                ·
                  rfl

theorem cell19_441158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_441158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441158 prefixEnd_441158 := by exact prefixLift 441158
  have htrace : WordTrace (prefixWord ++ tailWord_441158) baseStart_441158 baseEnd_441158 := by
    simpa [prefixWord, tailWord_441158, baseEnd_441158] using wordTrace_append hprefix tailTrace_441158
  have hstable : (prefixWord ++ tailWord_441158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441158).length < 2 ^ (prefixWord ++ tailWord_441158).sum := by decide
  have hdescent : baseEnd_441158 < baseStart_441158 := by decide
  rcases family_descends (prefixWord ++ tailWord_441158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441164 : List Nat := [2, 2, 1, 3, 3, 1, 1, 6]
def baseStart_441164 : Nat := 118140960795 + 441164 * 2 ^ 59
def prefixEnd_441164 : Nat := 4983230072969 + 3 ^ 40 * 441164 * 2
def baseEnd_441164 : Nat := 134239513754202771864373

theorem tailTrace_441164 : CollatzResearch.WordTrace tailWord_441164 prefixEnd_441164 134239513754202771864373 := by
  unfold tailWord_441164
  simp only [CollatzResearch.WordTrace]
  refine ⟨8045286486872823828901273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10727048649163765105201697 8045286486872823828901273)
  ·
    refine ⟨6033964865154617871675955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8045286486872823828901273 6033964865154617871675955)
    ·
      refine ⟨9050947297731926807513933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6033964865154617871675955 9050947297731926807513933)
      ·
        refine ⟨3394105236649472552817725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9050947297731926807513933 3394105236649472552817725)
        ·
          refine ⟨1272789463743552207306647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3394105236649472552817725 1272789463743552207306647)
          ·
            refine ⟨1909184195615328310959971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1272789463743552207306647 1909184195615328310959971)
            ·
              refine ⟨2863776293422992466439957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909184195615328310959971 2863776293422992466439957)
              ·
                refine ⟨134239513754202771864373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2863776293422992466439957 134239513754202771864373)
                ·
                  rfl

theorem cell19_441164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_441164 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441164 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441164 prefixEnd_441164 := by exact prefixLift 441164
  have htrace : WordTrace (prefixWord ++ tailWord_441164) baseStart_441164 baseEnd_441164 := by
    simpa [prefixWord, tailWord_441164, baseEnd_441164] using wordTrace_append hprefix tailTrace_441164
  have hstable : (prefixWord ++ tailWord_441164).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441164).length < 2 ^ (prefixWord ++ tailWord_441164).sum := by decide
  have hdescent : baseEnd_441164 < baseStart_441164 := by decide
  rcases family_descends (prefixWord ++ tailWord_441164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441204 : List Nat := [2, 17]
def baseStart_441204 : Nat := 118140960795 + 441204 * 2 ^ 59
def prefixEnd_441204 : Nat := 4983230072969 + 3 ^ 40 * 441204 * 2
def baseEnd_441204 : Nat := 184158690188607038375

theorem tailTrace_441204 : CollatzResearch.WordTrace tailWord_441204 prefixEnd_441204 184158690188607038375 := by
  unfold tailWord_441204
  simp only [CollatzResearch.WordTrace]
  refine ⟨8046015946800367244629333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10728021262400489659505777 8046015946800367244629333)
  ·
    refine ⟨184158690188607038375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 17 8046015946800367244629333 184158690188607038375)
    ·
      rfl

theorem cell19_441204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 17].length) (baseStart_441204 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441204 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441204 prefixEnd_441204 := by exact prefixLift 441204
  have htrace : WordTrace (prefixWord ++ tailWord_441204) baseStart_441204 baseEnd_441204 := by
    simpa [prefixWord, tailWord_441204, baseEnd_441204] using wordTrace_append hprefix tailTrace_441204
  have hstable : (prefixWord ++ tailWord_441204).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441204).length < 2 ^ (prefixWord ++ tailWord_441204).sum := by decide
  have hdescent : baseEnd_441204 < baseStart_441204 := by decide
  rcases family_descends (prefixWord ++ tailWord_441204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441221 : List Nat := [1, 3, 1, 1, 3, 3, 3, 4]
def baseStart_441221 : Nat := 118140960795 + 441221 * 2 ^ 59
def prefixEnd_441221 : Nat := 4983230072969 + 3 ^ 40 * 441221 * 2
def baseEnd_441221 : Nat := 134256857989643528597551

theorem tailTrace_441221 : CollatzResearch.WordTrace tailWord_441221 prefixEnd_441221 134256857989643528597551 := by
  unfold tailWord_441221
  simp only [CollatzResearch.WordTrace]
  refine ⟨16092651934539146392627517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10728434623026097595085011 16092651934539146392627517)
  ·
    refine ⟨6034744475452179897235319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16092651934539146392627517 6034744475452179897235319)
    ·
      refine ⟨9052116713178269845852979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6034744475452179897235319 9052116713178269845852979)
      ·
        refine ⟨13578175069767404768779469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9052116713178269845852979 13578175069767404768779469)
        ·
          refine ⟨5091815651162776788292301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13578175069767404768779469 5091815651162776788292301)
          ·
            refine ⟨1909430869186041295609613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5091815651162776788292301 1909430869186041295609613)
            ·
              refine ⟨716036575944765485853605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1909430869186041295609613 716036575944765485853605)
              ·
                refine ⟨134256857989643528597551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 716036575944765485853605 134256857989643528597551)
                ·
                  rfl

theorem cell19_441221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_441221 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441221 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441221 prefixEnd_441221 := by exact prefixLift 441221
  have htrace : WordTrace (prefixWord ++ tailWord_441221) baseStart_441221 baseEnd_441221 := by
    simpa [prefixWord, tailWord_441221, baseEnd_441221] using wordTrace_append hprefix tailTrace_441221
  have hstable : (prefixWord ++ tailWord_441221).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441221).length < 2 ^ (prefixWord ++ tailWord_441221).sum := by decide
  have hdescent : baseEnd_441221 < baseStart_441221 := by decide
  rcases family_descends (prefixWord ++ tailWord_441221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441278 : List Nat := [4, 2, 1, 1, 1, 2, 2, 6]
def baseStart_441278 : Nat := 118140960795 + 441278 * 2 ^ 59
def prefixEnd_441278 : Nat := 4983230072969 + 3 ^ 40 * 441278 * 2
def baseEnd_441278 : Nat := 134274202225084285330729

theorem tailTrace_441278 : CollatzResearch.WordTrace tailWord_441278 prefixEnd_441278 134274202225084285330729 := by
  unfold tailWord_441278
  simp only [CollatzResearch.WordTrace]
  refine ⟨2011841361916580640931561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10729820596888430084968325 2011841361916580640931561)
  ·
    refine ⟨1508881021437435480698671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2011841361916580640931561 1508881021437435480698671)
    ·
      refine ⟨2263321532156153221048007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1508881021437435480698671 2263321532156153221048007)
      ·
        refine ⟨3394982298234229831572011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2263321532156153221048007 3394982298234229831572011)
        ·
          refine ⟨5092473447351344747358017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3394982298234229831572011 5092473447351344747358017)
          ·
            refine ⟨3819355085513508560518513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5092473447351344747358017 3819355085513508560518513)
            ·
              refine ⟨2864516314135131420388885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3819355085513508560518513 2864516314135131420388885)
              ·
                refine ⟨134274202225084285330729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2864516314135131420388885 134274202225084285330729)
                ·
                  rfl

theorem cell19_441278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_441278 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441278 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441278 prefixEnd_441278 := by exact prefixLift 441278
  have htrace : WordTrace (prefixWord ++ tailWord_441278) baseStart_441278 baseEnd_441278 := by
    simpa [prefixWord, tailWord_441278, baseEnd_441278] using wordTrace_append hprefix tailTrace_441278
  have hstable : (prefixWord ++ tailWord_441278).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441278).length < 2 ^ (prefixWord ++ tailWord_441278).sum := by decide
  have hdescent : baseEnd_441278 < baseStart_441278 := by decide
  rcases family_descends (prefixWord ++ tailWord_441278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_441295 : List Nat := [1, 1, 2, 1, 1, 8, 2, 3]
def baseStart_441295 : Nat := 118140960795 + 441295 * 2 ^ 59
def prefixEnd_441295 : Nat := 4983230072969 + 3 ^ 40 * 441295 * 2
def baseEnd_441295 : Nat := 134279375067233282952905

theorem tailTrace_441295 : CollatzResearch.WordTrace tailWord_441295 prefixEnd_441295 134279375067233282952905 := by
  unfold tailWord_441295
  simp only [CollatzResearch.WordTrace]
  refine ⟨16095350936271057030821339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10730233957514038020547559 16095350936271057030821339)
  ·
    refine ⟨24143026404406585546232009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16095350936271057030821339 24143026404406585546232009)
    ·
      refine ⟨18107269803304939159674007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24143026404406585546232009 18107269803304939159674007)
      ·
        refine ⟨27160904704957408739511011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18107269803304939159674007 27160904704957408739511011)
        ·
          refine ⟨40741357057436113109266517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27160904704957408739511011 40741357057436113109266517)
          ·
            refine ⟨477437778016829450499217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 40741357057436113109266517 477437778016829450499217)
            ·
              refine ⟨358078333512622087874413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 477437778016829450499217 358078333512622087874413)
              ·
                refine ⟨134279375067233282952905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358078333512622087874413 134279375067233282952905)
                ·
                  rfl

theorem cell19_441295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 3].length) (baseStart_441295 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_441295 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_441295 prefixEnd_441295 := by exact prefixLift 441295
  have htrace : WordTrace (prefixWord ++ tailWord_441295) baseStart_441295 baseEnd_441295 := by
    simpa [prefixWord, tailWord_441295, baseEnd_441295] using wordTrace_append hprefix tailTrace_441295
  have hstable : (prefixWord ++ tailWord_441295).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_441295).length < 2 ^ (prefixWord ++ tailWord_441295).sum := by decide
  have hdescent : baseEnd_441295 < baseStart_441295 := by decide
  rcases family_descends (prefixWord ++ tailWord_441295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
