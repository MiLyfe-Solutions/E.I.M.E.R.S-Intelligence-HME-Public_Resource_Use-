import V185TrunkScan23Chunk0413

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2446905 : List Nat := [1, 2, 1, 5, 1, 2, 3, 3, 1, 4]
def baseStart_2446905 : Nat := 118140960795 + 2446905 * 2 ^ 59
def prefixEnd_2446905 : Nat := 4983230072969 + 3 ^ 40 * 2446905 * 2
def baseEnd_2446905 : Nat := 418812793629951402211465

theorem tailTrace_2446905 : CollatzResearch.WordTrace tailWord_2446905 prefixEnd_2446905 418812793629951402211465 := by
  unfold tailWord_2446905
  simp only [CollatzResearch.WordTrace]
  refine ⟨89245957200288557948542169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59497304800192371965694779 89245957200288557948542169)
  ·
    refine ⟨66934467900216418461406627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89245957200288557948542169 66934467900216418461406627)
    ·
      refine ⟨100401701850324627692109941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66934467900216418461406627 100401701850324627692109941)
      ·
        refine ⟨9412659548467933846135307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100401701850324627692109941 9412659548467933846135307)
        ·
          refine ⟨14118989322701900769202961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9412659548467933846135307 14118989322701900769202961)
          ·
            refine ⟨10589241992026425576902221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14118989322701900769202961 10589241992026425576902221)
            ·
              refine ⟨3970965747009909591338333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10589241992026425576902221 3970965747009909591338333)
              ·
                refine ⟨1489112155128716096751875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3970965747009909591338333 1489112155128716096751875)
                ·
                  refine ⟨2233668232693074145127813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1489112155128716096751875 2233668232693074145127813)
                  ·
                    refine ⟨418812793629951402211465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2233668232693074145127813 418812793629951402211465)
                    ·
                      rfl

theorem cell23_2446905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 1, 4].length) (baseStart_2446905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446905 prefixEnd_2446905 := by exact prefixLift 2446905
  have htrace : WordTrace (prefixWord ++ tailWord_2446905) baseStart_2446905 baseEnd_2446905 := by
    simpa [prefixWord, tailWord_2446905, baseEnd_2446905] using wordTrace_append hprefix tailTrace_2446905
  have hstable : (prefixWord ++ tailWord_2446905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446905).length < 2 ^ (prefixWord ++ tailWord_2446905).sum := by decide
  have hdescent : baseEnd_2446905 < baseStart_2446905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446948 : List Nat := [2, 3, 1, 1, 2, 3, 3, 2, 1, 5]
def baseStart_2446948 : Nat := 118140960795 + 2446948 * 2 ^ 59
def prefixEnd_2446948 : Nat := 4983230072969 + 3 ^ 40 * 2446948 * 2
def baseEnd_2446948 : Nat := 418820153519332512798899

theorem tailTrace_2446948 : CollatzResearch.WordTrace tailWord_2446948 prefixEnd_2446948 418820153519332512798899 := by
  unfold tailWord_2446948
  simp only [CollatzResearch.WordTrace]
  refine ⟨44623762769566388146178749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59498350359421850861571665 44623762769566388146178749)
  ·
    refine ⟨16733911038587395554817031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44623762769566388146178749 16733911038587395554817031)
    ·
      refine ⟨25100866557881093332225547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16733911038587395554817031 25100866557881093332225547)
      ·
        refine ⟨37651299836821639998338321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25100866557881093332225547 37651299836821639998338321)
        ·
          refine ⟨28238474877616229998753741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37651299836821639998338321 28238474877616229998753741)
          ·
            refine ⟨10589428079106086249532653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28238474877616229998753741 10589428079106086249532653)
            ·
              refine ⟨3971035529664782343574745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10589428079106086249532653 3971035529664782343574745)
              ·
                refine ⟨2978276647248586757681059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3971035529664782343574745 2978276647248586757681059)
                ·
                  refine ⟨4467414970872880136521589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2978276647248586757681059 4467414970872880136521589)
                  ·
                    refine ⟨418820153519332512798899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4467414970872880136521589 418820153519332512798899)
                    ·
                      rfl

theorem cell23_2446948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_2446948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446948 prefixEnd_2446948 := by exact prefixLift 2446948
  have htrace : WordTrace (prefixWord ++ tailWord_2446948) baseStart_2446948 baseEnd_2446948 := by
    simpa [prefixWord, tailWord_2446948, baseEnd_2446948] using wordTrace_append hprefix tailTrace_2446948
  have hstable : (prefixWord ++ tailWord_2446948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446948).length < 2 ^ (prefixWord ++ tailWord_2446948).sum := by decide
  have hdescent : baseEnd_2446948 < baseStart_2446948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446961 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 6, 4]
def baseStart_2446961 : Nat := 118140960795 + 2446961 * 2 ^ 59
def prefixEnd_2446961 : Nat := 4983230072969 + 3 ^ 40 * 2446961 * 2
def baseEnd_2446961 : Nat := 418822378602168662511379

theorem tailTrace_2446961 : CollatzResearch.WordTrace tailWord_2446961 prefixEnd_2446961 418822378602168662511379 := by
  unfold tailWord_2446961
  simp only [CollatzResearch.WordTrace]
  refine ⟨89247999688085679512580737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59498666458723786341720491 89247999688085679512580737)
  ·
    refine ⟨66935999766064259634435553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89247999688085679512580737 66935999766064259634435553)
    ·
      refine ⟨50201999824548194725826665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66935999766064259634435553 50201999824548194725826665)
      ·
        refine ⟨37651499868411146044369999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50201999824548194725826665 37651499868411146044369999)
        ·
          refine ⟨56477249802616719066554999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37651499868411146044369999 56477249802616719066554999)
          ·
            refine ⟨84715874703925078599832499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56477249802616719066554999 84715874703925078599832499)
            ·
              refine ⟨127073812055887617899748749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84715874703925078599832499 127073812055887617899748749)
              ·
                refine ⟨47652679520957856712405781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127073812055887617899748749 47652679520957856712405781)
                ·
                  refine ⟨2233719352544899533394021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47652679520957856712405781 2233719352544899533394021)
                  ·
                    refine ⟨418822378602168662511379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2233719352544899533394021 418822378602168662511379)
                    ·
                      rfl

theorem cell23_2446961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_2446961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446961 prefixEnd_2446961 := by exact prefixLift 2446961
  have htrace : WordTrace (prefixWord ++ tailWord_2446961) baseStart_2446961 baseEnd_2446961 := by
    simpa [prefixWord, tailWord_2446961, baseEnd_2446961] using wordTrace_append hprefix tailTrace_2446961
  have hstable : (prefixWord ++ tailWord_2446961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446961).length < 2 ^ (prefixWord ++ tailWord_2446961).sum := by decide
  have hdescent : baseEnd_2446961 < baseStart_2446961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2446981 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 3, 2, 4]
def baseStart_2446981 : Nat := 118140960795 + 2446981 * 2 ^ 59
def prefixEnd_2446981 : Nat := 4983230072969 + 3 ^ 40 * 2446981 * 2
def baseEnd_2446981 : Nat := 1256477405419595909284045

theorem tailTrace_2446981 : CollatzResearch.WordTrace tailWord_2446981 prefixEnd_2446981 1256477405419595909284045 := by
  unfold tailWord_2446981
  simp only [CollatzResearch.WordTrace]
  refine ⟨89248729148013222928308797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59499152765342148618872531 89248729148013222928308797)
  ·
    refine ⟨33468273430504958598115799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89248729148013222928308797 33468273430504958598115799)
    ·
      refine ⟨50202410145757437897173699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33468273430504958598115799 50202410145757437897173699)
      ·
        refine ⟨75303615218636156845760549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50202410145757437897173699 75303615218636156845760549)
        ·
          refine ⟨14119427853494279408580103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75303615218636156845760549 14119427853494279408580103)
          ·
            refine ⟨21179141780241419112870155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14119427853494279408580103 21179141780241419112870155)
            ·
              refine ⟨31768712670362128669305233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21179141780241419112870155 31768712670362128669305233)
              ·
                refine ⟨23826534502771596501978925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31768712670362128669305233 23826534502771596501978925)
                ·
                  refine ⟨8934950438539348688242097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23826534502771596501978925 8934950438539348688242097)
                  ·
                    refine ⟨6701212828904511516181573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8934950438539348688242097 6701212828904511516181573)
                    ·
                      refine ⟨1256477405419595909284045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6701212828904511516181573 1256477405419595909284045)
                      ·
                        rfl

theorem cell23_2446981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_2446981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2446981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2446981 prefixEnd_2446981 := by exact prefixLift 2446981
  have htrace : WordTrace (prefixWord ++ tailWord_2446981) baseStart_2446981 baseEnd_2446981 := by
    simpa [prefixWord, tailWord_2446981, baseEnd_2446981] using wordTrace_append hprefix tailTrace_2446981
  have hstable : (prefixWord ++ tailWord_2446981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2446981).length < 2 ^ (prefixWord ++ tailWord_2446981).sum := by decide
  have hdescent : baseEnd_2446981 < baseStart_2446981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2446981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447008 : List Nat := [2, 1, 1, 4, 3, 2, 3, 7]
def baseStart_2447008 : Nat := 118140960795 + 2447008 * 2 ^ 59
def prefixEnd_2447008 : Nat := 4983230072969 + 3 ^ 40 * 2447008 * 2
def baseEnd_2447008 : Nat := 46536713681380270505423

theorem tailTrace_2447008 : CollatzResearch.WordTrace tailWord_2447008 prefixEnd_2447008 46536713681380270505423 := by
  unfold tailWord_2447008
  simp only [CollatzResearch.WordTrace]
  refine ⟨44624856959457703269770839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59499809279276937693027785 44624856959457703269770839)
  ·
    refine ⟨66937285439186554904656259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44624856959457703269770839 66937285439186554904656259)
    ·
      refine ⟨100405928158779832356984389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66937285439186554904656259 100405928158779832356984389)
      ·
        refine ⟨18826111529771218566934573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100405928158779832356984389 18826111529771218566934573)
        ·
          refine ⟨7059791823664206962600465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18826111529771218566934573 7059791823664206962600465)
          ·
            refine ⟨5294843867748155221950349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7059791823664206962600465 5294843867748155221950349)
            ·
              refine ⟨1985566450405558208231381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5294843867748155221950349 1985566450405558208231381)
              ·
                refine ⟨46536713681380270505423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1985566450405558208231381 46536713681380270505423)
                ·
                  rfl

theorem cell23_2447008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 7].length) (baseStart_2447008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447008 prefixEnd_2447008 := by exact prefixLift 2447008
  have htrace : WordTrace (prefixWord ++ tailWord_2447008) baseStart_2447008 baseEnd_2447008 := by
    simpa [prefixWord, tailWord_2447008, baseEnd_2447008] using wordTrace_append hprefix tailTrace_2447008
  have hstable : (prefixWord ++ tailWord_2447008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447008).length < 2 ^ (prefixWord ++ tailWord_2447008).sum := by decide
  have hdescent : baseEnd_2447008 < baseStart_2447008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447016 : List Nat := [2, 1, 7, 1, 1, 2, 2, 1, 1, 5]
def baseStart_2447016 : Nat := 118140960795 + 2447016 * 2 ^ 59
def prefixEnd_2447016 : Nat := 4983230072969 + 3 ^ 40 * 2447016 * 2
def baseEnd_2447016 : Nat := 418831792414167757448795

theorem tailTrace_2447016 : CollatzResearch.WordTrace tailWord_2447016 prefixEnd_2447016 418831792414167757448795 := by
  unfold tailWord_2447016
  simp only [CollatzResearch.WordTrace]
  refine ⟨44625002851443211952916451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59500003801924282603888601 44625002851443211952916451)
  ·
    refine ⟨66937504277164817929374677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44625002851443211952916451 66937504277164817929374677)
    ·
      refine ⟨1568847756496050420219719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 66937504277164817929374677 1568847756496050420219719)
      ·
        refine ⟨2353271634744075630329579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1568847756496050420219719 2353271634744075630329579)
        ·
          refine ⟨3529907452116113445494369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353271634744075630329579 3529907452116113445494369)
          ·
            refine ⟨2647430589087085084120777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3529907452116113445494369 2647430589087085084120777)
            ·
              refine ⟨1985572941815313813090583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2647430589087085084120777 1985572941815313813090583)
              ·
                refine ⟨2978359412722970719635875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1985572941815313813090583 2978359412722970719635875)
                ·
                  refine ⟨4467539119084456079453813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2978359412722970719635875 4467539119084456079453813)
                  ·
                    refine ⟨418831792414167757448795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4467539119084456079453813 418831792414167757448795)
                    ·
                      rfl

theorem cell23_2447016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_2447016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447016 prefixEnd_2447016 := by exact prefixLift 2447016
  have htrace : WordTrace (prefixWord ++ tailWord_2447016) baseStart_2447016 baseEnd_2447016 := by
    simpa [prefixWord, tailWord_2447016, baseEnd_2447016] using wordTrace_append hprefix tailTrace_2447016
  have hstable : (prefixWord ++ tailWord_2447016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447016).length < 2 ^ (prefixWord ++ tailWord_2447016).sum := by decide
  have hdescent : baseEnd_2447016 < baseStart_2447016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447029 : List Nat := [1, 3, 3, 3, 3, 1, 1, 2, 2, 4]
def baseStart_2447029 : Nat := 118140960795 + 2447029 * 2 ^ 59
def prefixEnd_2447029 : Nat := 4983230072969 + 3 ^ 40 * 2447029 * 2
def baseEnd_2447029 : Nat := 418834017497003907161275

theorem tailTrace_2447029 : CollatzResearch.WordTrace tailWord_2447029 prefixEnd_2447029 418834017497003907161275 := by
  unfold tailWord_2447029
  simp only [CollatzResearch.WordTrace]
  refine ⟨89250479851839327126056141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59500319901226218084037427 89250479851839327126056141)
  ·
    refine ⟨33468929944439747672271053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89250479851839327126056141 33468929944439747672271053)
    ·
      refine ⟨12550848729164905377101645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33468929944439747672271053 12550848729164905377101645)
      ·
        refine ⟨4706568273436839516413117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12550848729164905377101645 4706568273436839516413117)
        ·
          refine ⟨1764963102538814818654919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4706568273436839516413117 1764963102538814818654919)
          ·
            refine ⟨2647444653808222227982379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1764963102538814818654919 2647444653808222227982379)
            ·
              refine ⟨3971166980712333341973569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2647444653808222227982379 3971166980712333341973569)
              ·
                refine ⟨2978375235534250006480177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3971166980712333341973569 2978375235534250006480177)
                ·
                  refine ⟨2233781426650687504860133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2978375235534250006480177 2233781426650687504860133)
                  ·
                    refine ⟨418834017497003907161275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2233781426650687504860133 418834017497003907161275)
                    ·
                      rfl

theorem cell23_2447029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_2447029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447029 prefixEnd_2447029 := by exact prefixLift 2447029
  have htrace : WordTrace (prefixWord ++ tailWord_2447029) baseStart_2447029 baseEnd_2447029 := by
    simpa [prefixWord, tailWord_2447029, baseEnd_2447029] using wordTrace_append hprefix tailTrace_2447029
  have hstable : (prefixWord ++ tailWord_2447029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447029).length < 2 ^ (prefixWord ++ tailWord_2447029).sum := by decide
  have hdescent : baseEnd_2447029 < baseStart_2447029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447046 : List Nat := [6, 1, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_2447046 : Nat := 118140960795 + 2447046 * 2 ^ 59
def prefixEnd_2447046 : Nat := 4983230072969 + 3 ^ 40 * 2447046 * 2
def baseEnd_2447046 : Nat := 418836927220712718323749

theorem tailTrace_2447046 : CollatzResearch.WordTrace tailWord_2447046 prefixEnd_2447046 418836927220712718323749 := by
  unfold tailWord_2447046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2789096871649304344669531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59500733261851826019616661 2789096871649304344669531)
  ·
    refine ⟨4183645307473956517004297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2789096871649304344669531 4183645307473956517004297)
    ·
      refine ⟨3137733980605467387753223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4183645307473956517004297 3137733980605467387753223)
      ·
        refine ⟨4706600970908201081629835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3137733980605467387753223 4706600970908201081629835)
        ·
          refine ⟨7059901456362301622444753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4706600970908201081629835 7059901456362301622444753)
          ·
            refine ⟨5294926092271726216833565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7059901456362301622444753 5294926092271726216833565)
            ·
              refine ⟨1985597284601897331312587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5294926092271726216833565 1985597284601897331312587)
              ·
                refine ⟨2978395926902845996968881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1985597284601897331312587 2978395926902845996968881)
                ·
                  refine ⟨2233796945177134497726661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2978395926902845996968881 2233796945177134497726661)
                  ·
                    refine ⟨418836927220712718323749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2233796945177134497726661 418836927220712718323749)
                    ·
                      rfl

theorem cell23_2447046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_2447046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447046 prefixEnd_2447046 := by exact prefixLift 2447046
  have htrace : WordTrace (prefixWord ++ tailWord_2447046) baseStart_2447046 baseEnd_2447046 := by
    simpa [prefixWord, tailWord_2447046, baseEnd_2447046] using wordTrace_append hprefix tailTrace_2447046
  have hstable : (prefixWord ++ tailWord_2447046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447046).length < 2 ^ (prefixWord ++ tailWord_2447046).sum := by decide
  have hdescent : baseEnd_2447046 < baseStart_2447046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447052 : List Nat := [2, 2, 1, 5, 2, 2, 1, 1, 1, 3, 3]
def baseStart_2447052 : Nat := 118140960795 + 2447052 * 2 ^ 59
def prefixEnd_2447052 : Nat := 4983230072969 + 3 ^ 40 * 2447052 * 2
def baseEnd_2447052 : Nat := 1256513862546065131496219

theorem tailTrace_2447052 : CollatzResearch.WordTrace tailWord_2447052 prefixEnd_2447052 1256513862546065131496219 := by
  unfold tailWord_2447052
  simp only [CollatzResearch.WordTrace]
  refine ⟨44625659365378001027071705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59500879153837334702762273 44625659365378001027071705)
  ·
    refine ⟨33469244524033500770303779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44625659365378001027071705 33469244524033500770303779)
    ·
      refine ⟨50203866786050251155455669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33469244524033500770303779 50203866786050251155455669)
      ·
        refine ⟨4706612511192211045823969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50203866786050251155455669 4706612511192211045823969)
        ·
          refine ⟨3529959383394158284367977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4706612511192211045823969 3529959383394158284367977)
          ·
            refine ⟨2647469537545618713275983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3529959383394158284367977 2647469537545618713275983)
            ·
              refine ⟨3971204306318428069913975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2647469537545618713275983 3971204306318428069913975)
              ·
                refine ⟨5956806459477642104870963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3971204306318428069913975 5956806459477642104870963)
                ·
                  refine ⟨8935209689216463157306445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5956806459477642104870963 8935209689216463157306445)
                  ·
                    refine ⟨3350703633456173683989917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8935209689216463157306445 3350703633456173683989917)
                    ·
                      refine ⟨1256513862546065131496219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3350703633456173683989917 1256513862546065131496219)
                      ·
                        rfl

theorem cell23_2447052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_2447052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447052 prefixEnd_2447052 := by exact prefixLift 2447052
  have htrace : WordTrace (prefixWord ++ tailWord_2447052) baseStart_2447052 baseEnd_2447052 := by
    simpa [prefixWord, tailWord_2447052, baseEnd_2447052] using wordTrace_append hprefix tailTrace_2447052
  have hstable : (prefixWord ++ tailWord_2447052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447052).length < 2 ^ (prefixWord ++ tailWord_2447052).sum := by decide
  have hdescent : baseEnd_2447052 < baseStart_2447052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447101 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_2447101 : Nat := 118140960795 + 2447101 * 2 ^ 59
def prefixEnd_2447101 : Nat := 4983230072969 + 3 ^ 40 * 2447101 * 2
def baseEnd_2447101 : Nat := 1256539023098135439783493

theorem tailTrace_2447101 : CollatzResearch.WordTrace tailWord_2447101 prefixEnd_2447101 1256539023098135439783493 := by
  unfold tailWord_2447101
  simp only [CollatzResearch.WordTrace]
  refine ⟨89253105907578483422677157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59502070605052322281784771 89253105907578483422677157)
  ·
    refine ⟨16734957357670965641751967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89253105907578483422677157 16734957357670965641751967)
    ·
      refine ⟨25102436036506448462627951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16734957357670965641751967 25102436036506448462627951)
      ·
        refine ⟨37653654054759672693941927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25102436036506448462627951 37653654054759672693941927)
        ·
          refine ⟨56480481082139509040912891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37653654054759672693941927 56480481082139509040912891)
          ·
            refine ⟨84720721623209263561369337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56480481082139509040912891 84720721623209263561369337)
            ·
              refine ⟨63540541217406947671027003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84720721623209263561369337 63540541217406947671027003)
              ·
                refine ⟨95310811826110421506540505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63540541217406947671027003 95310811826110421506540505)
                ·
                  refine ⟨71483108869582816129905379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95310811826110421506540505 71483108869582816129905379)
                  ·
                    refine ⟨107224663304374224194858069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71483108869582816129905379 107224663304374224194858069)
                    ·
                      refine ⟨1256539023098135439783493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 107224663304374224194858069 1256539023098135439783493)
                      ·
                        rfl

theorem cell23_2447101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_2447101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447101 prefixEnd_2447101 := by exact prefixLift 2447101
  have htrace : WordTrace (prefixWord ++ tailWord_2447101) baseStart_2447101 baseEnd_2447101 := by
    simpa [prefixWord, tailWord_2447101, baseEnd_2447101] using wordTrace_append hprefix tailTrace_2447101
  have hstable : (prefixWord ++ tailWord_2447101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447101).length < 2 ^ (prefixWord ++ tailWord_2447101).sum := by decide
  have hdescent : baseEnd_2447101 < baseStart_2447101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447121 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 7]
def baseStart_2447121 : Nat := 118140960795 + 2447121 * 2 ^ 59
def prefixEnd_2447121 : Nat := 4983230072969 + 3 ^ 40 * 2447121 * 2
def baseEnd_2447121 : Nat := 1256549292711225361533401

theorem tailTrace_2447121 : CollatzResearch.WordTrace tailWord_2447121 prefixEnd_2447121 1256549292711225361533401 := by
  unfold tailWord_2447121
  simp only [CollatzResearch.WordTrace]
  refine ⟨89253835367506026838405217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59502556911670684558936811 89253835367506026838405217)
  ·
    refine ⟨66940376525629520128803913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89253835367506026838405217 66940376525629520128803913)
    ·
      refine ⟨50205282394222140096602935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66940376525629520128803913 50205282394222140096602935)
      ·
        refine ⟨75307923591333210144904403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50205282394222140096602935 75307923591333210144904403)
        ·
          refine ⟨112961885386999815217356605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75307923591333210144904403 112961885386999815217356605)
          ·
            refine ⟨42360707020124930706508727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112961885386999815217356605 42360707020124930706508727)
            ·
              refine ⟨63541060530187396059763091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42360707020124930706508727 63541060530187396059763091)
              ·
                refine ⟨95311590795281094089644637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63541060530187396059763091 95311590795281094089644637)
                ·
                  refine ⟨35741846548230410283616739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95311590795281094089644637 35741846548230410283616739)
                  ·
                    refine ⟨53612769822345615425425109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35741846548230410283616739 53612769822345615425425109)
                    ·
                      refine ⟨1256549292711225361533401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53612769822345615425425109 1256549292711225361533401)
                      ·
                        rfl

theorem cell23_2447121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_2447121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447121 prefixEnd_2447121 := by exact prefixLift 2447121
  have htrace : WordTrace (prefixWord ++ tailWord_2447121) baseStart_2447121 baseEnd_2447121 := by
    simpa [prefixWord, tailWord_2447121, baseEnd_2447121] using wordTrace_append hprefix tailTrace_2447121
  have hstable : (prefixWord ++ tailWord_2447121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447121).length < 2 ^ (prefixWord ++ tailWord_2447121).sum := by decide
  have hdescent : baseEnd_2447121 < baseStart_2447121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447128 : List Nat := [2, 1, 2, 3, 1, 1, 3, 3, 2, 5]
def baseStart_2447128 : Nat := 118140960795 + 2447128 * 2 ^ 59
def prefixEnd_2447128 : Nat := 4983230072969 + 3 ^ 40 * 2447128 * 2
def baseEnd_2447128 : Nat := 418850962358602278048623

theorem tailTrace_2447128 : CollatzResearch.WordTrace tailWord_2447128 prefixEnd_2447128 418850962358602278048623 := by
  unfold tailWord_2447128
  simp only [CollatzResearch.WordTrace]
  refine ⟨44627045339240333516955019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59502727118987111355940025 44627045339240333516955019)
  ·
    refine ⟨66940568008860500275432529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44627045339240333516955019 66940568008860500275432529)
    ·
      refine ⟨50205426006645375206574397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66940568008860500275432529 50205426006645375206574397)
      ·
        refine ⟨18827034752492015702465399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50205426006645375206574397 18827034752492015702465399)
        ·
          refine ⟨28240552128738023553698099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18827034752492015702465399 28240552128738023553698099)
          ·
            refine ⟨42360828193107035330547149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28240552128738023553698099 42360828193107035330547149)
            ·
              refine ⟨15885310572415138248955181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42360828193107035330547149 15885310572415138248955181)
              ·
                refine ⟨5956991464655676843358193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15885310572415138248955181 5956991464655676843358193)
                ·
                  refine ⟨4467743598491757632518645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5956991464655676843358193 4467743598491757632518645)
                  ·
                    refine ⟨418850962358602278048623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4467743598491757632518645 418850962358602278048623)
                    ·
                      rfl

theorem cell23_2447128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_2447128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447128 prefixEnd_2447128 := by exact prefixLift 2447128
  have htrace : WordTrace (prefixWord ++ tailWord_2447128) baseStart_2447128 baseEnd_2447128 := by
    simpa [prefixWord, tailWord_2447128, baseEnd_2447128] using wordTrace_append hprefix tailTrace_2447128
  have hstable : (prefixWord ++ tailWord_2447128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447128).length < 2 ^ (prefixWord ++ tailWord_2447128).sum := by decide
  have hdescent : baseEnd_2447128 < baseStart_2447128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447138 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 3, 2, 5]
def baseStart_2447138 : Nat := 118140960795 + 2447138 * 2 ^ 59
def prefixEnd_2447138 : Nat := 4983230072969 + 3 ^ 40 * 2447138 * 2
def baseEnd_2447138 : Nat := 1256558021882351795020823

theorem tailTrace_2447138 : CollatzResearch.WordTrace tailWord_2447138 prefixEnd_2447138 1256558021882351795020823 := by
  unfold tailWord_2447138
  simp only [CollatzResearch.WordTrace]
  refine ⟨22313613852111109685443517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59502970272296292494516045 22313613852111109685443517)
  ·
    refine ⟨8367605194541666132041319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22313613852111109685443517 8367605194541666132041319)
    ·
      refine ⟨12551407791812499198061979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8367605194541666132041319 12551407791812499198061979)
      ·
        refine ⟨18827111687718748797092969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12551407791812499198061979 18827111687718748797092969)
        ·
          refine ⟨14120333765789061597819727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18827111687718748797092969 14120333765789061597819727)
          ·
            refine ⟨21180500648683592396729591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14120333765789061597819727 21180500648683592396729591)
            ·
              refine ⟨31770750973025388595094387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21180500648683592396729591 31770750973025388595094387)
              ·
                refine ⟨47656126459538082892641581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31770750973025388595094387 47656126459538082892641581)
                ·
                  refine ⟨17871047422326781084740593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47656126459538082892641581 17871047422326781084740593)
                  ·
                    refine ⟨13403285566745085813555445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17871047422326781084740593 13403285566745085813555445)
                    ·
                      refine ⟨1256558021882351795020823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13403285566745085813555445 1256558021882351795020823)
                      ·
                        rfl

theorem cell23_2447138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_2447138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447138 prefixEnd_2447138 := by exact prefixLift 2447138
  have htrace : WordTrace (prefixWord ++ tailWord_2447138) baseStart_2447138 baseEnd_2447138 := by
    simpa [prefixWord, tailWord_2447138, baseEnd_2447138] using wordTrace_append hprefix tailTrace_2447138
  have hstable : (prefixWord ++ tailWord_2447138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447138).length < 2 ^ (prefixWord ++ tailWord_2447138).sum := by decide
  have hdescent : baseEnd_2447138 < baseStart_2447138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447185 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 1, 4, 3]
def baseStart_2447185 : Nat := 118140960795 + 2447185 * 2 ^ 59
def prefixEnd_2447185 : Nat := 4983230072969 + 3 ^ 40 * 2447185 * 2
def baseEnd_2447185 : Nat := 1256582155473113111133107

theorem tailTrace_2447185 : CollatzResearch.WordTrace tailWord_2447185 prefixEnd_2447185 1256582155473113111133107 := by
  unfold tailWord_2447185
  simp only [CollatzResearch.WordTrace]
  refine ⟨89256169639274165768735009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59504113092849443845823339 89256169639274165768735009)
  ·
    refine ⟨66942127229455624326551257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89256169639274165768735009 66942127229455624326551257)
    ·
      refine ⟨50206595422091718244913443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66942127229455624326551257 50206595422091718244913443)
      ·
        refine ⟨75309893133137577367370165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50206595422091718244913443 75309893133137577367370165)
        ·
          refine ⟨7060302481231647878190953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75309893133137577367370165 7060302481231647878190953)
          ·
            refine ⟨5295226860923735908643215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7060302481231647878190953 5295226860923735908643215)
            ·
              refine ⟨7942840291385603862964823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5295226860923735908643215 7942840291385603862964823)
              ·
                refine ⟨11914260437078405794447235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7942840291385603862964823 11914260437078405794447235)
                ·
                  refine ⟨17871390655617608691670853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11914260437078405794447235 17871390655617608691670853)
                  ·
                    refine ⟨3350885747928301629688285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17871390655617608691670853 3350885747928301629688285)
                    ·
                      refine ⟨1256582155473113111133107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3350885747928301629688285 1256582155473113111133107)
                      ·
                        rfl

theorem cell23_2447185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_2447185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447185 prefixEnd_2447185 := by exact prefixLift 2447185
  have htrace : WordTrace (prefixWord ++ tailWord_2447185) baseStart_2447185 baseEnd_2447185 := by
    simpa [prefixWord, tailWord_2447185, baseEnd_2447185] using wordTrace_append hprefix tailTrace_2447185
  have hstable : (prefixWord ++ tailWord_2447185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447185).length < 2 ^ (prefixWord ++ tailWord_2447185).sum := by decide
  have hdescent : baseEnd_2447185 < baseStart_2447185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447208 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_2447208 : Nat := 118140960795 + 2447208 * 2 ^ 59
def prefixEnd_2447208 : Nat := 4983230072969 + 3 ^ 40 * 2447208 * 2
def baseEnd_2447208 : Nat := 1256593965528166521145501

theorem tailTrace_2447208 : CollatzResearch.WordTrace tailWord_2447208 prefixEnd_2447208 1256593965528166521145501 := by
  unfold tailWord_2447208
  simp only [CollatzResearch.WordTrace]
  refine ⟨44628504259095420348411139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59504672345460560464548185 44628504259095420348411139)
  ·
    refine ⟨66942756388643130522616709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44628504259095420348411139 66942756388643130522616709)
    ·
      refine ⟨12551766822870586972990633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66942756388643130522616709 12551766822870586972990633)
      ·
        refine ⟨9413825117152940229742975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12551766822870586972990633 9413825117152940229742975)
        ·
          refine ⟨14120737675729410344614463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9413825117152940229742975 14120737675729410344614463)
          ·
            refine ⟨21181106513594115516921695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14120737675729410344614463 21181106513594115516921695)
            ·
              refine ⟨31771659770391173275382543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21181106513594115516921695 31771659770391173275382543)
              ·
                refine ⟨47657489655586759913073815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31771659770391173275382543 47657489655586759913073815)
                ·
                  refine ⟨71486234483380139869610723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47657489655586759913073815 71486234483380139869610723)
                  ·
                    refine ⟨107229351725070209804416085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71486234483380139869610723 107229351725070209804416085)
                    ·
                      refine ⟨1256593965528166521145501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 107229351725070209804416085 1256593965528166521145501)
                      ·
                        rfl

theorem cell23_2447208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_2447208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447208 prefixEnd_2447208 := by exact prefixLift 2447208
  have htrace : WordTrace (prefixWord ++ tailWord_2447208) baseStart_2447208 baseEnd_2447208 := by
    simpa [prefixWord, tailWord_2447208, baseEnd_2447208] using wordTrace_append hprefix tailTrace_2447208
  have hstable : (prefixWord ++ tailWord_2447208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447208).length < 2 ^ (prefixWord ++ tailWord_2447208).sum := by decide
  have hdescent : baseEnd_2447208 < baseStart_2447208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447225 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 3, 5, 2]
def baseStart_2447225 : Nat := 118140960795 + 2447225 * 2 ^ 59
def prefixEnd_2447225 : Nat := 4983230072969 + 3 ^ 40 * 2447225 * 2
def baseEnd_2447225 : Nat := 1256602694699292954632923

theorem tailTrace_2447225 : CollatzResearch.WordTrace tailWord_2447225 prefixEnd_2447225 1256602694699292954632923 := by
  unfold tailWord_2447225
  simp only [CollatzResearch.WordTrace]
  refine ⟨89257628559129252600191129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59505085706086168400127419 89257628559129252600191129)
  ·
    refine ⟨66943221419346939450143347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89257628559129252600191129 66943221419346939450143347)
    ·
      refine ⟨100414832129020409175215021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66943221419346939450143347 100414832129020409175215021)
      ·
        refine ⟨37655562048382653440705633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100414832129020409175215021 37655562048382653440705633)
        ·
          refine ⟨28241671536286990080529225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37655562048382653440705633 28241671536286990080529225)
          ·
            refine ⟨21181253652215242560396919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28241671536286990080529225 21181253652215242560396919)
            ·
              refine ⟨31771880478322863840595379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21181253652215242560396919 31771880478322863840595379)
              ·
                refine ⟨47657820717484295760893069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31771880478322863840595379 47657820717484295760893069)
                ·
                  refine ⟨17871682769056610910334901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47657820717484295760893069 17871682769056610910334901)
                  ·
                    refine ⟨1675470259599057272843897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17871682769056610910334901 1675470259599057272843897)
                    ·
                      refine ⟨1256602694699292954632923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1675470259599057272843897 1256602694699292954632923)
                      ·
                        rfl

theorem cell23_2447225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_2447225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447225 prefixEnd_2447225 := by exact prefixLift 2447225
  have htrace : WordTrace (prefixWord ++ tailWord_2447225) baseStart_2447225 baseEnd_2447225 := by
    simpa [prefixWord, tailWord_2447225, baseEnd_2447225] using wordTrace_append hprefix tailTrace_2447225
  have hstable : (prefixWord ++ tailWord_2447225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447225).length < 2 ^ (prefixWord ++ tailWord_2447225).sum := by decide
  have hdescent : baseEnd_2447225 < baseStart_2447225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447235 : List Nat := [1, 1, 1, 3, 4, 2, 1, 4, 1, 5]
def baseStart_2447235 : Nat := 118140960795 + 2447235 * 2 ^ 59
def prefixEnd_2447235 : Nat := 4983230072969 + 3 ^ 40 * 2447235 * 2
def baseEnd_2447235 : Nat := 418869276501945971835959

theorem tailTrace_2447235 : CollatzResearch.WordTrace tailWord_2447235 prefixEnd_2447235 418869276501945971835959 := by
  unfold tailWord_2447235
  simp only [CollatzResearch.WordTrace]
  refine ⟨89257993289093024308055159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59505328859395349538703439 89257993289093024308055159)
  ·
    refine ⟨133886989933639536462082739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89257993289093024308055159 133886989933639536462082739)
    ·
      refine ⟨200830484900459304693124109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133886989933639536462082739 200830484900459304693124109)
      ·
        refine ⟨75311431837672239259921541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200830484900459304693124109 75311431837672239259921541)
        ·
          refine ⟨14120893469563544861235289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75311431837672239259921541 14120893469563544861235289)
          ·
            refine ⟨10590670102172658645926467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14120893469563544861235289 10590670102172658645926467)
            ·
              refine ⟨15886005153258987968889701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10590670102172658645926467 15886005153258987968889701)
              ·
                refine ⟨2978625966236060244166819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15886005153258987968889701 2978625966236060244166819)
                ·
                  refine ⟨4467938949354090366250229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2978625966236060244166819 4467938949354090366250229)
                  ·
                    refine ⟨418869276501945971835959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4467938949354090366250229 418869276501945971835959)
                    ·
                      rfl

theorem cell23_2447235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 5].length) (baseStart_2447235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447235 prefixEnd_2447235 := by exact prefixLift 2447235
  have htrace : WordTrace (prefixWord ++ tailWord_2447235) baseStart_2447235 baseEnd_2447235 := by
    simpa [prefixWord, tailWord_2447235, baseEnd_2447235] using wordTrace_append hprefix tailTrace_2447235
  have hstable : (prefixWord ++ tailWord_2447235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447235).length < 2 ^ (prefixWord ++ tailWord_2447235).sum := by decide
  have hdescent : baseEnd_2447235 < baseStart_2447235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447249 : List Nat := [1, 2, 2, 1, 1, 1, 7, 3, 1, 1, 3]
def baseStart_2447249 : Nat := 118140960795 + 2447249 * 2 ^ 59
def prefixEnd_2447249 : Nat := 4983230072969 + 3 ^ 40 * 2447249 * 2
def baseEnd_2447249 : Nat := 1256615018235000860732813

theorem tailTrace_2447249 : CollatzResearch.WordTrace tailWord_2447249 prefixEnd_2447249 1256615018235000860732813 := by
  unfold tailWord_2447249
  simp only [CollatzResearch.WordTrace]
  refine ⟨89258503911042304699064801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59505669274028203132709867 89258503911042304699064801)
  ·
    refine ⟨66943877933281728524298601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89258503911042304699064801 66943877933281728524298601)
    ·
      refine ⟨50207908449961296393223951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66943877933281728524298601 50207908449961296393223951)
      ·
        refine ⟨75311862674941944589835927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50207908449961296393223951 75311862674941944589835927)
        ·
          refine ⟨112967794012412916884753891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75311862674941944589835927 112967794012412916884753891)
          ·
            refine ⟨169451691018619375327130837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112967794012412916884753891 169451691018619375327130837)
            ·
              refine ⟨3971524008248891609229629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 169451691018619375327130837 3971524008248891609229629)
              ·
                refine ⟨1489321503093334353461111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3971524008248891609229629 1489321503093334353461111)
                ·
                  refine ⟨2233982254640001530191667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1489321503093334353461111 2233982254640001530191667)
                  ·
                    refine ⟨3350973381960002295287501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2233982254640001530191667 3350973381960002295287501)
                    ·
                      refine ⟨1256615018235000860732813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3350973381960002295287501 1256615018235000860732813)
                      ·
                        rfl

theorem cell23_2447249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 1, 1, 3].length) (baseStart_2447249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447249 prefixEnd_2447249 := by exact prefixLift 2447249
  have htrace : WordTrace (prefixWord ++ tailWord_2447249) baseStart_2447249 baseEnd_2447249 := by
    simpa [prefixWord, tailWord_2447249, baseEnd_2447249] using wordTrace_append hprefix tailTrace_2447249
  have hstable : (prefixWord ++ tailWord_2447249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447249).length < 2 ^ (prefixWord ++ tailWord_2447249).sum := by decide
  have hdescent : baseEnd_2447249 < baseStart_2447249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447252 : List Nat := [2, 4, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_2447252 : Nat := 118140960795 + 2447252 * 2 ^ 59
def prefixEnd_2447252 : Nat := 4983230072969 + 3 ^ 40 * 2447252 * 2
def baseEnd_2447252 : Nat := 418872186225654782998433

theorem tailTrace_2447252 : CollatzResearch.WordTrace tailWord_2447252 prefixEnd_2447252 418872186225654782998433 := by
  unfold tailWord_2447252
  simp only [CollatzResearch.WordTrace]
  refine ⟨44629306665015718105712005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59505742220020957474282673 44629306665015718105712005)
  ·
    refine ⟨8367994999690447144821001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44629306665015718105712005 8367994999690447144821001)
    ·
      refine ⟨6275996249767835358615751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8367994999690447144821001 6275996249767835358615751)
      ·
        refine ⟨9413994374651753037923627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6275996249767835358615751 9413994374651753037923627)
        ·
          refine ⟨14120991561977629556885441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9413994374651753037923627 14120991561977629556885441)
          ·
            refine ⟨10590743671483222167664081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14120991561977629556885441 10590743671483222167664081)
            ·
              refine ⟨7943057753612416625748061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10590743671483222167664081 7943057753612416625748061)
              ·
                refine ⟨2978646657604656234655523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7943057753612416625748061 2978646657604656234655523)
                ·
                  refine ⟨4467969986406984351983285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2978646657604656234655523 4467969986406984351983285)
                  ·
                    refine ⟨418872186225654782998433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4467969986406984351983285 418872186225654782998433)
                    ·
                      rfl

theorem cell23_2447252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_2447252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447252 prefixEnd_2447252 := by exact prefixLift 2447252
  have htrace : WordTrace (prefixWord ++ tailWord_2447252) baseStart_2447252 baseEnd_2447252 := by
    simpa [prefixWord, tailWord_2447252, baseEnd_2447252] using wordTrace_append hprefix tailTrace_2447252
  have hstable : (prefixWord ++ tailWord_2447252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447252).length < 2 ^ (prefixWord ++ tailWord_2447252).sum := by decide
  have hdescent : baseEnd_2447252 < baseStart_2447252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447266 : List Nat := [3, 3, 1, 2, 3, 2, 1, 1, 3, 1, 3]
def baseStart_2447266 : Nat := 118140960795 + 2447266 * 2 ^ 59
def prefixEnd_2447266 : Nat := 4983230072969 + 3 ^ 40 * 2447266 * 2
def baseEnd_2447266 : Nat := 1256623747406127294220235

theorem tailTrace_2447266 : CollatzResearch.WordTrace tailWord_2447266 prefixEnd_2447266 1256623747406127294220235 := by
  unfold tailWord_2447266
  simp only [CollatzResearch.WordTrace]
  refine ⟨22314780987995179150608413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59506082634653811068289101 22314780987995179150608413)
  ·
    refine ⟨8368042870498192181478155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22314780987995179150608413 8368042870498192181478155)
    ·
      refine ⟨12552064305747288272217233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8368042870498192181478155 12552064305747288272217233)
      ·
        refine ⟨9414048229310466204162925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12552064305747288272217233 9414048229310466204162925)
        ·
          refine ⟨3530268085991424826561097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9414048229310466204162925 3530268085991424826561097)
          ·
            refine ⟨2647701064493568619920823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3530268085991424826561097 2647701064493568619920823)
            ·
              refine ⟨3971551596740352929881235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2647701064493568619920823 3971551596740352929881235)
              ·
                refine ⟨5957327395110529394821853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3971551596740352929881235 5957327395110529394821853)
                ·
                  refine ⟨2233997773166448523058195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5957327395110529394821853 2233997773166448523058195)
                  ·
                    refine ⟨3350996659749672784587293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2233997773166448523058195 3350996659749672784587293)
                    ·
                      refine ⟨1256623747406127294220235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3350996659749672784587293 1256623747406127294220235)
                      ·
                        rfl

theorem cell23_2447266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_2447266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447266 prefixEnd_2447266 := by exact prefixLift 2447266
  have htrace : WordTrace (prefixWord ++ tailWord_2447266) baseStart_2447266 baseEnd_2447266 := by
    simpa [prefixWord, tailWord_2447266, baseEnd_2447266] using wordTrace_append hprefix tailTrace_2447266
  have hstable : (prefixWord ++ tailWord_2447266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447266).length < 2 ^ (prefixWord ++ tailWord_2447266).sum := by decide
  have hdescent : baseEnd_2447266 < baseStart_2447266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447285 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 1, 1, 6]
def baseStart_2447285 : Nat := 118140960795 + 2447285 * 2 ^ 59
def prefixEnd_2447285 : Nat := 4983230072969 + 3 ^ 40 * 2447285 * 2
def baseEnd_2447285 : Nat := 1256633503538562719882647

theorem tailTrace_2447285 : CollatzResearch.WordTrace tailWord_2447285 prefixEnd_2447285 1256633503538562719882647 := by
  unfold tailWord_2447285
  simp only [CollatzResearch.WordTrace]
  refine ⟨89259816938911882847375309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59506544625941255231583539 89259816938911882847375309)
  ·
    refine ⟨33472431352091956067765741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89259816938911882847375309 33472431352091956067765741)
    ·
      refine ⟨12552161757034483525412153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33472431352091956067765741 12552161757034483525412153)
      ·
        refine ⟨9414121317775862644059115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12552161757034483525412153 9414121317775862644059115)
        ·
          refine ⟨14121181976663793966088673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9414121317775862644059115 14121181976663793966088673)
          ·
            refine ⟨10590886482497845474566505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14121181976663793966088673 10590886482497845474566505)
            ·
              refine ⟨7943164861873384105924879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10590886482497845474566505 7943164861873384105924879)
              ·
                refine ⟨11914747292810076158887319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7943164861873384105924879 11914747292810076158887319)
                ·
                  refine ⟨17872120939215114238330979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11914747292810076158887319 17872120939215114238330979)
                  ·
                    refine ⟨26808181408822671357496469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17872120939215114238330979 26808181408822671357496469)
                    ·
                      refine ⟨1256633503538562719882647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26808181408822671357496469 1256633503538562719882647)
                      ·
                        rfl

theorem cell23_2447285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_2447285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447285 prefixEnd_2447285 := by exact prefixLift 2447285
  have htrace : WordTrace (prefixWord ++ tailWord_2447285) baseStart_2447285 baseEnd_2447285 := by
    simpa [prefixWord, tailWord_2447285, baseEnd_2447285] using wordTrace_append hprefix tailTrace_2447285
  have hstable : (prefixWord ++ tailWord_2447285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447285).length < 2 ^ (prefixWord ++ tailWord_2447285).sum := by decide
  have hdescent : baseEnd_2447285 < baseStart_2447285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447305 : List Nat := [1, 2, 1, 1, 2, 1, 2, 6, 1, 3, 3]
def baseStart_2447305 : Nat := 118140960795 + 2447305 * 2 ^ 59
def prefixEnd_2447305 : Nat := 4983230072969 + 3 ^ 40 * 2447305 * 2
def baseEnd_2447305 : Nat := 1256643773151652641632555

theorem tailTrace_2447305 : CollatzResearch.WordTrace tailWord_2447305 prefixEnd_2447305 1256643773151652641632555 := by
  unfold tailWord_2447305
  simp only [CollatzResearch.WordTrace]
  refine ⟨89260546398839426263103369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59507030932559617508735579 89260546398839426263103369)
  ·
    refine ⟨66945409799129569697327527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89260546398839426263103369 66945409799129569697327527)
    ·
      refine ⟨100418114698694354545991291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66945409799129569697327527 100418114698694354545991291)
      ·
        refine ⟨150627172048041531818986937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100418114698694354545991291 150627172048041531818986937)
        ·
          refine ⟨112970379036031148864240203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150627172048041531818986937 112970379036031148864240203)
          ·
            refine ⟨169455568554046723296360305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112970379036031148864240203 169455568554046723296360305)
            ·
              refine ⟨127091676415535042472270229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169455568554046723296360305 127091676415535042472270229)
              ·
                refine ⟨5957422331978205115887667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 127091676415535042472270229 5957422331978205115887667)
                ·
                  refine ⟨8936133497967307673831501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5957422331978205115887667 8936133497967307673831501)
                  ·
                    refine ⟨3351050061737740377686813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8936133497967307673831501 3351050061737740377686813)
                    ·
                      refine ⟨1256643773151652641632555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3351050061737740377686813 1256643773151652641632555)
                      ·
                        rfl

theorem cell23_2447305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 3, 3].length) (baseStart_2447305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447305 prefixEnd_2447305 := by exact prefixLift 2447305
  have htrace : WordTrace (prefixWord ++ tailWord_2447305) baseStart_2447305 baseEnd_2447305 := by
    simpa [prefixWord, tailWord_2447305, baseEnd_2447305] using wordTrace_append hprefix tailTrace_2447305
  have hstable : (prefixWord ++ tailWord_2447305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447305).length < 2 ^ (prefixWord ++ tailWord_2447305).sum := by decide
  have hdescent : baseEnd_2447305 < baseStart_2447305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447332 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 5, 3, 2]
def baseStart_2447332 : Nat := 118140960795 + 2447332 * 2 ^ 59
def prefixEnd_2447332 : Nat := 4983230072969 + 3 ^ 40 * 2447332 * 2
def baseEnd_2447332 : Nat := 1256657637129324035994931

theorem tailTrace_2447332 : CollatzResearch.WordTrace tailWord_2447332 prefixEnd_2447332 1256657637129324035994931 := by
  unfold tailWord_2447332
  simp only [CollatzResearch.WordTrace]
  refine ⟨44630765584870804937168125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59507687446494406582890833 44630765584870804937168125)
  ·
    refine ⟨16736537094326551851438047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44630765584870804937168125 16736537094326551851438047)
    ·
      refine ⟨25104805641489827777157071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16736537094326551851438047 25104805641489827777157071)
      ·
        refine ⟨37657208462234741665735607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25104805641489827777157071 37657208462234741665735607)
        ·
          refine ⟨56485812693352112498603411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37657208462234741665735607 56485812693352112498603411)
          ·
            refine ⟨84728719040028168747905117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56485812693352112498603411 84728719040028168747905117)
            ·
              refine ⟨31773269640010563280464419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84728719040028168747905117 31773269640010563280464419)
              ·
                refine ⟨47659904460015844920696629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31773269640010563280464419 47659904460015844920696629)
                ·
                  refine ⟨4468116043126485461315309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47659904460015844920696629 4468116043126485461315309)
                  ·
                    refine ⟨1675543516172432047993241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4468116043126485461315309 1675543516172432047993241)
                    ·
                      refine ⟨1256657637129324035994931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1675543516172432047993241 1256657637129324035994931)
                      ·
                        rfl

theorem cell23_2447332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_2447332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447332 prefixEnd_2447332 := by exact prefixLift 2447332
  have htrace : WordTrace (prefixWord ++ tailWord_2447332) baseStart_2447332 baseEnd_2447332 := by
    simpa [prefixWord, tailWord_2447332, baseEnd_2447332] using wordTrace_append hprefix tailTrace_2447332
  have hstable : (prefixWord ++ tailWord_2447332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447332).length < 2 ^ (prefixWord ++ tailWord_2447332).sum := by decide
  have hdescent : baseEnd_2447332 < baseStart_2447332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447402 : List Nat := [3, 1, 4, 1, 2, 1, 2, 2, 7]
def baseStart_2447402 : Nat := 118140960795 + 2447402 * 2 ^ 59
def prefixEnd_2447402 : Nat := 4983230072969 + 3 ^ 40 * 2447402 * 2
def baseEnd_2447402 : Nat := 139632620086126529124401

theorem tailTrace_2447402 : CollatzResearch.WordTrace tailWord_2447402 prefixEnd_2447402 139632620086126529124401 := by
  unfold tailWord_2447402
  simp only [CollatzResearch.WordTrace]
  refine ⟨22316021069872002957346115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59509389519658674552922973 22316021069872002957346115)
  ·
    refine ⟨33474031604808004436019173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22316021069872002957346115 33474031604808004436019173)
    ·
      refine ⟨6276380925901500831753595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33474031604808004436019173 6276380925901500831753595)
      ·
        refine ⟨9414571388852251247630393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6276380925901500831753595 9414571388852251247630393)
        ·
          refine ⟨7060928541639188435722795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9414571388852251247630393 7060928541639188435722795)
          ·
            refine ⟨10591392812458782653584193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7060928541639188435722795 10591392812458782653584193)
            ·
              refine ⟨7943544609344086990188145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10591392812458782653584193 7943544609344086990188145)
              ·
                refine ⟨5957658457008065242641109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7943544609344086990188145 5957658457008065242641109)
                ·
                  refine ⟨139632620086126529124401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5957658457008065242641109 139632620086126529124401)
                  ·
                    rfl

theorem cell23_2447402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 7].length) (baseStart_2447402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447402 prefixEnd_2447402 := by exact prefixLift 2447402
  have htrace : WordTrace (prefixWord ++ tailWord_2447402) baseStart_2447402 baseEnd_2447402 := by
    simpa [prefixWord, tailWord_2447402, baseEnd_2447402] using wordTrace_append hprefix tailTrace_2447402
  have hstable : (prefixWord ++ tailWord_2447402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447402).length < 2 ^ (prefixWord ++ tailWord_2447402).sum := by decide
  have hdescent : baseEnd_2447402 < baseStart_2447402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447415 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 1, 7]
def baseStart_2447415 : Nat := 118140960795 + 2447415 * 2 ^ 59
def prefixEnd_2447415 : Nat := 4983230072969 + 3 ^ 40 * 2447415 * 2
def baseEnd_2447415 : Nat := 418900085341215737085683

theorem tailTrace_2447415 : CollatzResearch.WordTrace tailWord_2447415 prefixEnd_2447415 418900085341215737085683 := by
  unfold tailWord_2447415
  simp only [CollatzResearch.WordTrace]
  refine ⟨89264558428440915049607699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59509705618960610033071799 89264558428440915049607699)
  ·
    refine ⟨133896837642661372574411549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89264558428440915049607699 133896837642661372574411549)
    ·
      refine ⟨50211314115998014715404331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133896837642661372574411549 50211314115998014715404331)
      ·
        refine ⟨75316971173997022073106497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50211314115998014715404331 75316971173997022073106497)
        ·
          refine ⟨56487728380497766554829873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75316971173997022073106497 56487728380497766554829873)
          ·
            refine ⟨42365796285373324916122405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56487728380497766554829873 42365796285373324916122405)
            ·
              refine ⟨7943586803507498421772951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42365796285373324916122405 7943586803507498421772951)
              ·
                refine ⟨11915380205261247632659427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7943586803507498421772951 11915380205261247632659427)
                ·
                  refine ⟨17873070307891871448989141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11915380205261247632659427 17873070307891871448989141)
                  ·
                    refine ⟨418900085341215737085683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17873070307891871448989141 418900085341215737085683)
                    ·
                      rfl

theorem cell23_2447415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_2447415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447415 prefixEnd_2447415 := by exact prefixLift 2447415
  have htrace : WordTrace (prefixWord ++ tailWord_2447415) baseStart_2447415 baseEnd_2447415 := by
    simpa [prefixWord, tailWord_2447415, baseEnd_2447415] using wordTrace_append hprefix tailTrace_2447415
  have hstable : (prefixWord ++ tailWord_2447415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447415).length < 2 ^ (prefixWord ++ tailWord_2447415).sum := by decide
  have hdescent : baseEnd_2447415 < baseStart_2447415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447469 : List Nat := [1, 5, 1, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_2447469 : Nat := 118140960795 + 2447469 * 2 ^ 59
def prefixEnd_2447469 : Nat := 4983230072969 + 3 ^ 40 * 2447469 * 2
def baseEnd_2447469 : Nat := 1256727983978989999981801

theorem tailTrace_2447469 : CollatzResearch.WordTrace tailWord_2447469 prefixEnd_2447469 1256727983978989999981801 := by
  unfold tailWord_2447469
  simp only [CollatzResearch.WordTrace]
  refine ⟨89266527970245282272073461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59511018646830188181382307 89266527970245282272073461)
  ·
    refine ⟨8368736997210495213006887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89266527970245282272073461 8368736997210495213006887)
    ·
      refine ⟨12553105495815742819510331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8368736997210495213006887 12553105495815742819510331)
      ·
        refine ⟨18829658243723614229265497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12553105495815742819510331 18829658243723614229265497)
        ·
          refine ⟨14122243682792710671949123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18829658243723614229265497 14122243682792710671949123)
          ·
            refine ⟨21183365524189066007923685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14122243682792710671949123 21183365524189066007923685)
            ·
              refine ⟨3971881035785449876485691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21183365524189066007923685 3971881035785449876485691)
              ·
                refine ⟨5957821553678174814728537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3971881035785449876485691 5957821553678174814728537)
                ·
                  refine ⟨4468366165258631111046403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5957821553678174814728537 4468366165258631111046403)
                  ·
                    refine ⟨6702549247887946666569605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4468366165258631111046403 6702549247887946666569605)
                    ·
                      refine ⟨1256727983978989999981801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6702549247887946666569605 1256727983978989999981801)
                      ·
                        rfl

theorem cell23_2447469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_2447469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447469 prefixEnd_2447469 := by exact prefixLift 2447469
  have htrace : WordTrace (prefixWord ++ tailWord_2447469) baseStart_2447469 baseEnd_2447469 := by
    simpa [prefixWord, tailWord_2447469, baseEnd_2447469] using wordTrace_append hprefix tailTrace_2447469
  have hstable : (prefixWord ++ tailWord_2447469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447469).length < 2 ^ (prefixWord ++ tailWord_2447469).sum := by decide
  have hdescent : baseEnd_2447469 < baseStart_2447469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447515 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 7]
def baseStart_2447515 : Nat := 118140960795 + 2447515 * 2 ^ 59
def prefixEnd_2447515 : Nat := 4983230072969 + 3 ^ 40 * 2447515 * 2
def baseEnd_2447515 : Nat := 1256751604089096820006589

theorem tailTrace_2447515 : CollatzResearch.WordTrace tailWord_2447515 prefixEnd_2447515 1256751604089096820006589 := by
  unfold tailWord_2447515
  simp only [CollatzResearch.WordTrace]
  refine ⟨89268205728078632128247999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59512137152052421418831999 89268205728078632128247999)
  ·
    refine ⟨133902308592117948192371999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89268205728078632128247999 133902308592117948192371999)
    ·
      refine ⟨200853462888176922288557999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133902308592117948192371999 200853462888176922288557999)
      ·
        refine ⟨301280194332265383432836999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200853462888176922288557999 301280194332265383432836999)
        ·
          refine ⟨451920291498398075149255499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301280194332265383432836999 451920291498398075149255499)
          ·
            refine ⟨677880437247597112723883249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451920291498398075149255499 677880437247597112723883249)
            ·
              refine ⟨508410327935697834542912437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677880437247597112723883249 508410327935697834542912437)
              ·
                refine ⟨47663468243971671988398041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 508410327935697834542912437 47663468243971671988398041)
                ·
                  refine ⟨35747601182978753991298531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47663468243971671988398041 35747601182978753991298531)
                  ·
                    refine ⟨53621401774468130986947797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35747601182978753991298531 53621401774468130986947797)
                    ·
                      refine ⟨1256751604089096820006589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53621401774468130986947797 1256751604089096820006589)
                      ·
                        rfl

theorem cell23_2447515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 7].length) (baseStart_2447515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447515 prefixEnd_2447515 := by exact prefixLift 2447515
  have htrace : WordTrace (prefixWord ++ tailWord_2447515) baseStart_2447515 baseEnd_2447515 := by
    simpa [prefixWord, tailWord_2447515, baseEnd_2447515] using wordTrace_append hprefix tailTrace_2447515
  have hstable : (prefixWord ++ tailWord_2447515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447515).length < 2 ^ (prefixWord ++ tailWord_2447515).sum := by decide
  have hdescent : baseEnd_2447515 < baseStart_2447515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447530 : List Nat := [3, 1, 5, 1, 2, 1, 2, 3, 1, 4]
def baseStart_2447530 : Nat := 118140960795 + 2447530 * 2 ^ 59
def prefixEnd_2447530 : Nat := 4983230072969 + 3 ^ 40 * 2447530 * 2
def baseEnd_2447530 : Nat := 418919768766304753773007

theorem tailTrace_2447530 : CollatzResearch.WordTrace tailWord_2447530 prefixEnd_2447530 418919768766304753773007 := by
  unfold tailWord_2447530
  simp only [CollatzResearch.WordTrace]
  refine ⟨22317188205756072422511011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59512501882016193126696029 22317188205756072422511011)
  ·
    refine ⟨33475782308634108633766517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22317188205756072422511011 33475782308634108633766517)
    ·
      refine ⟨3138354591434447684415611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33475782308634108633766517 3138354591434447684415611)
      ·
        refine ⟨4707531887151671526623417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3138354591434447684415611 4707531887151671526623417)
        ·
          refine ⟨3530648915363753644967563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4707531887151671526623417 3530648915363753644967563)
          ·
            refine ⟨5295973373045630467451345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3530648915363753644967563 5295973373045630467451345)
            ·
              refine ⟨3971980029784222850588509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5295973373045630467451345 3971980029784222850588509)
              ·
                refine ⟨1489492511169083568970691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3971980029784222850588509 1489492511169083568970691)
                ·
                  refine ⟨2234238766753625353456037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1489492511169083568970691 2234238766753625353456037)
                  ·
                    refine ⟨418919768766304753773007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2234238766753625353456037 418919768766304753773007)
                    ·
                      rfl

theorem cell23_2447530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_2447530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447530 prefixEnd_2447530 := by exact prefixLift 2447530
  have htrace : WordTrace (prefixWord ++ tailWord_2447530) baseStart_2447530 baseEnd_2447530 := by
    simpa [prefixWord, tailWord_2447530, baseEnd_2447530] using wordTrace_append hprefix tailTrace_2447530
  have hstable : (prefixWord ++ tailWord_2447530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447530).length < 2 ^ (prefixWord ++ tailWord_2447530).sum := by decide
  have hdescent : baseEnd_2447530 < baseStart_2447530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447569 : List Nat := [1, 2, 2, 1, 2, 2, 2, 5, 2, 4]
def baseStart_2447569 : Nat := 118140960795 + 2447569 * 2 ^ 59
def prefixEnd_2447569 : Nat := 4983230072969 + 3 ^ 40 * 2447569 * 2
def baseEnd_2447569 : Nat := 418926444014813202910447

theorem tailTrace_2447569 : CollatzResearch.WordTrace tailWord_2447569 prefixEnd_2447569 418926444014813202910447 := by
  unfold tailWord_2447569
  simp only [CollatzResearch.WordTrace]
  refine ⟨89270175269882999350713761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59513450179921999567142507 89270175269882999350713761)
  ·
    refine ⟨66952631452412249513035321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89270175269882999350713761 66952631452412249513035321)
    ·
      refine ⟨50214473589309187134776491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66952631452412249513035321 50214473589309187134776491)
      ·
        refine ⟨75321710383963780702164737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50214473589309187134776491 75321710383963780702164737)
        ·
          refine ⟨56491282787972835526623553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75321710383963780702164737 56491282787972835526623553)
          ·
            refine ⟨42368462090979626644967665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56491282787972835526623553 42368462090979626644967665)
            ·
              refine ⟨31776346568234719983725749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42368462090979626644967665 31776346568234719983725749)
              ·
                refine ⟨2979032490772004998474289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31776346568234719983725749 2979032490772004998474289)
                ·
                  refine ⟨2234274368079003748855717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2979032490772004998474289 2234274368079003748855717)
                  ·
                    refine ⟨418926444014813202910447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2234274368079003748855717 418926444014813202910447)
                    ·
                      rfl

theorem cell23_2447569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_2447569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447569 prefixEnd_2447569 := by exact prefixLift 2447569
  have htrace : WordTrace (prefixWord ++ tailWord_2447569) baseStart_2447569 baseEnd_2447569 := by
    simpa [prefixWord, tailWord_2447569, baseEnd_2447569] using wordTrace_append hprefix tailTrace_2447569
  have hstable : (prefixWord ++ tailWord_2447569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447569).length < 2 ^ (prefixWord ++ tailWord_2447569).sum := by decide
  have hdescent : baseEnd_2447569 < baseStart_2447569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447576 : List Nat := [2, 1, 2, 2, 4, 2, 2, 2, 1, 1, 4]
def baseStart_2447576 : Nat := 118140960795 + 2447576 * 2 ^ 59
def prefixEnd_2447576 : Nat := 4983230072969 + 3 ^ 40 * 2447576 * 2
def baseEnd_2447576 : Nat := 1256782926409021081343809

theorem tailTrace_2447576 : CollatzResearch.WordTrace tailWord_2447576 prefixEnd_2447576 1256782926409021081343809 := by
  unfold tailWord_2447576
  simp only [CollatzResearch.WordTrace]
  refine ⟨44635215290428819773109291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59513620387238426364145721 44635215290428819773109291)
  ·
    refine ⟨66952822935643229659663937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44635215290428819773109291 66952822935643229659663937)
    ·
      refine ⟨50214617201732422244747953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66952822935643229659663937 50214617201732422244747953)
      ·
        refine ⟨37660962901299316683560965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50214617201732422244747953 37660962901299316683560965)
        ·
          refine ⟨7061430543993621878167681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37660962901299316683560965 7061430543993621878167681)
          ·
            refine ⟨5296072907995216408625761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7061430543993621878167681 5296072907995216408625761)
            ·
              refine ⟨3972054680996412306469321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5296072907995216408625761 3972054680996412306469321)
              ·
                refine ⟨2979041010747309229851991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3972054680996412306469321 2979041010747309229851991)
                ·
                  refine ⟨4468561516120963844777987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2979041010747309229851991 4468561516120963844777987)
                  ·
                    refine ⟨6702842274181445767166981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4468561516120963844777987 6702842274181445767166981)
                    ·
                      refine ⟨1256782926409021081343809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6702842274181445767166981 1256782926409021081343809)
                      ·
                        rfl

theorem cell23_2447576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_2447576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447576 prefixEnd_2447576 := by exact prefixLift 2447576
  have htrace : WordTrace (prefixWord ++ tailWord_2447576) baseStart_2447576 baseEnd_2447576 := by
    simpa [prefixWord, tailWord_2447576, baseEnd_2447576] using wordTrace_append hprefix tailTrace_2447576
  have hstable : (prefixWord ++ tailWord_2447576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447576).length < 2 ^ (prefixWord ++ tailWord_2447576).sum := by decide
  have hdescent : baseEnd_2447576 < baseStart_2447576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447579 : List Nat := [1, 1, 1, 1, 1, 1, 1, 10, 1, 2, 3]
def baseStart_2447579 : Nat := 118140960795 + 2447579 * 2 ^ 59
def prefixEnd_2447579 : Nat := 4983230072969 + 3 ^ 40 * 2447579 * 2
def baseEnd_2447579 : Nat := 1256784466850984569606295

theorem tailTrace_2447579 : CollatzResearch.WordTrace tailWord_2447579 prefixEnd_2447579 1256784466850984569606295 := by
  unfold tailWord_2447579
  simp only [CollatzResearch.WordTrace]
  refine ⟨89270539999846771058577791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59513693333231180705718527 89270539999846771058577791)
  ·
    refine ⟨133905809999770156587866687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89270539999846771058577791 133905809999770156587866687)
    ·
      refine ⟨200858714999655234881800031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133905809999770156587866687 200858714999655234881800031)
      ·
        refine ⟨301288072499482852322700047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200858714999655234881800031 301288072499482852322700047)
        ·
          refine ⟨451932108749224278484050071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301288072499482852322700047 451932108749224278484050071)
          ·
            refine ⟨677898163123836417726075107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451932108749224278484050071 677898163123836417726075107)
            ·
              refine ⟨1016847244685754626589112661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677898163123836417726075107 1016847244685754626589112661)
              ·
                refine ⟨2979044662165296757585291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1016847244685754626589112661 2979044662165296757585291)
                ·
                  refine ⟨4468566993247945136377937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2979044662165296757585291 4468566993247945136377937)
                  ·
                    refine ⟨3351425244935958852283453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4468566993247945136377937 3351425244935958852283453)
                    ·
                      refine ⟨1256784466850984569606295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3351425244935958852283453 1256784466850984569606295)
                      ·
                        rfl

theorem cell23_2447579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 2, 3].length) (baseStart_2447579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447579 prefixEnd_2447579 := by exact prefixLift 2447579
  have htrace : WordTrace (prefixWord ++ tailWord_2447579) baseStart_2447579 baseEnd_2447579 := by
    simpa [prefixWord, tailWord_2447579, baseEnd_2447579] using wordTrace_append hprefix tailTrace_2447579
  have hstable : (prefixWord ++ tailWord_2447579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447579).length < 2 ^ (prefixWord ++ tailWord_2447579).sum := by decide
  have hdescent : baseEnd_2447579 < baseStart_2447579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447587 : List Nat := [1, 1, 1, 8, 1, 2, 1, 3, 1, 1, 3]
def baseStart_2447587 : Nat := 118140960795 + 2447587 * 2 ^ 59
def prefixEnd_2447587 : Nat := 4983230072969 + 3 ^ 40 * 2447587 * 2
def baseEnd_2447587 : Nat := 1256788574696220538306259

theorem tailTrace_2447587 : CollatzResearch.WordTrace tailWord_2447587 prefixEnd_2447587 1256788574696220538306259 := by
  unfold tailWord_2447587
  simp only [CollatzResearch.WordTrace]
  refine ⟨89270831783817788424869015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59513887855878525616579343 89270831783817788424869015)
  ·
    refine ⟨133906247675726682637303523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89270831783817788424869015 133906247675726682637303523)
    ·
      refine ⟨200859371513590023955955285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133906247675726682637303523 200859371513590023955955285)
      ·
        refine ⟨2353820759924883093233851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 200859371513590023955955285 2353820759924883093233851)
        ·
          refine ⟨3530731139887324639850777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353820759924883093233851 3530731139887324639850777)
          ·
            refine ⟨2648048354915493479888083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3530731139887324639850777 2648048354915493479888083)
            ·
              refine ⟨3972072532373240219832125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2648048354915493479888083 3972072532373240219832125)
              ·
                refine ⟨1489527199639965082437047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3972072532373240219832125 1489527199639965082437047)
                ·
                  refine ⟨2234290799459947623655571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1489527199639965082437047 2234290799459947623655571)
                  ·
                    refine ⟨3351436199189921435483357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2234290799459947623655571 3351436199189921435483357)
                    ·
                      refine ⟨1256788574696220538306259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3351436199189921435483357 1256788574696220538306259)
                      ·
                        rfl

theorem cell23_2447587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_2447587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447587 prefixEnd_2447587 := by exact prefixLift 2447587
  have htrace : WordTrace (prefixWord ++ tailWord_2447587) baseStart_2447587 baseEnd_2447587 := by
    simpa [prefixWord, tailWord_2447587, baseEnd_2447587] using wordTrace_append hprefix tailTrace_2447587
  have hstable : (prefixWord ++ tailWord_2447587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447587).length < 2 ^ (prefixWord ++ tailWord_2447587).sum := by decide
  have hdescent : baseEnd_2447587 < baseStart_2447587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447620 : List Nat := [2, 3, 2, 2, 3, 2, 2, 1, 2, 4]
def baseStart_2447620 : Nat := 118140960795 + 2447620 * 2 ^ 59
def prefixEnd_2447620 : Nat := 4983230072969 + 3 ^ 40 * 2447620 * 2
def baseEnd_2447620 : Nat := 418935173185939636397869

theorem tailTrace_2447620 : CollatzResearch.WordTrace tailWord_2447620 prefixEnd_2447620 418935173185939636397869 := by
  unfold tailWord_2447620
  simp only [CollatzResearch.WordTrace]
  refine ⟨44636017696349117530410157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59514690261798823373880209 44636017696349117530410157)
  ·
    refine ⟨16738506636130919073903809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44636017696349117530410157 16738506636130919073903809)
    ·
      refine ⟨12553879977098189305427857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16738506636130919073903809 12553879977098189305427857)
      ·
        refine ⟨9415409982823641979070893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12553879977098189305427857 9415409982823641979070893)
        ·
          refine ⟨3530778743558865742151585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9415409982823641979070893 3530778743558865742151585)
          ·
            refine ⟨2648084057669149306613689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3530778743558865742151585 2648084057669149306613689)
            ·
              refine ⟨1986063043251861979960267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2648084057669149306613689 1986063043251861979960267)
              ·
                refine ⟨2979094564877792969940401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1986063043251861979960267 2979094564877792969940401)
                ·
                  refine ⟨2234320923658344727455301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2979094564877792969940401 2234320923658344727455301)
                  ·
                    refine ⟨418935173185939636397869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2234320923658344727455301 418935173185939636397869)
                    ·
                      rfl

theorem cell23_2447620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_2447620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447620 prefixEnd_2447620 := by exact prefixLift 2447620
  have htrace : WordTrace (prefixWord ++ tailWord_2447620) baseStart_2447620 baseEnd_2447620 := by
    simpa [prefixWord, tailWord_2447620, baseEnd_2447620] using wordTrace_append hprefix tailTrace_2447620
  have hstable : (prefixWord ++ tailWord_2447620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447620).length < 2 ^ (prefixWord ++ tailWord_2447620).sum := by decide
  have hdescent : baseEnd_2447620 < baseStart_2447620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447661 : List Nat := [1, 5, 3, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_2447661 : Nat := 118140960795 + 2447661 * 2 ^ 59
def prefixEnd_2447661 : Nat := 4983230072969 + 3 ^ 40 * 2447661 * 2
def baseEnd_2447661 : Nat := 1256826572264653248780919

theorem tailTrace_2447661 : CollatzResearch.WordTrace tailWord_2447661 prefixEnd_2447661 1256826572264653248780919 := by
  unfold tailWord_2447661
  simp only [CollatzResearch.WordTrace]
  refine ⟨89273530785549699063062837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59515687190366466042041891 89273530785549699063062837)
  ·
    refine ⟨8369393511145284287162141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89273530785549699063062837 8369393511145284287162141)
    ·
      refine ⟨3138522566679481607685803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8369393511145284287162141 3138522566679481607685803)
      ·
        refine ⟨4707783850019222411528705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3138522566679481607685803 4707783850019222411528705)
        ·
          refine ⟨3530837887514416808646529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4707783850019222411528705 3530837887514416808646529)
          ·
            refine ⟨2648128415635812606484897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3530837887514416808646529 2648128415635812606484897)
            ·
              refine ⟨1986096311726859454863673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2648128415635812606484897 1986096311726859454863673)
              ·
                refine ⟨1489572233795144591147755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1986096311726859454863673 1489572233795144591147755)
                ·
                  refine ⟨2234358350692716886721633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1489572233795144591147755 2234358350692716886721633)
                  ·
                    refine ⟨1675768763019537665041225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2234358350692716886721633 1675768763019537665041225)
                    ·
                      refine ⟨1256826572264653248780919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1675768763019537665041225 1256826572264653248780919)
                      ·
                        rfl

theorem cell23_2447661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_2447661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447661 prefixEnd_2447661 := by exact prefixLift 2447661
  have htrace : WordTrace (prefixWord ++ tailWord_2447661) baseStart_2447661 baseEnd_2447661 := by
    simpa [prefixWord, tailWord_2447661, baseEnd_2447661] using wordTrace_append hprefix tailTrace_2447661
  have hstable : (prefixWord ++ tailWord_2447661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447661).length < 2 ^ (prefixWord ++ tailWord_2447661).sum := by decide
  have hdescent : baseEnd_2447661 < baseStart_2447661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447669 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 1, 6, 3]
def baseStart_2447669 : Nat := 118140960795 + 2447669 * 2 ^ 59
def prefixEnd_2447669 : Nat := 4983230072969 + 3 ^ 40 * 2447669 * 2
def baseEnd_2447669 : Nat := 1256830680109889217480881

theorem tailTrace_2447669 : CollatzResearch.WordTrace tailWord_2447669 prefixEnd_2447669 1256830680109889217480881 := by
  unfold tailWord_2447669
  simp only [CollatzResearch.WordTrace]
  refine ⟨89273822569520716429354061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59515881713013810952902707 89273822569520716429354061)
  ·
    refine ⟨33477683463570268661007773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89273822569520716429354061 33477683463570268661007773)
    ·
      refine ⟨12554131298838850747877915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33477683463570268661007773 12554131298838850747877915)
      ·
        refine ⟨18831196948258276121816873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12554131298838850747877915 18831196948258276121816873)
        ·
          refine ⟨14123397711193707091362655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18831196948258276121816873 14123397711193707091362655)
          ·
            refine ⟨21185096566790560637043983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14123397711193707091362655 21185096566790560637043983)
            ·
              refine ⟨31777644850185840955565975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21185096566790560637043983 31777644850185840955565975)
              ·
                refine ⟨47666467275278761433348963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31777644850185840955565975 47666467275278761433348963)
                ·
                  refine ⟨71499700912918142150023445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47666467275278761433348963 71499700912918142150023445)
                  ·
                    refine ⟨3351548480293037913282349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71499700912918142150023445 3351548480293037913282349)
                    ·
                      refine ⟨1256830680109889217480881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3351548480293037913282349 1256830680109889217480881)
                      ·
                        rfl

theorem cell23_2447669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_2447669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447669 prefixEnd_2447669 := by exact prefixLift 2447669
  have htrace : WordTrace (prefixWord ++ tailWord_2447669) baseStart_2447669 baseEnd_2447669 := by
    simpa [prefixWord, tailWord_2447669, baseEnd_2447669] using wordTrace_append hprefix tailTrace_2447669
  have hstable : (prefixWord ++ tailWord_2447669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447669).length < 2 ^ (prefixWord ++ tailWord_2447669).sum := by decide
  have hdescent : baseEnd_2447669 < baseStart_2447669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447679 : List Nat := [1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 4]
def baseStart_2447679 : Nat := 118140960795 + 2447679 * 2 ^ 59
def prefixEnd_2447679 : Nat := 4983230072969 + 3 ^ 40 * 2447679 * 2
def baseEnd_2447679 : Nat := 1256835814916434178355835

theorem tailTrace_2447679 : CollatzResearch.WordTrace tailWord_2447679 prefixEnd_2447679 1256835814916434178355835 := by
  unfold tailWord_2447679
  simp only [CollatzResearch.WordTrace]
  refine ⟨89274187299484488137218091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59516124866322992091478727 89274187299484488137218091)
  ·
    refine ⟨133911280949226732205827137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89274187299484488137218091 133911280949226732205827137)
    ·
      refine ⟨100433460711920049154370353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133911280949226732205827137 100433460711920049154370353)
      ·
        refine ⟨75325095533940036865777765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100433460711920049154370353 75325095533940036865777765)
        ·
          refine ⟨14123455412613756912333331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75325095533940036865777765 14123455412613756912333331)
          ·
            refine ⟨21185183118920635368499997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14123455412613756912333331 21185183118920635368499997)
            ·
              refine ⟨7944443669595238263187499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21185183118920635368499997 7944443669595238263187499)
              ·
                refine ⟨11916665504392857394781249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7944443669595238263187499 11916665504392857394781249)
                ·
                  refine ⟨8937499128294643046085937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11916665504392857394781249 8937499128294643046085937)
                  ·
                    refine ⟨6703124346220982284564453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8937499128294643046085937 6703124346220982284564453)
                    ·
                      refine ⟨1256835814916434178355835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6703124346220982284564453 1256835814916434178355835)
                      ·
                        rfl

theorem cell23_2447679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_2447679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447679 prefixEnd_2447679 := by exact prefixLift 2447679
  have htrace : WordTrace (prefixWord ++ tailWord_2447679) baseStart_2447679 baseEnd_2447679 := by
    simpa [prefixWord, tailWord_2447679, baseEnd_2447679] using wordTrace_append hprefix tailTrace_2447679
  have hstable : (prefixWord ++ tailWord_2447679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447679).length < 2 ^ (prefixWord ++ tailWord_2447679).sum := by decide
  have hdescent : baseEnd_2447679 < baseStart_2447679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447683 : List Nat := [1, 1, 1, 3, 1, 3, 4, 3, 2, 2, 2]
def baseStart_2447683 : Nat := 118140960795 + 2447683 * 2 ^ 59
def prefixEnd_2447683 : Nat := 4983230072969 + 3 ^ 40 * 2447683 * 2
def baseEnd_2447683 : Nat := 1256837868839052162705817

theorem tailTrace_2447683 : CollatzResearch.WordTrace tailWord_2447683 prefixEnd_2447683 1256837868839052162705817 := by
  unfold tailWord_2447683
  simp only [CollatzResearch.WordTrace]
  refine ⟨89274333191469996820363703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59516222127646664546909135 89274333191469996820363703)
  ·
    refine ⟨133911499787204995230545555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89274333191469996820363703 133911499787204995230545555)
    ·
      refine ⟨200867249680807492845818333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133911499787204995230545555 200867249680807492845818333)
      ·
        refine ⟨75325218630302809817181875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200867249680807492845818333 75325218630302809817181875)
        ·
          refine ⟨112987827945454214725772813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75325218630302809817181875 112987827945454214725772813)
          ·
            refine ⟨42370435479545330522164805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112987827945454214725772813 42370435479545330522164805)
            ·
              refine ⟨7944456652414749472905901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42370435479545330522164805 7944456652414749472905901)
              ·
                refine ⟨2979171244655531052339713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7944456652414749472905901 2979171244655531052339713)
                ·
                  refine ⟨2234378433491648289254785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2979171244655531052339713 2234378433491648289254785)
                  ·
                    refine ⟨1675783825118736216941089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2234378433491648289254785 1675783825118736216941089)
                    ·
                      refine ⟨1256837868839052162705817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1675783825118736216941089 1256837868839052162705817)
                      ·
                        rfl

theorem cell23_2447683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 2, 2].length) (baseStart_2447683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447683 prefixEnd_2447683 := by exact prefixLift 2447683
  have htrace : WordTrace (prefixWord ++ tailWord_2447683) baseStart_2447683 baseEnd_2447683 := by
    simpa [prefixWord, tailWord_2447683, baseEnd_2447683] using wordTrace_append hprefix tailTrace_2447683
  have hstable : (prefixWord ++ tailWord_2447683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447683).length < 2 ^ (prefixWord ++ tailWord_2447683).sum := by decide
  have hdescent : baseEnd_2447683 < baseStart_2447683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447734 : List Nat := [5, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2]
def baseStart_2447734 : Nat := 118140960795 + 2447734 * 2 ^ 59
def prefixEnd_2447734 : Nat := 4983230072969 + 3 ^ 40 * 2447734 * 2
def baseEnd_2447734 : Nat := 1256864056352431463168083

theorem tailTrace_2447734 : CollatzResearch.WordTrace tailWord_2447734 prefixEnd_2447734 1256864056352431463168083 := by
  unfold tailWord_2447734
  simp only [CollatzResearch.WordTrace]
  refine ⟨5579762082142827033154391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59517462209523488353646837 5579762082142827033154391)
  ·
    refine ⟨8369643123214240549731587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5579762082142827033154391 8369643123214240549731587)
    ·
      refine ⟨12554464684821360824597381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8369643123214240549731587 12554464684821360824597381)
      ·
        refine ⟨2353962128404005154612009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12554464684821360824597381 2353962128404005154612009)
        ·
          refine ⟨1765471596303003865959007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2353962128404005154612009 1765471596303003865959007)
          ·
            refine ⟨2648207394454505798938511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1765471596303003865959007 2648207394454505798938511)
            ·
              refine ⟨3972311091681758698407767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2648207394454505798938511 3972311091681758698407767)
              ·
                refine ⟨5958466637522638047611651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3972311091681758698407767 5958466637522638047611651)
                ·
                  refine ⟨8937699956283957071417477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5958466637522638047611651 8937699956283957071417477)
                  ·
                    refine ⟨1675818741803241950890777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8937699956283957071417477 1675818741803241950890777)
                    ·
                      refine ⟨1256864056352431463168083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1675818741803241950890777 1256864056352431463168083)
                      ·
                        rfl

theorem cell23_2447734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_2447734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447734 prefixEnd_2447734 := by exact prefixLift 2447734
  have htrace : WordTrace (prefixWord ++ tailWord_2447734) baseStart_2447734 baseEnd_2447734 := by
    simpa [prefixWord, tailWord_2447734, baseEnd_2447734] using wordTrace_append hprefix tailTrace_2447734
  have hstable : (prefixWord ++ tailWord_2447734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447734).length < 2 ^ (prefixWord ++ tailWord_2447734).sum := by decide
  have hdescent : baseEnd_2447734 < baseStart_2447734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447739 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 4]
def baseStart_2447739 : Nat := 118140960795 + 2447739 * 2 ^ 59
def prefixEnd_2447739 : Nat := 4983230072969 + 3 ^ 40 * 2447739 * 2
def baseEnd_2447739 : Nat := 1256866623755703943605559

theorem tailTrace_2447739 : CollatzResearch.WordTrace tailWord_2447739 prefixEnd_2447739 1256866623755703943605559 := by
  unfold tailWord_2447739
  simp only [CollatzResearch.WordTrace]
  refine ⟨89276375679267118384402271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59517583786178078922934847 89276375679267118384402271)
  ·
    refine ⟨133914563518900677576603407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89276375679267118384402271 133914563518900677576603407)
    ·
      refine ⟨200871845278351016364905111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133914563518900677576603407 200871845278351016364905111)
      ·
        refine ⟨301307767917526524547357667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200871845278351016364905111 301307767917526524547357667)
        ·
          refine ⟨451961651876289786821036501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301307767917526524547357667 451961651876289786821036501)
          ·
            refine ⟨10592851215850541878618043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 451961651876289786821036501 10592851215850541878618043)
            ·
              refine ⟨15889276823775812817927065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10592851215850541878618043 15889276823775812817927065)
              ·
                refine ⟨11916957617831859613445299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15889276823775812817927065 11916957617831859613445299)
                ·
                  refine ⟨17875436426747789420167949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11916957617831859613445299 17875436426747789420167949)
                  ·
                    refine ⟨6703288660030421032562981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17875436426747789420167949 6703288660030421032562981)
                    ·
                      refine ⟨1256866623755703943605559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6703288660030421032562981 1256866623755703943605559)
                      ·
                        rfl

theorem cell23_2447739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 4].length) (baseStart_2447739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447739 prefixEnd_2447739 := by exact prefixLift 2447739
  have htrace : WordTrace (prefixWord ++ tailWord_2447739) baseStart_2447739 baseEnd_2447739 := by
    simpa [prefixWord, tailWord_2447739, baseEnd_2447739] using wordTrace_append hprefix tailTrace_2447739
  have hstable : (prefixWord ++ tailWord_2447739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447739).length < 2 ^ (prefixWord ++ tailWord_2447739).sum := by decide
  have hdescent : baseEnd_2447739 < baseStart_2447739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447773 : List Nat := [1, 4, 2, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_2447773 : Nat := 118140960795 + 2447773 * 2 ^ 59
def prefixEnd_2447773 : Nat := 4983230072969 + 3 ^ 40 * 2447773 * 2
def baseEnd_2447773 : Nat := 1256884082097956810580403

theorem tailTrace_2447773 : CollatzResearch.WordTrace tailWord_2447773 prefixEnd_2447773 1256884082097956810580403 := by
  unfold tailWord_2447773
  simp only [CollatzResearch.WordTrace]
  refine ⟨89277615761143942191139973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59518410507429294794093315 89277615761143942191139973)
  ·
    refine ⟨16739552955214489160838745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89277615761143942191139973 16739552955214489160838745)
    ·
      refine ⟨12554664716410866870629059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16739552955214489160838745 12554664716410866870629059)
      ·
        refine ⟨18831997074616300305943589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12554664716410866870629059 18831997074616300305943589)
        ·
          refine ⟨3530999451490556307364423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18831997074616300305943589 3530999451490556307364423)
          ·
            refine ⟨5296499177235834461046635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3530999451490556307364423 5296499177235834461046635)
            ·
              refine ⟨7944748765853751691569953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5296499177235834461046635 7944748765853751691569953)
              ·
                refine ⟨5958561574390313768677465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7944748765853751691569953 5958561574390313768677465)
                ·
                  refine ⟨4468921180792735326508099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5958561574390313768677465 4468921180792735326508099)
                  ·
                    refine ⟨6703381771189102989762149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4468921180792735326508099 6703381771189102989762149)
                    ·
                      refine ⟨1256884082097956810580403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6703381771189102989762149 1256884082097956810580403)
                      ·
                        rfl

theorem cell23_2447773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_2447773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447773 prefixEnd_2447773 := by exact prefixLift 2447773
  have htrace : WordTrace (prefixWord ++ tailWord_2447773) baseStart_2447773 baseEnd_2447773 := by
    simpa [prefixWord, tailWord_2447773, baseEnd_2447773] using wordTrace_append hprefix tailTrace_2447773
  have hstable : (prefixWord ++ tailWord_2447773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447773).length < 2 ^ (prefixWord ++ tailWord_2447773).sum := by decide
  have hdescent : baseEnd_2447773 < baseStart_2447773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447776 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 3]
def baseStart_2447776 : Nat := 118140960795 + 2447776 * 2 ^ 59
def prefixEnd_2447776 : Nat := 4983230072969 + 3 ^ 40 * 2447776 * 2
def baseEnd_2447776 : Nat := 1256885622539920298842889

theorem tailTrace_2447776 : CollatzResearch.WordTrace tailWord_2447776 prefixEnd_2447776 1256885622539920298842889 := by
  unfold tailWord_2447776
  simp only [CollatzResearch.WordTrace]
  refine ⟨44638862590066536851749591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59518483453422049135666121 44638862590066536851749591)
  ·
    refine ⟨66958293885099805277624387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44638862590066536851749591 66958293885099805277624387)
    ·
      refine ⟨100437440827649707916436581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66958293885099805277624387 100437440827649707916436581)
      ·
        refine ⟨18832020155184320234331859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100437440827649707916436581 18832020155184320234331859)
        ·
          refine ⟨28248030232776480351497789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18832020155184320234331859 28248030232776480351497789)
          ·
            refine ⟨10593011337291180131811671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28248030232776480351497789 10593011337291180131811671)
            ·
              refine ⟨15889517005936770197717507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10593011337291180131811671 15889517005936770197717507)
              ·
                refine ⟨23834275508905155296576261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15889517005936770197717507 23834275508905155296576261)
                ·
                  refine ⟨4468926657919716618108049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23834275508905155296576261 4468926657919716618108049)
                  ·
                    refine ⟨3351694993439787463581037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4468926657919716618108049 3351694993439787463581037)
                    ·
                      refine ⟨1256885622539920298842889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3351694993439787463581037 1256885622539920298842889)
                      ·
                        rfl

theorem cell23_2447776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_2447776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447776 prefixEnd_2447776 := by exact prefixLift 2447776
  have htrace : WordTrace (prefixWord ++ tailWord_2447776) baseStart_2447776 baseEnd_2447776 := by
    simpa [prefixWord, tailWord_2447776, baseEnd_2447776] using wordTrace_append hprefix tailTrace_2447776
  have hstable : (prefixWord ++ tailWord_2447776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447776).length < 2 ^ (prefixWord ++ tailWord_2447776).sum := by decide
  have hdescent : baseEnd_2447776 < baseStart_2447776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447779 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 8]
def baseStart_2447779 : Nat := 118140960795 + 2447779 * 2 ^ 59
def prefixEnd_2447779 : Nat := 4983230072969 + 3 ^ 40 * 2447779 * 2
def baseEnd_2447779 : Nat := 139654129220209309678375

theorem tailTrace_2447779 : CollatzResearch.WordTrace tailWord_2447779 prefixEnd_2447779 139654129220209309678375 := by
  unfold tailWord_2447779
  simp only [CollatzResearch.WordTrace]
  refine ⟨89277834599122205215858391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59518556399414803477238927 89277834599122205215858391)
  ·
    refine ⟨133916751898683307823787587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89277834599122205215858391 133916751898683307823787587)
    ·
      refine ⟨200875127848024961735681381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133916751898683307823787587 200875127848024961735681381)
      ·
        refine ⟨37664086471504680325440259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200875127848024961735681381 37664086471504680325440259)
        ·
          refine ⟨56496129707257020488160389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37664086471504680325440259 56496129707257020488160389)
          ·
            refine ⟨10593024320110691341530073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56496129707257020488160389 10593024320110691341530073)
            ·
              refine ⟨7944768240083018506147555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10593024320110691341530073 7944768240083018506147555)
              ·
                refine ⟨11917152360124527759221333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7944768240083018506147555 11917152360124527759221333)
                ·
                  refine ⟨139654129220209309678375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11917152360124527759221333 139654129220209309678375)
                  ·
                    rfl

theorem cell23_2447779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 8].length) (baseStart_2447779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447779 prefixEnd_2447779 := by exact prefixLift 2447779
  have htrace : WordTrace (prefixWord ++ tailWord_2447779) baseStart_2447779 baseEnd_2447779 := by
    simpa [prefixWord, tailWord_2447779, baseEnd_2447779] using wordTrace_append hprefix tailTrace_2447779
  have hstable : (prefixWord ++ tailWord_2447779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447779).length < 2 ^ (prefixWord ++ tailWord_2447779).sum := by decide
  have hdescent : baseEnd_2447779 < baseStart_2447779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447783 : List Nat := [1, 1, 6, 1, 1, 2, 3, 1, 3, 4]
def baseStart_2447783 : Nat := 118140960795 + 2447783 * 2 ^ 59
def prefixEnd_2447783 : Nat := 4983230072969 + 3 ^ 40 * 2447783 * 2
def baseEnd_2447783 : Nat := 418963072301500590485119

theorem tailTrace_2447783 : CollatzResearch.WordTrace tailWord_2447783 prefixEnd_2447783 418963072301500590485119 := by
  unfold tailWord_2447783
  simp only [CollatzResearch.WordTrace]
  refine ⟨89277980491107713899004003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59518653660738475932669335 89277980491107713899004003)
  ·
    refine ⟨133916970736661570848506005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89277980491107713899004003 133916970736661570848506005)
    ·
      refine ⟨6277358003281011133523719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 133916970736661570848506005 6277358003281011133523719)
      ·
        refine ⟨9416037004921516700285579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6277358003281011133523719 9416037004921516700285579)
        ·
          refine ⟨14124055507382275050428369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9416037004921516700285579 14124055507382275050428369)
          ·
            refine ⟨10593041630536706287821277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14124055507382275050428369 10593041630536706287821277)
            ·
              refine ⟨3972390611451264857932979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10593041630536706287821277 3972390611451264857932979)
              ·
                refine ⟨5958585917176897286899469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3972390611451264857932979 5958585917176897286899469)
                ·
                  refine ⟨2234469718941336482587301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5958585917176897286899469 2234469718941336482587301)
                  ·
                    refine ⟨418963072301500590485119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2234469718941336482587301 418963072301500590485119)
                    ·
                      rfl

theorem cell23_2447783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_2447783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447783 prefixEnd_2447783 := by exact prefixLift 2447783
  have htrace : WordTrace (prefixWord ++ tailWord_2447783) baseStart_2447783 baseEnd_2447783 := by
    simpa [prefixWord, tailWord_2447783, baseEnd_2447783] using wordTrace_append hprefix tailTrace_2447783
  have hstable : (prefixWord ++ tailWord_2447783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447783).length < 2 ^ (prefixWord ++ tailWord_2447783).sum := by decide
  have hdescent : baseEnd_2447783 < baseStart_2447783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447806 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_2447806 : Nat := 118140960795 + 2447806 * 2 ^ 59
def prefixEnd_2447806 : Nat := 4983230072969 + 3 ^ 40 * 2447806 * 2
def baseEnd_2447806 : Nat := 1256901026959555181467751

theorem tailTrace_2447806 : CollatzResearch.WordTrace tailWord_2447806 prefixEnd_2447806 1256901026959555181467751 := by
  unfold tailWord_2447806
  simp only [CollatzResearch.WordTrace]
  refine ⟨11159852421253048603386409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59519212913349592551394181 11159852421253048603386409)
  ·
    refine ⟨8369889315939786452539807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11159852421253048603386409 8369889315939786452539807)
    ·
      refine ⟨12554833973909679678809711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8369889315939786452539807 12554833973909679678809711)
      ·
        refine ⟨18832250960864519518214567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12554833973909679678809711 18832250960864519518214567)
        ·
          refine ⟨28248376441296779277321851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18832250960864519518214567 28248376441296779277321851)
          ·
            refine ⟨42372564661945168915982777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28248376441296779277321851 42372564661945168915982777)
            ·
              refine ⟨31779423496458876686987083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42372564661945168915982777 31779423496458876686987083)
              ·
                refine ⟨47669135244688315030480625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31779423496458876686987083 47669135244688315030480625)
                ·
                  refine ⟨35751851433516236272860469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47669135244688315030480625 35751851433516236272860469)
                  ·
                    refine ⟨3351736071892147150580669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35751851433516236272860469 3351736071892147150580669)
                    ·
                      refine ⟨1256901026959555181467751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3351736071892147150580669 1256901026959555181467751)
                      ·
                        rfl

theorem cell23_2447806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_2447806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447806 prefixEnd_2447806 := by exact prefixLift 2447806
  have htrace : WordTrace (prefixWord ++ tailWord_2447806) baseStart_2447806 baseEnd_2447806 := by
    simpa [prefixWord, tailWord_2447806, baseEnd_2447806] using wordTrace_append hprefix tailTrace_2447806
  have hstable : (prefixWord ++ tailWord_2447806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447806).length < 2 ^ (prefixWord ++ tailWord_2447806).sum := by decide
  have hdescent : baseEnd_2447806 < baseStart_2447806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447833 : List Nat := [1, 2, 1, 2, 4, 1, 1, 4, 2, 3, 2]
def baseStart_2447833 : Nat := 118140960795 + 2447833 * 2 ^ 59
def prefixEnd_2447833 : Nat := 4983230072969 + 3 ^ 40 * 2447833 * 2
def baseEnd_2447833 : Nat := 1256914890937226575830127

theorem tailTrace_2447833 : CollatzResearch.WordTrace tailWord_2447833 prefixEnd_2447833 1256914890937226575830127 := by
  unfold tailWord_2447833
  simp only [CollatzResearch.WordTrace]
  refine ⟨89279804140926572438324153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59519869427284381625549435 89279804140926572438324153)
  ·
    refine ⟨66959853105694929328743115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89279804140926572438324153 66959853105694929328743115)
    ·
      refine ⟨100439779658542393993114673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66959853105694929328743115 100439779658542393993114673)
      ·
        refine ⟨75329834743906795494836005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100439779658542393993114673 75329834743906795494836005)
        ·
          refine ⟨14124344014482524155281751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75329834743906795494836005 14124344014482524155281751)
          ·
            refine ⟨21186516021723786232922627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14124344014482524155281751 21186516021723786232922627)
            ·
              refine ⟨31779774032585679349383941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21186516021723786232922627 31779774032585679349383941)
              ·
                refine ⟨5958707631109814878009489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31779774032585679349383941 5958707631109814878009489)
                ·
                  refine ⟨4469030723332361158507117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5958707631109814878009489 4469030723332361158507117)
                  ·
                    refine ⟨1675886521249635434440169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4469030723332361158507117 1675886521249635434440169)
                    ·
                      refine ⟨1256914890937226575830127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1675886521249635434440169 1256914890937226575830127)
                      ·
                        rfl

theorem cell23_2447833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 3, 2].length) (baseStart_2447833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447833 prefixEnd_2447833 := by exact prefixLift 2447833
  have htrace : WordTrace (prefixWord ++ tailWord_2447833) baseStart_2447833 baseEnd_2447833 := by
    simpa [prefixWord, tailWord_2447833, baseEnd_2447833] using wordTrace_append hprefix tailTrace_2447833
  have hstable : (prefixWord ++ tailWord_2447833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447833).length < 2 ^ (prefixWord ++ tailWord_2447833).sum := by decide
  have hdescent : baseEnd_2447833 < baseStart_2447833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447840 : List Nat := [2, 1, 1, 3, 1, 1, 5, 4, 1, 1, 3]
def baseStart_2447840 : Nat := 118140960795 + 2447840 * 2 ^ 59
def prefixEnd_2447840 : Nat := 4983230072969 + 3 ^ 40 * 2447840 * 2
def baseEnd_2447840 : Nat := 1256918485301808048442595

theorem tailTrace_2447840 : CollatzResearch.WordTrace tailWord_2447840 prefixEnd_2447840 1256918485301808048442595 := by
  unfold tailWord_2447840
  simp only [CollatzResearch.WordTrace]
  refine ⟨44640029725950606316914487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59520039634600808422552649 44640029725950606316914487)
  ·
    refine ⟨66960044588925909475371731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44640029725950606316914487 66960044588925909475371731)
    ·
      refine ⟨100440066883388864213057597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66960044588925909475371731 100440066883388864213057597)
      ·
        refine ⟨37665025081270824079896599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100440066883388864213057597 37665025081270824079896599)
        ·
          refine ⟨56497537621906236119844899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37665025081270824079896599 56497537621906236119844899)
          ·
            refine ⟨84746306432859354179767349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56497537621906236119844899 84746306432859354179767349)
            ·
              refine ⟨7944966228080564454353189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84746306432859354179767349 7944966228080564454353189)
              ·
                refine ⟨1489681167765105835191223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7944966228080564454353189 1489681167765105835191223)
                ·
                  refine ⟨2234521751647658752786835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1489681167765105835191223 2234521751647658752786835)
                  ·
                    refine ⟨3351782627471488129180253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2234521751647658752786835 3351782627471488129180253)
                    ·
                      refine ⟨1256918485301808048442595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3351782627471488129180253 1256918485301808048442595)
                      ·
                        rfl

theorem cell23_2447840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 1, 1, 3].length) (baseStart_2447840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447840 prefixEnd_2447840 := by exact prefixLift 2447840
  have htrace : WordTrace (prefixWord ++ tailWord_2447840) baseStart_2447840 baseEnd_2447840 := by
    simpa [prefixWord, tailWord_2447840, baseEnd_2447840] using wordTrace_append hprefix tailTrace_2447840
  have hstable : (prefixWord ++ tailWord_2447840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447840).length < 2 ^ (prefixWord ++ tailWord_2447840).sum := by decide
  have hdescent : baseEnd_2447840 < baseStart_2447840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447856 : List Nat := [2, 1, 1, 1, 3, 3, 4, 1, 1, 6]
def baseStart_2447856 : Nat := 118140960795 + 2447856 * 2 ^ 59
def prefixEnd_2447856 : Nat := 4983230072969 + 3 ^ 40 * 2447856 * 2
def baseEnd_2447856 : Nat := 418975566997426661947507

theorem tailTrace_2447856 : CollatzResearch.WordTrace tailWord_2447856 prefixEnd_2447856 418975566997426661947507 := by
  unfold tailWord_2447856
  simp only [CollatzResearch.WordTrace]
  refine ⟨44640321509921623683205711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59520428679895498244274281 44640321509921623683205711)
  ·
    refine ⟨66960482264882435524808567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44640321509921623683205711 66960482264882435524808567)
    ·
      refine ⟨100440723397323653287212851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66960482264882435524808567 100440723397323653287212851)
      ·
        refine ⟨150661085095985479930819277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100440723397323653287212851 150661085095985479930819277)
        ·
          refine ⟨56497906910994554974057229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150661085095985479930819277 56497906910994554974057229)
          ·
            refine ⟨21186715091622958115271461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56497906910994554974057229 21186715091622958115271461)
            ·
              refine ⟨3972509079679304646613399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21186715091622958115271461 3972509079679304646613399)
              ·
                refine ⟨5958763619518956969920099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3972509079679304646613399 5958763619518956969920099)
                ·
                  refine ⟨8938145429278435454880149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5958763619518956969920099 8938145429278435454880149)
                  ·
                    refine ⟨418975566997426661947507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8938145429278435454880149 418975566997426661947507)
                    ·
                      rfl

theorem cell23_2447856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 4, 1, 1, 6].length) (baseStart_2447856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447856 prefixEnd_2447856 := by exact prefixLift 2447856
  have htrace : WordTrace (prefixWord ++ tailWord_2447856) baseStart_2447856 baseEnd_2447856 := by
    simpa [prefixWord, tailWord_2447856, baseEnd_2447856] using wordTrace_append hprefix tailTrace_2447856
  have hstable : (prefixWord ++ tailWord_2447856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447856).length < 2 ^ (prefixWord ++ tailWord_2447856).sum := by decide
  have hdescent : baseEnd_2447856 < baseStart_2447856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2447886 : List Nat := [4, 1, 1, 2, 3, 2, 10]
def baseStart_2447886 : Nat := 118140960795 + 2447886 * 2 ^ 59
def prefixEnd_2447886 : Nat := 4983230072969 + 3 ^ 40 * 2447886 * 2
def baseEnd_2447886 : Nat := 15517803770517467511943

theorem tailTrace_2447886 : CollatzResearch.WordTrace tailWord_2447886 prefixEnd_2447886 15517803770517467511943 := by
  unfold tailWord_2447886
  simp only [CollatzResearch.WordTrace]
  refine ⟨11160217151216820311250439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59521158139823041660002341 11160217151216820311250439)
  ·
    refine ⟨16740325726825230466875659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11160217151216820311250439 16740325726825230466875659)
    ·
      refine ⟨25110488590237845700313489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16740325726825230466875659 25110488590237845700313489)
      ·
        refine ⟨18832866442678384275235117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25110488590237845700313489 18832866442678384275235117)
        ·
          refine ⟨7062324916004394103213169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18832866442678384275235117 7062324916004394103213169)
          ·
            refine ⟨5296743687003295577409877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7062324916004394103213169 5296743687003295577409877)
            ·
              refine ⟨15517803770517467511943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5296743687003295577409877 15517803770517467511943)
              ·
                rfl

theorem cell23_2447886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 10].length) (baseStart_2447886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2447886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2447886 prefixEnd_2447886 := by exact prefixLift 2447886
  have htrace : WordTrace (prefixWord ++ tailWord_2447886) baseStart_2447886 baseEnd_2447886 := by
    simpa [prefixWord, tailWord_2447886, baseEnd_2447886] using wordTrace_append hprefix tailTrace_2447886
  have hstable : (prefixWord ++ tailWord_2447886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2447886).length < 2 ^ (prefixWord ++ tailWord_2447886).sum := by decide
  have hdescent : baseEnd_2447886 < baseStart_2447886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2447886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448004 : List Nat := [2, 3, 2, 1, 3, 2, 2, 2, 2, 2, 2]
def baseStart_2448004 : Nat := 118140960795 + 2448004 * 2 ^ 59
def prefixEnd_2448004 : Nat := 4983230072969 + 3 ^ 40 * 2448004 * 2
def baseEnd_2448004 : Nat := 1257002696129145406791841

theorem tailTrace_2448004 : CollatzResearch.WordTrace tailWord_2448004 prefixEnd_2448004 1257002696129145406791841 := by
  unfold tailWord_2448004
  simp only [CollatzResearch.WordTrace]
  refine ⟨44643020511653534321399533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59524027348871379095199377 44643020511653534321399533)
  ·
    refine ⟨16741132691870075370524825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44643020511653534321399533 16741132691870075370524825)
    ·
      refine ⟨12555849518902556527893619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16741132691870075370524825 12555849518902556527893619)
      ·
        refine ⟨18833774278353834791840429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12555849518902556527893619 18833774278353834791840429)
        ·
          refine ⟨7062665354382688046940161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18833774278353834791840429 7062665354382688046940161)
          ·
            refine ⟨5296999015787016035205121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7062665354382688046940161 5296999015787016035205121)
            ·
              refine ⟨3972749261840262026403841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5296999015787016035205121 3972749261840262026403841)
              ·
                refine ⟨2979561946380196519802881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3972749261840262026403841 2979561946380196519802881)
                ·
                  refine ⟨2234671459785147389852161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2979561946380196519802881 2234671459785147389852161)
                  ·
                    refine ⟨1676003594838860542389121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2234671459785147389852161 1676003594838860542389121)
                    ·
                      refine ⟨1257002696129145406791841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1676003594838860542389121 1257002696129145406791841)
                      ·
                        rfl

theorem cell23_2448004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_2448004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448004 prefixEnd_2448004 := by exact prefixLift 2448004
  have htrace : WordTrace (prefixWord ++ tailWord_2448004) baseStart_2448004 baseEnd_2448004 := by
    simpa [prefixWord, tailWord_2448004, baseEnd_2448004] using wordTrace_append hprefix tailTrace_2448004
  have hstable : (prefixWord ++ tailWord_2448004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448004).length < 2 ^ (prefixWord ++ tailWord_2448004).sum := by decide
  have hdescent : baseEnd_2448004 < baseStart_2448004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448020 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_2448020 : Nat := 118140960795 + 2448020 * 2 ^ 59
def prefixEnd_2448020 : Nat := 4983230072969 + 3 ^ 40 * 2448020 * 2
def baseEnd_2448020 : Nat := 1257010911819617344191767

theorem tailTrace_2448020 : CollatzResearch.WordTrace tailWord_2448020 prefixEnd_2448020 1257010911819617344191767 := by
  unfold tailWord_2448020
  simp only [CollatzResearch.WordTrace]
  refine ⟨44643312295624551687690757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59524416394166068916921009 44643312295624551687690757)
  ·
    refine ⟨8370621055429603441442017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44643312295624551687690757 8370621055429603441442017)
    ·
      refine ⟨6277965791572202581081513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8370621055429603441442017 6277965791572202581081513)
      ·
        refine ⟨4708474343679151935811135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6277965791572202581081513 4708474343679151935811135)
        ·
          refine ⟨7062711515518727903716703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4708474343679151935811135 7062711515518727903716703)
          ·
            refine ⟨10594067273278091855575055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7062711515518727903716703 10594067273278091855575055)
            ·
              refine ⟨15891100909917137783362583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10594067273278091855575055 15891100909917137783362583)
              ·
                refine ⟨23836651364875706675043875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15891100909917137783362583 23836651364875706675043875)
                ·
                  refine ⟨35754977047313560012565813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23836651364875706675043875 35754977047313560012565813)
                  ·
                    refine ⟨3352029098185646251178045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35754977047313560012565813 3352029098185646251178045)
                    ·
                      refine ⟨1257010911819617344191767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3352029098185646251178045 1257010911819617344191767)
                      ·
                        rfl

theorem cell23_2448020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_2448020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448020 prefixEnd_2448020 := by exact prefixLift 2448020
  have htrace : WordTrace (prefixWord ++ tailWord_2448020) baseStart_2448020 baseEnd_2448020 := by
    simpa [prefixWord, tailWord_2448020, baseEnd_2448020] using wordTrace_append hprefix tailTrace_2448020
  have hstable : (prefixWord ++ tailWord_2448020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448020).length < 2 ^ (prefixWord ++ tailWord_2448020).sum := by decide
  have hdescent : baseEnd_2448020 < baseStart_2448020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448060 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 4, 4, 2]
def baseStart_2448060 : Nat := 118140960795 + 2448060 * 2 ^ 59
def prefixEnd_2448060 : Nat := 4983230072969 + 3 ^ 40 * 2448060 * 2
def baseEnd_2448060 : Nat := 1257031451045797187691583

theorem tailTrace_2448060 : CollatzResearch.WordTrace tailWord_2448060 prefixEnd_2448060 1257031451045797187691583 := by
  unfold tailWord_2448060
  simp only [CollatzResearch.WordTrace]
  refine ⟨44644041755552095103418817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59525389007402793471225089 44644041755552095103418817)
  ·
    refine ⟨33483031316664071327564113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44644041755552095103418817 33483031316664071327564113)
    ·
      refine ⟨25112273487498053495673085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33483031316664071327564113 25112273487498053495673085)
      ·
        refine ⟨9417102557811770060877407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25112273487498053495673085 9417102557811770060877407)
        ·
          refine ⟨14125653836717655091316111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9417102557811770060877407 14125653836717655091316111)
          ·
            refine ⟨21188480755076482636974167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14125653836717655091316111 21188480755076482636974167)
            ·
              refine ⟨31782721132614723955461251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21188480755076482636974167 31782721132614723955461251)
              ·
                refine ⟨47674081698922085933191877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31782721132614723955461251 47674081698922085933191877)
                ·
                  refine ⟨8938890318547891112473477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47674081698922085933191877 8938890318547891112473477)
                  ·
                    refine ⟨1676041934727729583588777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8938890318547891112473477 1676041934727729583588777)
                    ·
                      refine ⟨1257031451045797187691583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1676041934727729583588777 1257031451045797187691583)
                      ·
                        rfl

theorem cell23_2448060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_2448060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448060 prefixEnd_2448060 := by exact prefixLift 2448060
  have htrace : WordTrace (prefixWord ++ tailWord_2448060) baseStart_2448060 baseEnd_2448060 := by
    simpa [prefixWord, tailWord_2448060, baseEnd_2448060] using wordTrace_append hprefix tailTrace_2448060
  have hstable : (prefixWord ++ tailWord_2448060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448060).length < 2 ^ (prefixWord ++ tailWord_2448060).sum := by decide
  have hdescent : baseEnd_2448060 < baseStart_2448060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448143 : List Nat := [1, 1, 2, 1, 1, 1, 6, 3, 1, 6]
def baseStart_2448143 : Nat := 118140960795 + 2448143 * 2 ^ 59
def prefixEnd_2448143 : Nat := 4983230072969 + 3 ^ 40 * 2448143 * 2
def baseEnd_2448143 : Nat := 419024689980040120984567

theorem tailTrace_2448143 : CollatzResearch.WordTrace tailWord_2448143 prefixEnd_2448143 419024689980040120984567 := by
  unfold tailWord_2448143
  simp only [CollatzResearch.WordTrace]
  refine ⟨89291110769803495382109083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59527407179868996921406055 89291110769803495382109083)
  ·
    refine ⟨133936666154705243073163625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89291110769803495382109083 133936666154705243073163625)
    ·
      refine ⟨100452499616028932304872719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133936666154705243073163625 100452499616028932304872719)
      ·
        refine ⟨150678749424043398457309079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100452499616028932304872719 150678749424043398457309079)
        ·
          refine ⟨226018124136065097685963619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150678749424043398457309079 226018124136065097685963619)
          ·
            refine ⟨339027186204097646528945429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226018124136065097685963619 339027186204097646528945429)
            ·
              refine ⟨15891899353317077181044317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 339027186204097646528945429 15891899353317077181044317)
              ·
                refine ⟨5959462257493903942891619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15891899353317077181044317 5959462257493903942891619)
                ·
                  refine ⟨8939193386240855914337429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5959462257493903942891619 8939193386240855914337429)
                  ·
                    refine ⟨419024689980040120984567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8939193386240855914337429 419024689980040120984567)
                    ·
                      rfl

theorem cell23_2448143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 6].length) (baseStart_2448143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448143 prefixEnd_2448143 := by exact prefixLift 2448143
  have htrace : WordTrace (prefixWord ++ tailWord_2448143) baseStart_2448143 baseEnd_2448143 := by
    simpa [prefixWord, tailWord_2448143, baseEnd_2448143] using wordTrace_append hprefix tailTrace_2448143
  have hstable : (prefixWord ++ tailWord_2448143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448143).length < 2 ^ (prefixWord ++ tailWord_2448143).sum := by decide
  have hdescent : baseEnd_2448143 < baseStart_2448143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448160 : List Nat := [2, 1, 1, 5, 1, 3, 1, 2, 1, 6]
def baseStart_2448160 : Nat := 118140960795 + 2448160 * 2 ^ 59
def prefixEnd_2448160 : Nat := 4983230072969 + 3 ^ 40 * 2448160 * 2
def baseEnd_2448160 : Nat := 419027599703748932147041

theorem tailTrace_2448160 : CollatzResearch.WordTrace tailWord_2448160 prefixEnd_2448160 419027599703748932147041 := by
  unfold tailWord_2448160
  simp only [CollatzResearch.WordTrace]
  refine ⟨44645865405370953642738967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59527820540494604856985289 44645865405370953642738967)
  ·
    refine ⟨66968798108056430464108451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44645865405370953642738967 66968798108056430464108451)
    ·
      refine ⟨100453197162084645696162677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66968798108056430464108451 100453197162084645696162677)
      ·
        refine ⟨9417487233945435534015251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100453197162084645696162677 9417487233945435534015251)
        ·
          refine ⟨14126230850918153301022877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9417487233945435534015251 14126230850918153301022877)
          ·
            refine ⟨5297336569094307487883579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14126230850918153301022877 5297336569094307487883579)
            ·
              refine ⟨7946004853641461231825369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5297336569094307487883579 7946004853641461231825369)
              ·
                refine ⟨5959503640231095923869027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7946004853641461231825369 5959503640231095923869027)
                ·
                  refine ⟨8939255460346643885803541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5959503640231095923869027 8939255460346643885803541)
                  ·
                    refine ⟨419027599703748932147041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8939255460346643885803541 419027599703748932147041)
                    ·
                      rfl

theorem cell23_2448160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 2, 1, 6].length) (baseStart_2448160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448160 prefixEnd_2448160 := by exact prefixLift 2448160
  have htrace : WordTrace (prefixWord ++ tailWord_2448160) baseStart_2448160 baseEnd_2448160 := by
    simpa [prefixWord, tailWord_2448160, baseEnd_2448160] using wordTrace_append hprefix tailTrace_2448160
  have hstable : (prefixWord ++ tailWord_2448160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448160).length < 2 ^ (prefixWord ++ tailWord_2448160).sum := by decide
  have hdescent : baseEnd_2448160 < baseStart_2448160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448164 : List Nat := [2, 3, 1, 3, 3, 1, 3, 1, 1, 5]
def baseStart_2448164 : Nat := 118140960795 + 2448164 * 2 ^ 59
def prefixEnd_2448164 : Nat := 4983230072969 + 3 ^ 40 * 2448164 * 2
def baseEnd_2448164 : Nat := 419028284344621593597035

theorem tailTrace_2448164 : CollatzResearch.WordTrace tailWord_2448164 prefixEnd_2448164 419028284344621593597035 := by
  unfold tailWord_2448164
  simp only [CollatzResearch.WordTrace]
  refine ⟨44645938351363707984311773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59527917801818277312415697 44645938351363707984311773)
  ·
    refine ⟨16742226881761390494116915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44645938351363707984311773 16742226881761390494116915)
    ·
      refine ⟨25113340322642085741175373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16742226881761390494116915 25113340322642085741175373)
      ·
        refine ⟨9417502620990782152940765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25113340322642085741175373 9417502620990782152940765)
        ·
          refine ⟨3531563482871543307352787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9417502620990782152940765 3531563482871543307352787)
          ·
            refine ⟨5297345224307314961029181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3531563482871543307352787 5297345224307314961029181)
            ·
              refine ⟨1986504459115243110385943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5297345224307314961029181 1986504459115243110385943)
              ·
                refine ⟨2979756688672864665578915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1986504459115243110385943 2979756688672864665578915)
                ·
                  refine ⟨4469635033009296998368373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2979756688672864665578915 4469635033009296998368373)
                  ·
                    refine ⟨419028284344621593597035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4469635033009296998368373 419028284344621593597035)
                    ·
                      rfl

theorem cell23_2448164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_2448164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448164 prefixEnd_2448164 := by exact prefixLift 2448164
  have htrace : WordTrace (prefixWord ++ tailWord_2448164) baseStart_2448164 baseEnd_2448164 := by
    simpa [prefixWord, tailWord_2448164, baseEnd_2448164] using wordTrace_append hprefix tailTrace_2448164
  have hstable : (prefixWord ++ tailWord_2448164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448164).length < 2 ^ (prefixWord ++ tailWord_2448164).sum := by decide
  have hdescent : baseEnd_2448164 < baseStart_2448164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448177 : List Nat := [1, 2, 2, 3, 2, 1, 4, 2, 2, 4]
def baseStart_2448177 : Nat := 118140960795 + 2448177 * 2 ^ 59
def prefixEnd_2448177 : Nat := 4983230072969 + 3 ^ 40 * 2448177 * 2
def baseEnd_2448177 : Nat := 419030509427457743309515

theorem tailTrace_2448177 : CollatzResearch.WordTrace tailWord_2448177 prefixEnd_2448177 419030509427457743309515 := by
  unfold tailWord_2448177
  simp only [CollatzResearch.WordTrace]
  refine ⟨89292350851680319188846785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59528233901120212792564523 89292350851680319188846785)
  ·
    refine ⟨66969263138760239391635089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89292350851680319188846785 66969263138760239391635089)
    ·
      refine ⟨50226947354070179543726317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66969263138760239391635089 50226947354070179543726317)
      ·
        refine ⟨18835105257776317328897369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50226947354070179543726317 18835105257776317328897369)
        ·
          refine ⟨14126328943332237996673027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18835105257776317328897369 14126328943332237996673027)
          ·
            refine ⟨21189493414998356995009541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14126328943332237996673027 21189493414998356995009541)
            ·
              refine ⟨3973030015312191936564289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21189493414998356995009541 3973030015312191936564289)
              ·
                refine ⟨2979772511484143952423217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3973030015312191936564289 2979772511484143952423217)
                ·
                  refine ⟨2234829383613107964317413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2979772511484143952423217 2234829383613107964317413)
                  ·
                    refine ⟨419030509427457743309515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2234829383613107964317413 419030509427457743309515)
                    ·
                      rfl

theorem cell23_2448177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_2448177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448177 prefixEnd_2448177 := by exact prefixLift 2448177
  have htrace : WordTrace (prefixWord ++ tailWord_2448177) baseStart_2448177 baseEnd_2448177 := by
    simpa [prefixWord, tailWord_2448177, baseEnd_2448177] using wordTrace_append hprefix tailTrace_2448177
  have hstable : (prefixWord ++ tailWord_2448177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448177).length < 2 ^ (prefixWord ++ tailWord_2448177).sum := by decide
  have hdescent : baseEnd_2448177 < baseStart_2448177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448258 : List Nat := [3, 4, 2, 2, 2, 1, 2, 7]
def baseStart_2448258 : Nat := 118140960795 + 2448258 * 2 ^ 59
def prefixEnd_2448258 : Nat := 4983230072969 + 3 ^ 40 * 2448258 * 2
def baseEnd_2448258 : Nat := 46560485933903237519099

theorem tailTrace_2448258 : CollatzResearch.WordTrace tailWord_2448258 prefixEnd_2448258 46560485933903237519099 := by
  unfold tailWord_2448258
  simp only [CollatzResearch.WordTrace]
  refine ⟨22323826291096717505636357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59530203442924580015030285 22323826291096717505636357)
  ·
    refine ⟨4185717429580634532306817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22323826291096717505636357 4185717429580634532306817)
    ·
      refine ⟨3139288072185475899230113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4185717429580634532306817 3139288072185475899230113)
      ·
        refine ⟨2354466054139106924422585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3139288072185475899230113 2354466054139106924422585)
        ·
          refine ⟨1765849540604330193316939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2354466054139106924422585 1765849540604330193316939)
          ·
            refine ⟨2648774310906495289975409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1765849540604330193316939 2648774310906495289975409)
            ·
              refine ⟨1986580733179871467481557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2648774310906495289975409 1986580733179871467481557)
              ·
                refine ⟨46560485933903237519099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1986580733179871467481557 46560485933903237519099)
                ·
                  rfl

theorem cell23_2448258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 2, 7].length) (baseStart_2448258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448258 prefixEnd_2448258 := by exact prefixLift 2448258
  have htrace : WordTrace (prefixWord ++ tailWord_2448258) baseStart_2448258 baseEnd_2448258 := by
    simpa [prefixWord, tailWord_2448258, baseEnd_2448258] using wordTrace_append hprefix tailTrace_2448258
  have hstable : (prefixWord ++ tailWord_2448258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448258).length < 2 ^ (prefixWord ++ tailWord_2448258).sum := by decide
  have hdescent : baseEnd_2448258 < baseStart_2448258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448260 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_2448260 : Nat := 118140960795 + 2448260 * 2 ^ 59
def prefixEnd_2448260 : Nat := 4983230072969 + 3 ^ 40 * 2448260 * 2
def baseEnd_2448260 : Nat := 1257134147176696405190663

theorem tailTrace_2448260 : CollatzResearch.WordTrace tailWord_2448260 prefixEnd_2448260 1257134147176696405190663 := by
  unfold tailWord_2448260
  simp only [CollatzResearch.WordTrace]
  refine ⟨44647689055189812182059117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59530252073586416242745489 44647689055189812182059117)
  ·
    refine ⟨16742883395696179568272169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44647689055189812182059117 16742883395696179568272169)
    ·
      refine ⟨12557162546772134676204127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16742883395696179568272169 12557162546772134676204127)
      ·
        refine ⟨18835743820158202014306191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12557162546772134676204127 18835743820158202014306191)
        ·
          refine ⟨28253615730237303021459287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18835743820158202014306191 28253615730237303021459287)
          ·
            refine ⟨42380423595355954532188931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28253615730237303021459287 42380423595355954532188931)
            ·
              refine ⟨63570635393033931798283397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42380423595355954532188931 63570635393033931798283397)
              ·
                refine ⟨11919494136193862212178137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63570635393033931798283397 11919494136193862212178137)
                ·
                  refine ⟨8939620602145396659133603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11919494136193862212178137 8939620602145396659133603)
                  ·
                    refine ⟨13409430903218094988700405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8939620602145396659133603 13409430903218094988700405)
                    ·
                      refine ⟨1257134147176696405190663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13409430903218094988700405 1257134147176696405190663)
                      ·
                        rfl

theorem cell23_2448260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_2448260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448260 prefixEnd_2448260 := by exact prefixLift 2448260
  have htrace : WordTrace (prefixWord ++ tailWord_2448260) baseStart_2448260 baseEnd_2448260 := by
    simpa [prefixWord, tailWord_2448260, baseEnd_2448260] using wordTrace_append hprefix tailTrace_2448260
  have hstable : (prefixWord ++ tailWord_2448260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448260).length < 2 ^ (prefixWord ++ tailWord_2448260).sum := by decide
  have hdescent : baseEnd_2448260 < baseStart_2448260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448354 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_2448354 : Nat := 118140960795 + 2448354 * 2 ^ 59
def prefixEnd_2448354 : Nat := 4983230072969 + 3 ^ 40 * 2448354 * 2
def baseEnd_2448354 : Nat := 1257182414358219037415231

theorem tailTrace_2448354 : CollatzResearch.WordTrace tailWord_2448354 prefixEnd_2448354 1257182414358219037415231 := by
  unfold tailWord_2448354
  simp only [CollatzResearch.WordTrace]
  refine ⟨22324701643009769604510029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59532537714692718945360077 22324701643009769604510029)
  ·
    refine ⟨8371763116128663601691261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22324701643009769604510029 8371763116128663601691261)
    ·
      refine ⟨3139411168548248850634223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8371763116128663601691261 3139411168548248850634223)
      ·
        refine ⟨4709116752822373275951335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3139411168548248850634223 4709116752822373275951335)
        ·
          refine ⟨7063675129233559913927003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4709116752822373275951335 7063675129233559913927003)
          ·
            refine ⟨10595512693850339870890505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7063675129233559913927003 10595512693850339870890505)
            ·
              refine ⟨7946634520387754903167879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10595512693850339870890505 7946634520387754903167879)
              ·
                refine ⟨11919951780581632354751819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7946634520387754903167879 11919951780581632354751819)
                ·
                  refine ⟨17879927670872448532127729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11919951780581632354751819 17879927670872448532127729)
                  ·
                    refine ⟨13409945753154336399095797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17879927670872448532127729 13409945753154336399095797)
                    ·
                      refine ⟨1257182414358219037415231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13409945753154336399095797 1257182414358219037415231)
                      ·
                        rfl

theorem cell23_2448354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_2448354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448354 prefixEnd_2448354 := by exact prefixLift 2448354
  have htrace : WordTrace (prefixWord ++ tailWord_2448354) baseStart_2448354 baseEnd_2448354 := by
    simpa [prefixWord, tailWord_2448354, baseEnd_2448354] using wordTrace_append hprefix tailTrace_2448354
  have hstable : (prefixWord ++ tailWord_2448354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448354).length < 2 ^ (prefixWord ++ tailWord_2448354).sum := by decide
  have hdescent : baseEnd_2448354 < baseStart_2448354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448374 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_2448374 : Nat := 118140960795 + 2448374 * 2 ^ 59
def prefixEnd_2448374 : Nat := 4983230072969 + 3 ^ 40 * 2448374 * 2
def baseEnd_2448374 : Nat := 419064227990436319721713

theorem tailTrace_2448374 : CollatzResearch.WordTrace tailWord_2448374 prefixEnd_2448374 419064227990436319721713 := by
  unfold tailWord_2448374
  simp only [CollatzResearch.WordTrace]
  refine ⟨5581221001997913864610511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59533024021311081222512117 5581221001997913864610511)
  ·
    refine ⟨8371831502996870796915767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5581221001997913864610511 8371831502996870796915767)
    ·
      refine ⟨12557747254495306195373651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8371831502996870796915767 12557747254495306195373651)
      ·
        refine ⟨18836620881742959293060477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12557747254495306195373651 18836620881742959293060477)
        ·
          refine ⟨7063732830653609734897679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18836620881742959293060477 7063732830653609734897679)
          ·
            refine ⟨10595599245980414602346519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7063732830653609734897679 10595599245980414602346519)
            ·
              refine ⟨15893398868970621903519779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10595599245980414602346519 15893398868970621903519779)
              ·
                refine ⟨23840098303455932855279669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15893398868970621903519779 23840098303455932855279669)
                ·
                  refine ⟨2235009215948993705182469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23840098303455932855279669 2235009215948993705182469)
                  ·
                    refine ⟨419064227990436319721713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2235009215948993705182469 419064227990436319721713)
                    ·
                      rfl

theorem cell23_2448374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_2448374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448374 prefixEnd_2448374 := by exact prefixLift 2448374
  have htrace : WordTrace (prefixWord ++ tailWord_2448374) baseStart_2448374 baseEnd_2448374 := by
    simpa [prefixWord, tailWord_2448374, baseEnd_2448374] using wordTrace_append hprefix tailTrace_2448374
  have hstable : (prefixWord ++ tailWord_2448374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448374).length < 2 ^ (prefixWord ++ tailWord_2448374).sum := by decide
  have hdescent : baseEnd_2448374 < baseStart_2448374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448391 : List Nat := [1, 1, 4, 3, 1, 1, 4, 3, 1, 4]
def baseStart_2448391 : Nat := 118140960795 + 2448391 * 2 ^ 59
def prefixEnd_2448391 : Nat := 4983230072969 + 3 ^ 40 * 2448391 * 2
def baseEnd_2448391 : Nat := 419067137714145130884187

theorem tailTrace_2448391 : CollatzResearch.WordTrace tailWord_2448391 prefixEnd_2448391 419067137714145130884187 := by
  unfold tailWord_2448391
  simp only [CollatzResearch.WordTrace]
  refine ⟨89300156072905033737137027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59533437381936689158091351 89300156072905033737137027)
  ·
    refine ⟨133950234109357550605705541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89300156072905033737137027 133950234109357550605705541)
    ·
      refine ⟨25115668895504540738569789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133950234109357550605705541 25115668895504540738569789)
      ·
        refine ⟨9418375835814202776963671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25115668895504540738569789 9418375835814202776963671)
        ·
          refine ⟨14127563753721304165445507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9418375835814202776963671 14127563753721304165445507)
          ·
            refine ⟨21191345630581956248168261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14127563753721304165445507 21191345630581956248168261)
            ·
              refine ⟨3973377305734116796531549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21191345630581956248168261 3973377305734116796531549)
              ·
                refine ⟨1490016489650293798699331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3973377305734116796531549 1490016489650293798699331)
                ·
                  refine ⟨2235024734475440698048997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1490016489650293798699331 2235024734475440698048997)
                  ·
                    refine ⟨419067137714145130884187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2235024734475440698048997 419067137714145130884187)
                    ·
                      rfl

theorem cell23_2448391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_2448391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448391 prefixEnd_2448391 := by exact prefixLift 2448391
  have htrace : WordTrace (prefixWord ++ tailWord_2448391) baseStart_2448391 baseEnd_2448391 := by
    simpa [prefixWord, tailWord_2448391, baseEnd_2448391] using wordTrace_append hprefix tailTrace_2448391
  have hstable : (prefixWord ++ tailWord_2448391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448391).length < 2 ^ (prefixWord ++ tailWord_2448391).sum := by decide
  have hdescent : baseEnd_2448391 < baseStart_2448391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448407 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 6]
def baseStart_2448407 : Nat := 118140960795 + 2448407 * 2 ^ 59
def prefixEnd_2448407 : Nat := 4983230072969 + 3 ^ 40 * 2448407 * 2
def baseEnd_2448407 : Nat := 1257209628832907330052487

theorem tailTrace_2448407 : CollatzResearch.WordTrace tailWord_2448407 prefixEnd_2448407 1257209628832907330052487 := by
  unfold tailWord_2448407
  simp only [CollatzResearch.WordTrace]
  refine ⟨89300739640847068469719475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59533826427231378979812983 89300739640847068469719475)
  ·
    refine ⟨133951109461270602704579213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89300739640847068469719475 133951109461270602704579213)
    ·
      refine ⟨50231666047976476014217205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133951109461270602704579213 50231666047976476014217205)
      ·
        refine ⟨4709218691997794626332863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50231666047976476014217205 4709218691997794626332863)
        ·
          refine ⟨7063828037996691939499295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4709218691997794626332863 7063828037996691939499295)
          ·
            refine ⟨10595742056995037909248943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7063828037996691939499295 10595742056995037909248943)
            ·
              refine ⟨15893613085492556863873415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10595742056995037909248943 15893613085492556863873415)
              ·
                refine ⟨23840419628238835295810123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15893613085492556863873415 23840419628238835295810123)
                ·
                  refine ⟨35760629442358252943715185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23840419628238835295810123 35760629442358252943715185)
                  ·
                    refine ⟨26820472081768689707786389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35760629442358252943715185 26820472081768689707786389)
                    ·
                      refine ⟨1257209628832907330052487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26820472081768689707786389 1257209628832907330052487)
                      ·
                        rfl

theorem cell23_2448407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_2448407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448407 prefixEnd_2448407 := by exact prefixLift 2448407
  have htrace : WordTrace (prefixWord ++ tailWord_2448407) baseStart_2448407 baseEnd_2448407 := by
    simpa [prefixWord, tailWord_2448407, baseEnd_2448407] using wordTrace_append hprefix tailTrace_2448407
  have hstable : (prefixWord ++ tailWord_2448407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448407).length < 2 ^ (prefixWord ++ tailWord_2448407).sum := by decide
  have hdescent : baseEnd_2448407 < baseStart_2448407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448434 : List Nat := [3, 2, 1, 1, 2, 2, 4, 2, 1, 5]
def baseStart_2448434 : Nat := 118140960795 + 2448434 * 2 ^ 59
def prefixEnd_2448434 : Nat := 4983230072969 + 3 ^ 40 * 2448434 * 2
def baseEnd_2448434 : Nat := 419074497603526241471621

theorem tailTrace_2448434 : CollatzResearch.WordTrace tailWord_2448434 prefixEnd_2448434 419074497603526241471621 := by
  unfold tailWord_2448434
  simp only [CollatzResearch.WordTrace]
  refine ⟨22325431102937313020238089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59534482941166168053968237 22325431102937313020238089)
  ·
    refine ⟨16744073327202984765178567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22325431102937313020238089 16744073327202984765178567)
    ·
      refine ⟨25116109990804477147767851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16744073327202984765178567 25116109990804477147767851)
      ·
        refine ⟨37674164986206715721651777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25116109990804477147767851 37674164986206715721651777)
        ·
          refine ⟨28255623739655036791238833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37674164986206715721651777 28255623739655036791238833)
          ·
            refine ⟨21191717804741277593429125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28255623739655036791238833 21191717804741277593429125)
            ·
              refine ⟨3973447088388989548767961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21191717804741277593429125 3973447088388989548767961)
              ·
                refine ⟨2980085316291742161575971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3973447088388989548767961 2980085316291742161575971)
                ·
                  refine ⟨4470127974437613242363957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2980085316291742161575971 4470127974437613242363957)
                  ·
                    refine ⟨419074497603526241471621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4470127974437613242363957 419074497603526241471621)
                    ·
                      rfl

theorem cell23_2448434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_2448434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448434 prefixEnd_2448434 := by exact prefixLift 2448434
  have htrace : WordTrace (prefixWord ++ tailWord_2448434) baseStart_2448434 baseEnd_2448434 := by
    simpa [prefixWord, tailWord_2448434, baseEnd_2448434] using wordTrace_append hprefix tailTrace_2448434
  have hstable : (prefixWord ++ tailWord_2448434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448434).length < 2 ^ (prefixWord ++ tailWord_2448434).sum := by decide
  have hdescent : baseEnd_2448434 < baseStart_2448434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448481 : List Nat := [1, 2, 3, 1, 1, 2, 6, 1, 2, 4]
def baseStart_2448481 : Nat := 118140960795 + 2448481 * 2 ^ 59
def prefixEnd_2448481 : Nat := 4983230072969 + 3 ^ 40 * 2448481 * 2
def baseEnd_2448481 : Nat := 419082542133780013509049

theorem tailTrace_2448481 : CollatzResearch.WordTrace tailWord_2448481 prefixEnd_2448481 419082542133780013509049 := by
  unfold tailWord_2448481
  simp only [CollatzResearch.WordTrace]
  refine ⟨89303438642578979107913297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59535625761719319405275531 89303438642578979107913297)
  ·
    refine ⟨66977578981934234330934973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89303438642578979107913297 66977578981934234330934973)
    ·
      refine ⟨25116592118225337874100615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66977578981934234330934973 25116592118225337874100615)
      ·
        refine ⟨37674888177338006811150923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25116592118225337874100615 37674888177338006811150923)
        ·
          refine ⟨56512332266007010216726385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37674888177338006811150923 56512332266007010216726385)
          ·
            refine ⟨42384249199505257662544789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56512332266007010216726385 42384249199505257662544789)
            ·
              refine ⟨1986761681226808952931787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42384249199505257662544789 1986761681226808952931787)
              ·
                refine ⟨2980142521840213429397681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1986761681226808952931787 2980142521840213429397681)
                ·
                  refine ⟨2235106891380160072048261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2980142521840213429397681 2235106891380160072048261)
                  ·
                    refine ⟨419082542133780013509049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2235106891380160072048261 419082542133780013509049)
                    ·
                      rfl

theorem cell23_2448481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_2448481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448481 prefixEnd_2448481 := by exact prefixLift 2448481
  have htrace : WordTrace (prefixWord ++ tailWord_2448481) baseStart_2448481 baseEnd_2448481 := by
    simpa [prefixWord, tailWord_2448481, baseEnd_2448481] using wordTrace_append hprefix tailTrace_2448481
  have hstable : (prefixWord ++ tailWord_2448481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448481).length < 2 ^ (prefixWord ++ tailWord_2448481).sum := by decide
  have hdescent : baseEnd_2448481 < baseStart_2448481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448504 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 6, 1, 3]
def baseStart_2448504 : Nat := 118140960795 + 2448504 * 2 ^ 59
def prefixEnd_2448504 : Nat := 4983230072969 + 3 ^ 40 * 2448504 * 2
def baseEnd_2448504 : Nat := 1257259436456393450539541

theorem tailTrace_2448504 : CollatzResearch.WordTrace tailWord_2448504 prefixEnd_2448504 1257259436456393450539541 := by
  unfold tailWord_2448504
  simp only [CollatzResearch.WordTrace]
  refine ⟨44652138760747827018000283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59536185014330436024000377 44652138760747827018000283)
  ·
    refine ⟨66978208141121740527000425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44652138760747827018000283 66978208141121740527000425)
    ·
      refine ⟨50233656105841305395250319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66978208141121740527000425 50233656105841305395250319)
      ·
        refine ⟨75350484158761958092875479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50233656105841305395250319 75350484158761958092875479)
        ·
          refine ⟨113025726238142937139313219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75350484158761958092875479 113025726238142937139313219)
          ·
            refine ⟨169538589357214405708969829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113025726238142937139313219 169538589357214405708969829)
            ·
              refine ⟨31788485504477701070431843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169538589357214405708969829 31788485504477701070431843)
              ·
                refine ⟨47682728256716551605647765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31788485504477701070431843 47682728256716551605647765)
                ·
                  refine ⟨2235127887033588356514739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 47682728256716551605647765 2235127887033588356514739)
                  ·
                    refine ⟨3352691830550382534772109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2235127887033588356514739 3352691830550382534772109)
                    ·
                      refine ⟨1257259436456393450539541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3352691830550382534772109 1257259436456393450539541)
                      ·
                        rfl

theorem cell23_2448504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 6, 1, 3].length) (baseStart_2448504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448504 prefixEnd_2448504 := by exact prefixLift 2448504
  have htrace : WordTrace (prefixWord ++ tailWord_2448504) baseStart_2448504 baseEnd_2448504 := by
    simpa [prefixWord, tailWord_2448504, baseEnd_2448504] using wordTrace_append hprefix tailTrace_2448504
  have hstable : (prefixWord ++ tailWord_2448504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448504).length < 2 ^ (prefixWord ++ tailWord_2448504).sum := by decide
  have hdescent : baseEnd_2448504 < baseStart_2448504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448521 : List Nat := [1, 2, 1, 1, 4, 3, 1, 4, 2, 1, 3]
def baseStart_2448521 : Nat := 118140960795 + 2448521 * 2 ^ 59
def prefixEnd_2448521 : Nat := 4983230072969 + 3 ^ 40 * 2448521 * 2
def baseEnd_2448521 : Nat := 1257268165627519884026963

theorem tailTrace_2448521 : CollatzResearch.WordTrace tailWord_2448521 prefixEnd_2448521 1257268165627519884026963 := by
  unfold tailWord_2448521
  simp only [CollatzResearch.WordTrace]
  refine ⟨89304897562434065939369417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59536598374956043959579611 89304897562434065939369417)
  ·
    refine ⟨66978673171825549454527063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89304897562434065939369417 66978673171825549454527063)
    ·
      refine ⟨100468009757738324181790595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66978673171825549454527063 100468009757738324181790595)
      ·
        refine ⟨150702014636607486272685893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100468009757738324181790595 150702014636607486272685893)
        ·
          refine ⟨28256627744363903676128605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150702014636607486272685893 28256627744363903676128605)
          ·
            refine ⟨10596235404136463878548227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28256627744363903676128605 10596235404136463878548227)
            ·
              refine ⟨15894353106204695817822341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10596235404136463878548227 15894353106204695817822341)
              ·
                refine ⟨2980191207413380465841689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15894353106204695817822341 2980191207413380465841689)
                ·
                  refine ⟨2235143405560035349381267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2980191207413380465841689 2235143405560035349381267)
                  ·
                    refine ⟨3352715108340053024071901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2235143405560035349381267 3352715108340053024071901)
                    ·
                      refine ⟨1257268165627519884026963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3352715108340053024071901 1257268165627519884026963)
                      ·
                        rfl

theorem cell23_2448521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 1, 3].length) (baseStart_2448521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448521 prefixEnd_2448521 := by exact prefixLift 2448521
  have htrace : WordTrace (prefixWord ++ tailWord_2448521) baseStart_2448521 baseEnd_2448521 := by
    simpa [prefixWord, tailWord_2448521, baseEnd_2448521] using wordTrace_append hprefix tailTrace_2448521
  have hstable : (prefixWord ++ tailWord_2448521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448521).length < 2 ^ (prefixWord ++ tailWord_2448521).sum := by decide
  have hdescent : baseEnd_2448521 < baseStart_2448521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448538 : List Nat := [3, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3]
def baseStart_2448538 : Nat := 118140960795 + 2448538 * 2 ^ 59
def prefixEnd_2448538 : Nat := 4983230072969 + 3 ^ 40 * 2448538 * 2
def baseEnd_2448538 : Nat := 1257276894798646317514385

theorem tailTrace_2448538 : CollatzResearch.WordTrace tailWord_2448538 prefixEnd_2448538 1257276894798646317514385 := by
  unfold tailWord_2448538
  simp only [CollatzResearch.WordTrace]
  refine ⟨22326379400843119460684567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59537011735581651895158845 22326379400843119460684567)
  ·
    refine ⟨33489569101264679191026851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22326379400843119460684567 33489569101264679191026851)
    ·
      refine ⟨50234353651897018786540277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33489569101264679191026851 50234353651897018786540277)
      ·
        refine ⟨4709470654865345511238151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50234353651897018786540277 4709470654865345511238151)
        ·
          refine ⟨7064205982298018266857227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4709470654865345511238151 7064205982298018266857227)
          ·
            refine ⟨10596308973447027400285841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7064205982298018266857227 10596308973447027400285841)
            ·
              refine ⟨7947231730085270550214381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10596308973447027400285841 7947231730085270550214381)
              ·
                refine ⟨2980211898781976456330393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7947231730085270550214381 2980211898781976456330393)
                ·
                  refine ⟨2235158924086482342247795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2980211898781976456330393 2235158924086482342247795)
                  ·
                    refine ⟨3352738386129723513371693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2235158924086482342247795 3352738386129723513371693)
                    ·
                      refine ⟨1257276894798646317514385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3352738386129723513371693 1257276894798646317514385)
                      ·
                        rfl

theorem cell23_2448538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_2448538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448538 prefixEnd_2448538 := by exact prefixLift 2448538
  have htrace : WordTrace (prefixWord ++ tailWord_2448538) baseStart_2448538 baseEnd_2448538 := by
    simpa [prefixWord, tailWord_2448538, baseEnd_2448538] using wordTrace_append hprefix tailTrace_2448538
  have hstable : (prefixWord ++ tailWord_2448538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448538).length < 2 ^ (prefixWord ++ tailWord_2448538).sum := by decide
  have hdescent : baseEnd_2448538 < baseStart_2448538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448547 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 5]
def baseStart_2448547 : Nat := 118140960795 + 2448547 * 2 ^ 59
def prefixEnd_2448547 : Nat := 4983230072969 + 3 ^ 40 * 2448547 * 2
def baseEnd_2448547 : Nat := 1257281516124536782301843

theorem tailTrace_2448547 : CollatzResearch.WordTrace tailWord_2448547 prefixEnd_2448547 1257281516124536782301843 := by
  unfold tailWord_2448547
  simp only [CollatzResearch.WordTrace]
  refine ⟨89305845860339872379815895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59537230573559914919877263 89305845860339872379815895)
  ·
    refine ⟨133958768790509808569723843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89305845860339872379815895 133958768790509808569723843)
    ·
      refine ⟨200938153185764712854585765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133958768790509808569723843 200938153185764712854585765)
      ·
        refine ⟨37675903722330883660234831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200938153185764712854585765 37675903722330883660234831)
        ·
          refine ⟨56513855583496325490352247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37675903722330883660234831 56513855583496325490352247)
          ·
            refine ⟨84770783375244488235528371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56513855583496325490352247 84770783375244488235528371)
            ·
              refine ⟨127156175062866732353292557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84770783375244488235528371 127156175062866732353292557)
              ·
                refine ⟨47683565648575024632484709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127156175062866732353292557 47683565648575024632484709)
                ·
                  refine ⟨8940668559107817118590883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47683565648575024632484709 8940668559107817118590883)
                  ·
                    refine ⟨13411002838661725677886325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8940668559107817118590883 13411002838661725677886325)
                    ·
                      refine ⟨1257281516124536782301843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13411002838661725677886325 1257281516124536782301843)
                      ·
                        rfl

theorem cell23_2448547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_2448547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448547 prefixEnd_2448547 := by exact prefixLift 2448547
  have htrace : WordTrace (prefixWord ++ tailWord_2448547) baseStart_2448547 baseEnd_2448547 := by
    simpa [prefixWord, tailWord_2448547, baseEnd_2448547] using wordTrace_append hprefix tailTrace_2448547
  have hstable : (prefixWord ++ tailWord_2448547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448547).length < 2 ^ (prefixWord ++ tailWord_2448547).sum := by decide
  have hdescent : baseEnd_2448547 < baseStart_2448547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448567 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 9]
def baseStart_2448567 : Nat := 118140960795 + 2448567 * 2 ^ 59
def prefixEnd_2448567 : Nat := 4983230072969 + 3 ^ 40 * 2448567 * 2
def baseEnd_2448567 : Nat := 139699087304180744894639

theorem tailTrace_2448567 : CollatzResearch.WordTrace tailWord_2448567 prefixEnd_2448567 139699087304180744894639 := by
  unfold tailWord_2448567
  simp only [CollatzResearch.WordTrace]
  refine ⟨89306575320267415795543955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59537716880178277197029303 89306575320267415795543955)
  ·
    refine ⟨133959862980401123693315933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89306575320267415795543955 133959862980401123693315933)
    ·
      refine ⟨50234948617650421384993475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133959862980401123693315933 50234948617650421384993475)
      ·
        refine ⟨75352422926475632077490213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50234948617650421384993475 75352422926475632077490213)
        ·
          refine ⟨14128579298714181014529415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75352422926475632077490213 14128579298714181014529415)
          ·
            refine ⟨21192868948071271521794123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14128579298714181014529415 21192868948071271521794123)
            ·
              refine ⟨31789303422106907282691185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21192868948071271521794123 31789303422106907282691185)
              ·
                refine ⟨23841977566580180462018389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31789303422106907282691185 23841977566580180462018389)
                ·
                  refine ⟨139699087304180744894639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23841977566580180462018389 139699087304180744894639)
                  ·
                    rfl

theorem cell23_2448567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 9].length) (baseStart_2448567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448567 prefixEnd_2448567 := by exact prefixLift 2448567
  have htrace : WordTrace (prefixWord ++ tailWord_2448567) baseStart_2448567 baseEnd_2448567 := by
    simpa [prefixWord, tailWord_2448567, baseEnd_2448567] using wordTrace_append hprefix tailTrace_2448567
  have hstable : (prefixWord ++ tailWord_2448567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448567).length < 2 ^ (prefixWord ++ tailWord_2448567).sum := by decide
  have hdescent : baseEnd_2448567 < baseStart_2448567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448589 : List Nat := [1, 6, 2, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_2448589 : Nat := 118140960795 + 2448589 * 2 ^ 59
def prefixEnd_2448589 : Nat := 4983230072969 + 3 ^ 40 * 2448589 * 2
def baseEnd_2448589 : Nat := 1257303082312025617976651

theorem tailTrace_2448589 : CollatzResearch.WordTrace tailWord_2448589 prefixEnd_2448589 1257303082312025617976651 := by
  unfold tailWord_2448589
  simp only [CollatzResearch.WordTrace]
  refine ⟨89307377726187713552844821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59538251817458475701896547 89307377726187713552844821)
  ·
    refine ⟨4186283330915049072789601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 89307377726187713552844821 4186283330915049072789601)
    ·
      refine ⟨3139712498186286804592201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4186283330915049072789601 3139712498186286804592201)
      ·
        refine ⟨2354784373639715103444151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3139712498186286804592201 2354784373639715103444151)
        ·
          refine ⟨3532176560459572655166227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2354784373639715103444151 3532176560459572655166227)
          ·
            refine ⟨5298264840689358982749341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3532176560459572655166227 5298264840689358982749341)
            ·
              refine ⟨1986849315258509618531003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5298264840689358982749341 1986849315258509618531003)
              ·
                refine ⟨2980273972887764427796505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1986849315258509618531003 2980273972887764427796505)
                ·
                  refine ⟨2235205479665823320847379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2980273972887764427796505 2235205479665823320847379)
                  ·
                    refine ⟨3352808219498734981271069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2235205479665823320847379 3352808219498734981271069)
                    ·
                      refine ⟨1257303082312025617976651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3352808219498734981271069 1257303082312025617976651)
                      ·
                        rfl

theorem cell23_2448589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_2448589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448589 prefixEnd_2448589 := by exact prefixLift 2448589
  have htrace : WordTrace (prefixWord ++ tailWord_2448589) baseStart_2448589 baseEnd_2448589 := by
    simpa [prefixWord, tailWord_2448589, baseEnd_2448589] using wordTrace_append hprefix tailTrace_2448589
  have hstable : (prefixWord ++ tailWord_2448589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448589).length < 2 ^ (prefixWord ++ tailWord_2448589).sum := by decide
  have hdescent : baseEnd_2448589 < baseStart_2448589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448618 : List Nat := [3, 1, 3, 1, 1, 5, 1, 3, 5]
def baseStart_2448618 : Nat := 118140960795 + 2448618 * 2 ^ 59
def prefixEnd_2448618 : Nat := 4983230072969 + 3 ^ 40 * 2448618 * 2
def baseEnd_2448618 : Nat := 139701997027889556057113

theorem tailTrace_2448618 : CollatzResearch.WordTrace tailWord_2448618 prefixEnd_2448618 139701997027889556057113 := by
  unfold tailWord_2448618
  simp only [CollatzResearch.WordTrace]
  refine ⟨22327108860770662876412627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59538956962055101003767005 22327108860770662876412627)
  ·
    refine ⟨33490663291155994314618941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22327108860770662876412627 33490663291155994314618941)
    ·
      refine ⟨12558998734183497867982103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33490663291155994314618941 12558998734183497867982103)
      ·
        refine ⟨18838498101275246801973155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12558998734183497867982103 18838498101275246801973155)
        ·
          refine ⟨28257747151912870202959733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18838498101275246801973155 28257747151912870202959733)
          ·
            refine ⟨2649163795491831581527475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28257747151912870202959733 2649163795491831581527475)
            ·
              refine ⟨3973745693237747372291213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2649163795491831581527475 3973745693237747372291213)
              ·
                refine ⟨1490154634964155264609205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3973745693237747372291213 1490154634964155264609205)
                ·
                  refine ⟨139701997027889556057113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1490154634964155264609205 139701997027889556057113)
                  ·
                    rfl

theorem cell23_2448618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 3, 5].length) (baseStart_2448618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448618 prefixEnd_2448618 := by exact prefixLift 2448618
  have htrace : WordTrace (prefixWord ++ tailWord_2448618) baseStart_2448618 baseEnd_2448618 := by
    simpa [prefixWord, tailWord_2448618, baseEnd_2448618] using wordTrace_append hprefix tailTrace_2448618
  have hstable : (prefixWord ++ tailWord_2448618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448618).length < 2 ^ (prefixWord ++ tailWord_2448618).sum := by decide
  have hdescent : baseEnd_2448618 < baseStart_2448618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448691 : List Nat := [1, 1, 1, 2, 5, 3, 2, 2, 6]
def baseStart_2448691 : Nat := 118140960795 + 2448691 * 2 ^ 59
def prefixEnd_2448691 : Nat := 4983230072969 + 3 ^ 40 * 2448691 * 2
def baseEnd_2448691 : Nat := 139706161926531579877909

theorem tailTrace_2448691 : CollatzResearch.WordTrace tailWord_2448691 prefixEnd_2448691 139706161926531579877909 := by
  unfold tailWord_2448691
  simp only [CollatzResearch.WordTrace]
  refine ⟨89311097971818184973057927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59540731981212123315371951 89311097971818184973057927)
  ·
    refine ⟨133966646957727277459586891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89311097971818184973057927 133966646957727277459586891)
    ·
      refine ⟨200949970436590916189380337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133966646957727277459586891 200949970436590916189380337)
      ·
        refine ⟨150712477827443187142035253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200949970436590916189380337 150712477827443187142035253)
        ·
          refine ⟨14129294796322798794565805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 150712477827443187142035253 14129294796322798794565805)
          ·
            refine ⟨5298485548621049547962177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14129294796322798794565805 5298485548621049547962177)
            ·
              refine ⟨3973864161465787160971633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5298485548621049547962177 3973864161465787160971633)
              ·
                refine ⟨2980398121099340370728725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3973864161465787160971633 2980398121099340370728725)
                ·
                  refine ⟨139706161926531579877909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2980398121099340370728725 139706161926531579877909)
                  ·
                    rfl

theorem cell23_2448691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 6].length) (baseStart_2448691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448691 prefixEnd_2448691 := by exact prefixLift 2448691
  have htrace : WordTrace (prefixWord ++ tailWord_2448691) baseStart_2448691 baseEnd_2448691 := by
    simpa [prefixWord, tailWord_2448691, baseEnd_2448691] using wordTrace_append hprefix tailTrace_2448691
  have hstable : (prefixWord ++ tailWord_2448691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448691).length < 2 ^ (prefixWord ++ tailWord_2448691).sum := by decide
  have hdescent : baseEnd_2448691 < baseStart_2448691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448704 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 5, 5]
def baseStart_2448704 : Nat := 118140960795 + 2448704 * 2 ^ 59
def prefixEnd_2448704 : Nat := 4983230072969 + 3 ^ 40 * 2448704 * 2
def baseEnd_2448704 : Nat := 419120710862430889346207

theorem tailTrace_2448704 : CollatzResearch.WordTrace tailWord_2448704 prefixEnd_2448704 419120710862430889346207 := by
  unfold tailWord_2448704
  simp only [CollatzResearch.WordTrace]
  refine ⟨44655786060385544096640583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59541048080514058795520777 44655786060385544096640583)
  ·
    refine ⟨66983679090578316144960875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44655786060385544096640583 66983679090578316144960875)
    ·
      refine ⟨100475518635867474217441313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66983679090578316144960875 100475518635867474217441313)
      ·
        refine ⟨75356638976900605663080985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100475518635867474217441313 75356638976900605663080985)
        ·
          refine ⟨56517479232675454247310739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75356638976900605663080985 56517479232675454247310739)
          ·
            refine ⟨84776218849013181370966109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56517479232675454247310739 84776218849013181370966109)
            ·
              refine ⟨31791082068379943014112291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84776218849013181370966109 31791082068379943014112291)
              ·
                refine ⟨47686623102569914521168437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31791082068379943014112291 47686623102569914521168437)
                ·
                  refine ⟨4470620915865929486359541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47686623102569914521168437 4470620915865929486359541)
                  ·
                    refine ⟨419120710862430889346207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4470620915865929486359541 419120710862430889346207)
                    ·
                      rfl

theorem cell23_2448704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 5, 5].length) (baseStart_2448704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448704 prefixEnd_2448704 := by exact prefixLift 2448704
  have htrace : WordTrace (prefixWord ++ tailWord_2448704) baseStart_2448704 baseEnd_2448704 := by
    simpa [prefixWord, tailWord_2448704, baseEnd_2448704] using wordTrace_append hprefix tailTrace_2448704
  have hstable : (prefixWord ++ tailWord_2448704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448704).length < 2 ^ (prefixWord ++ tailWord_2448704).sum := by decide
  have hdescent : baseEnd_2448704 < baseStart_2448704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448708 : List Nat := [2, 3, 4, 1, 1, 1, 2, 3, 6]
def baseStart_2448708 : Nat := 118140960795 + 2448708 * 2 ^ 59
def prefixEnd_2448708 : Nat := 4983230072969 + 3 ^ 40 * 2448708 * 2
def baseEnd_2448708 : Nat := 139707131834434516932067

theorem tailTrace_2448708 : CollatzResearch.WordTrace tailWord_2448708 prefixEnd_2448708 139707131834434516932067 := by
  unfold tailWord_2448708
  simp only [CollatzResearch.WordTrace]
  refine ⟨44655859006378298438213389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59541145341837731250951185 44655859006378298438213389)
  ·
    refine ⟨16745947127391861914330021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44655859006378298438213389 16745947127391861914330021)
    ·
      refine ⟨3139865086385974108936879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16745947127391861914330021 3139865086385974108936879)
      ·
        refine ⟨4709797629578961163405319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3139865086385974108936879 4709797629578961163405319)
        ·
          refine ⟨7064696444368441745107979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4709797629578961163405319 7064696444368441745107979)
          ·
            refine ⟨10597044666552662617661969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7064696444368441745107979 10597044666552662617661969)
            ·
              refine ⟨7947783499914496963246477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10597044666552662617661969 7947783499914496963246477)
              ·
                refine ⟨2980418812467936361217429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7947783499914496963246477 2980418812467936361217429)
                ·
                  refine ⟨139707131834434516932067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2980418812467936361217429 139707131834434516932067)
                  ·
                    rfl

theorem cell23_2448708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_2448708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448708 prefixEnd_2448708 := by exact prefixLift 2448708
  have htrace : WordTrace (prefixWord ++ tailWord_2448708) baseStart_2448708 baseEnd_2448708 := by
    simpa [prefixWord, tailWord_2448708, baseEnd_2448708] using wordTrace_append hprefix tailTrace_2448708
  have hstable : (prefixWord ++ tailWord_2448708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448708).length < 2 ^ (prefixWord ++ tailWord_2448708).sum := by decide
  have hdescent : baseEnd_2448708 < baseStart_2448708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448718 : List Nat := [4, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3]
def baseStart_2448718 : Nat := 118140960795 + 2448718 * 2 ^ 59
def prefixEnd_2448718 : Nat := 4983230072969 + 3 ^ 40 * 2448718 * 2
def baseEnd_2448718 : Nat := 1257369321316455613263557

theorem tailTrace_2448718 : CollatzResearch.WordTrace tailWord_2448718 prefixEnd_2448718 1257369321316455613263557 := by
  unfold tailWord_2448718
  simp only [CollatzResearch.WordTrace]
  refine ⟨11164010342840046073036351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59541388495146912389527205 11164010342840046073036351)
  ·
    refine ⟨16746015514260069109554527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11164010342840046073036351 16746015514260069109554527)
    ·
      refine ⟨25119023271390103664331791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16746015514260069109554527 25119023271390103664331791)
      ·
        refine ⟨37678534907085155496497687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25119023271390103664331791 37678534907085155496497687)
        ·
          refine ⟨56517802360627733244746531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37678534907085155496497687 56517802360627733244746531)
          ·
            refine ⟨84776703540941599867119797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56517802360627733244746531 84776703540941599867119797)
            ·
              refine ⟨7947815956963274987542481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84776703540941599867119797 7947815956963274987542481)
              ·
                refine ⟨5960861967722456240656861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7947815956963274987542481 5960861967722456240656861)
                ·
                  refine ⟨2235323237895921090246323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5960861967722456240656861 2235323237895921090246323)
                  ·
                    refine ⟨3352984856843881635369485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2235323237895921090246323 3352984856843881635369485)
                    ·
                      refine ⟨1257369321316455613263557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3352984856843881635369485 1257369321316455613263557)
                      ·
                        rfl

theorem cell23_2448718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_2448718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448718 prefixEnd_2448718 := by exact prefixLift 2448718
  have htrace : WordTrace (prefixWord ++ tailWord_2448718) baseStart_2448718 baseEnd_2448718 := by
    simpa [prefixWord, tailWord_2448718, baseEnd_2448718] using wordTrace_append hprefix tailTrace_2448718
  have hstable : (prefixWord ++ tailWord_2448718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448718).length < 2 ^ (prefixWord ++ tailWord_2448718).sum := by decide
  have hdescent : baseEnd_2448718 < baseStart_2448718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448721 : List Nat := [1, 2, 2, 1, 4, 1, 2, 4, 1, 5]
def baseStart_2448721 : Nat := 118140960795 + 2448721 * 2 ^ 59
def prefixEnd_2448721 : Nat := 4983230072969 + 3 ^ 40 * 2448721 * 2
def baseEnd_2448721 : Nat := 419123620586139700508681

theorem tailTrace_2448721 : CollatzResearch.WordTrace tailWord_2448721 prefixEnd_2448721 419123620586139700508681 := by
  unfold tailWord_2448721
  simp only [CollatzResearch.WordTrace]
  refine ⟨89312192161709500096650017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59541461441139666731100011 89312192161709500096650017)
  ·
    refine ⟨66984144121282125072487513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89312192161709500096650017 66984144121282125072487513)
    ·
      refine ⟨50238108090961593804365635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66984144121282125072487513 50238108090961593804365635)
      ·
        refine ⟨75357162136442390706548453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50238108090961593804365635 75357162136442390706548453)
        ·
          refine ⟨14129467900582948257477835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75357162136442390706548453 14129467900582948257477835)
          ·
            refine ⟨21194201850874422386216753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14129467900582948257477835 21194201850874422386216753)
            ·
              refine ⟨15895651388155816789662565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21194201850874422386216753 15895651388155816789662565)
              ·
                refine ⟨2980434635279215648061731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15895651388155816789662565 2980434635279215648061731)
                ·
                  refine ⟨4470651952918823472092597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2980434635279215648061731 4470651952918823472092597)
                  ·
                    refine ⟨419123620586139700508681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4470651952918823472092597 419123620586139700508681)
                    ·
                      rfl

theorem cell23_2448721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_2448721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448721 prefixEnd_2448721 := by exact prefixLift 2448721
  have htrace : WordTrace (prefixWord ++ tailWord_2448721) baseStart_2448721 baseEnd_2448721 := by
    simpa [prefixWord, tailWord_2448721, baseEnd_2448721] using wordTrace_append hprefix tailTrace_2448721
  have hstable : (prefixWord ++ tailWord_2448721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448721).length < 2 ^ (prefixWord ++ tailWord_2448721).sum := by decide
  have hdescent : baseEnd_2448721 < baseStart_2448721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448738 : List Nat := [3, 3, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_2448738 : Nat := 118140960795 + 2448738 * 2 ^ 59
def prefixEnd_2448738 : Nat := 4983230072969 + 3 ^ 40 * 2448738 * 2
def baseEnd_2448738 : Nat := 419126530309848511671155

theorem tailTrace_2448738 : CollatzResearch.WordTrace tailWord_2448738 prefixEnd_2448738 419126530309848511671155 := by
  unfold tailWord_2448738
  simp only [CollatzResearch.WordTrace]
  refine ⟨22328203050661978000004717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59541874801765274666679245 22328203050661978000004717)
  ·
    refine ⟨8373076143998241750001769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22328203050661978000004717 8373076143998241750001769)
    ·
      refine ⟨6279807107998681312501327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8373076143998241750001769 6279807107998681312501327)
      ·
        refine ⟨9419710661998021968751991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6279807107998681312501327 9419710661998021968751991)
        ·
          refine ⟨14129565992997032953127987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9419710661998021968751991 14129565992997032953127987)
          ·
            refine ⟨21194348989495549429691981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14129565992997032953127987 21194348989495549429691981)
            ·
              refine ⟨7947880871060831036134493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21194348989495549429691981 7947880871060831036134493)
              ·
                refine ⟨2980455326647811638550435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7947880871060831036134493 2980455326647811638550435)
                ·
                  refine ⟨4470682989971717457825653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2980455326647811638550435 4470682989971717457825653)
                  ·
                    refine ⟨419126530309848511671155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4470682989971717457825653 419126530309848511671155)
                    ·
                      rfl

theorem cell23_2448738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_2448738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448738 prefixEnd_2448738 := by exact prefixLift 2448738
  have htrace : WordTrace (prefixWord ++ tailWord_2448738) baseStart_2448738 baseEnd_2448738 := by
    simpa [prefixWord, tailWord_2448738, baseEnd_2448738] using wordTrace_append hprefix tailTrace_2448738
  have hstable : (prefixWord ++ tailWord_2448738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448738).length < 2 ^ (prefixWord ++ tailWord_2448738).sum := by decide
  have hdescent : baseEnd_2448738 < baseStart_2448738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448751 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 4, 4]
def baseStart_2448751 : Nat := 118140960795 + 2448751 * 2 ^ 59
def prefixEnd_2448751 : Nat := 4983230072969 + 3 ^ 40 * 2448751 * 2
def baseEnd_2448751 : Nat := 419128755392684661383635

theorem tailTrace_2448751 : CollatzResearch.WordTrace tailWord_2448751 prefixEnd_2448751 419128755392684661383635 := by
  unfold tailWord_2448751
  simp only [CollatzResearch.WordTrace]
  refine ⟨89313286351600815220242107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59542190901067210146828071 89313286351600815220242107)
  ·
    refine ⟨133969929527401222830363161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89313286351600815220242107 133969929527401222830363161)
    ·
      refine ⟨100477447145550917122772371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133969929527401222830363161 100477447145550917122772371)
      ·
        refine ⟨150716170718326375684158557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100477447145550917122772371 150716170718326375684158557)
        ·
          refine ⟨56518564019372390881559459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150716170718326375684158557 56518564019372390881559459)
          ·
            refine ⟨84777846029058586322339189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56518564019372390881559459 84777846029058586322339189)
            ·
              refine ⟨7947923065224242467719299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84777846029058586322339189 7947923065224242467719299)
              ·
                refine ⟨11921884597836363701578949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7947923065224242467719299 11921884597836363701578949)
                ·
                  refine ⟨2235353362094318194046053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11921884597836363701578949 2235353362094318194046053)
                  ·
                    refine ⟨419128755392684661383635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2235353362094318194046053 419128755392684661383635)
                    ·
                      rfl

theorem cell23_2448751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 4, 4].length) (baseStart_2448751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448751 prefixEnd_2448751 := by exact prefixLift 2448751
  have htrace : WordTrace (prefixWord ++ tailWord_2448751) baseStart_2448751 baseEnd_2448751 := by
    simpa [prefixWord, tailWord_2448751, baseEnd_2448751] using wordTrace_append hprefix tailTrace_2448751
  have hstable : (prefixWord ++ tailWord_2448751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448751).length < 2 ^ (prefixWord ++ tailWord_2448751).sum := by decide
  have hdescent : baseEnd_2448751 < baseStart_2448751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448761 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 5, 2, 3]
def baseStart_2448761 : Nat := 118140960795 + 2448761 * 2 ^ 59
def prefixEnd_2448761 : Nat := 4983230072969 + 3 ^ 40 * 2448761 * 2
def baseEnd_2448761 : Nat := 1257391400984598945025859

theorem tailTrace_2448761 : CollatzResearch.WordTrace tailWord_2448761 prefixEnd_2448761 1257391400984598945025859 := by
  unfold tailWord_2448761
  simp only [CollatzResearch.WordTrace]
  refine ⟨89313651081564586928106137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59542434054376391285404091 89313651081564586928106137)
  ·
    refine ⟨66985238311173440196079603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89313651081564586928106137 66985238311173440196079603)
    ·
      refine ⟨100477857466760160294119405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66985238311173440196079603 100477857466760160294119405)
      ·
        refine ⟨37679196550035060110294777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100477857466760160294119405 37679196550035060110294777)
        ·
          refine ⟨28259397412526295082721083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37679196550035060110294777 28259397412526295082721083)
          ·
            refine ⟨42389096118789442624081625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28259397412526295082721083 42389096118789442624081625)
            ·
              refine ⟨31791822089092081968061219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42389096118789442624081625 31791822089092081968061219)
              ·
                refine ⟨47687733133638122952091829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31791822089092081968061219 47687733133638122952091829)
                ·
                  refine ⟨4470724981278574026758609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47687733133638122952091829 4470724981278574026758609)
                  ·
                    refine ⟨3353043735958930520068957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4470724981278574026758609 3353043735958930520068957)
                    ·
                      refine ⟨1257391400984598945025859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3353043735958930520068957 1257391400984598945025859)
                      ·
                        rfl

theorem cell23_2448761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_2448761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448761 prefixEnd_2448761 := by exact prefixLift 2448761
  have htrace : WordTrace (prefixWord ++ tailWord_2448761) baseStart_2448761 baseEnd_2448761 := by
    simpa [prefixWord, tailWord_2448761, baseEnd_2448761] using wordTrace_append hprefix tailTrace_2448761
  have hstable : (prefixWord ++ tailWord_2448761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448761).length < 2 ^ (prefixWord ++ tailWord_2448761).sum := by decide
  have hdescent : baseEnd_2448761 < baseStart_2448761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448764 : List Nat := [2, 2, 2, 1, 1, 1, 4, 10]
def baseStart_2448764 : Nat := 118140960795 + 2448764 * 2 ^ 59
def prefixEnd_2448764 : Nat := 4983230072969 + 3 ^ 40 * 2448764 * 2
def baseEnd_2448764 : Nat := 46570108941724534566235

theorem tailTrace_2448764 : CollatzResearch.WordTrace tailWord_2448764 prefixEnd_2448764 46570108941724534566235 := by
  unfold tailWord_2448764
  simp only [CollatzResearch.WordTrace]
  refine ⟨44656880250276859220232673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59542507000369145626976897 44656880250276859220232673)
  ·
    refine ⟨33492660187707644415174505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44656880250276859220232673 33492660187707644415174505)
    ·
      refine ⟨25119495140780733311380879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33492660187707644415174505 25119495140780733311380879)
      ·
        refine ⟨37679242711171099967071319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25119495140780733311380879 37679242711171099967071319)
        ·
          refine ⟨56518864066756649950606979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37679242711171099967071319 56518864066756649950606979)
          ·
            refine ⟨84778296100134974925910469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56518864066756649950606979 84778296100134974925910469)
            ·
              refine ⟨15895930518775307798608213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84778296100134974925910469 15895930518775307798608213)
              ·
                refine ⟨46570108941724534566235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 15895930518775307798608213 46570108941724534566235)
                ·
                  rfl

theorem cell23_2448764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 10].length) (baseStart_2448764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448764 prefixEnd_2448764 := by exact prefixLift 2448764
  have htrace : WordTrace (prefixWord ++ tailWord_2448764) baseStart_2448764 baseEnd_2448764 := by
    simpa [prefixWord, tailWord_2448764, baseEnd_2448764] using wordTrace_append hprefix tailTrace_2448764
  have hstable : (prefixWord ++ tailWord_2448764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448764).length < 2 ^ (prefixWord ++ tailWord_2448764).sum := by decide
  have hdescent : baseEnd_2448764 < baseStart_2448764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448771 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 6]
def baseStart_2448771 : Nat := 118140960795 + 2448771 * 2 ^ 59
def prefixEnd_2448771 : Nat := 4983230072969 + 3 ^ 40 * 2448771 * 2
def baseEnd_2448771 : Nat := 1257396535791143905900813

theorem tailTrace_2448771 : CollatzResearch.WordTrace tailWord_2448771 prefixEnd_2448771 1257396535791143905900813 := by
  unfold tailWord_2448771
  simp only [CollatzResearch.WordTrace]
  refine ⟨89314015811528358635970167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59542677207685572423980111 89314015811528358635970167)
  ·
    refine ⟨133971023717292537953955251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89314015811528358635970167 133971023717292537953955251)
    ·
      refine ⟨200956535575938806930932877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133971023717292537953955251 200956535575938806930932877)
      ·
        refine ⟨75358700840977052599099829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200956535575938806930932877 75358700840977052599099829)
        ·
          refine ⟨7064878203841598681165609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75358700840977052599099829 7064878203841598681165609)
          ·
            refine ⟨5298658652881199010874207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7064878203841598681165609 5298658652881199010874207)
            ·
              refine ⟨7947987979321798516311311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5298658652881199010874207 7947987979321798516311311)
              ·
                refine ⟨11921981968982697774466967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7947987979321798516311311 11921981968982697774466967)
                ·
                  refine ⟨17882972953474046661700451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11921981968982697774466967 17882972953474046661700451)
                  ·
                    refine ⟨26824459430211069992550677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17882972953474046661700451 26824459430211069992550677)
                    ·
                      refine ⟨1257396535791143905900813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26824459430211069992550677 1257396535791143905900813)
                      ·
                        rfl

theorem cell23_2448771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_2448771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448771 prefixEnd_2448771 := by exact prefixLift 2448771
  have htrace : WordTrace (prefixWord ++ tailWord_2448771) baseStart_2448771 baseEnd_2448771 := by
    simpa [prefixWord, tailWord_2448771, baseEnd_2448771] using wordTrace_append hprefix tailTrace_2448771
  have hstable : (prefixWord ++ tailWord_2448771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448771).length < 2 ^ (prefixWord ++ tailWord_2448771).sum := by decide
  have hdescent : baseEnd_2448771 < baseStart_2448771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448775 : List Nat := [1, 1, 4, 2, 2, 2, 2, 2, 3, 2, 2]
def baseStart_2448775 : Nat := 118140960795 + 2448775 * 2 ^ 59
def prefixEnd_2448775 : Nat := 4983230072969 + 3 ^ 40 * 2448775 * 2
def baseEnd_2448775 : Nat := 1257398589713761890250795

theorem tailTrace_2448775 : CollatzResearch.WordTrace tailWord_2448775 prefixEnd_2448775 1257398589713761890250795 := by
  unfold tailWord_2448775
  simp only [CollatzResearch.WordTrace]
  refine ⟨89314161703513867319115779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59542774469009244879410519 89314161703513867319115779)
  ·
    refine ⟨133971242555270800978673669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89314161703513867319115779 133971242555270800978673669)
    ·
      refine ⟨25119607979113275183501313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133971242555270800978673669 25119607979113275183501313)
      ·
        refine ⟨18839705984334956387625985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25119607979113275183501313 18839705984334956387625985)
        ·
          refine ⟨14129779488251217290719489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18839705984334956387625985 14129779488251217290719489)
          ·
            refine ⟨10597334616188412968039617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14129779488251217290719489 10597334616188412968039617)
            ·
              refine ⟨7948000962141309726029713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10597334616188412968039617 7948000962141309726029713)
              ·
                refine ⟨5961000721605982294522285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7948000962141309726029713 5961000721605982294522285)
                ·
                  refine ⟨2235375270602243360445857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5961000721605982294522285 2235375270602243360445857)
                  ·
                    refine ⟨1676531452951682520334393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2235375270602243360445857 1676531452951682520334393)
                    ·
                      refine ⟨1257398589713761890250795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1676531452951682520334393 1257398589713761890250795)
                      ·
                        rfl

theorem cell23_2448775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_2448775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448775 prefixEnd_2448775 := by exact prefixLift 2448775
  have htrace : WordTrace (prefixWord ++ tailWord_2448775) baseStart_2448775 baseEnd_2448775 := by
    simpa [prefixWord, tailWord_2448775, baseEnd_2448775] using wordTrace_append hprefix tailTrace_2448775
  have hstable : (prefixWord ++ tailWord_2448775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448775).length < 2 ^ (prefixWord ++ tailWord_2448775).sum := by decide
  have hdescent : baseEnd_2448775 < baseStart_2448775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448786 : List Nat := [3, 2, 3, 3, 1, 2, 1, 3, 1, 1, 3]
def baseStart_2448786 : Nat := 118140960795 + 2448786 * 2 ^ 59
def prefixEnd_2448786 : Nat := 4983230072969 + 3 ^ 40 * 2448786 * 2
def baseEnd_2448786 : Nat := 1257404238000961347213245

theorem tailTrace_2448786 : CollatzResearch.WordTrace tailWord_2448786 prefixEnd_2448786 1257404238000961347213245 := by
  unfold tailWord_2448786
  simp only [CollatzResearch.WordTrace]
  refine ⟨22328640726618504049441553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59543041937649344131844141 22328640726618504049441553)
  ·
    refine ⟨16746480544963878037081165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22328640726618504049441553 16746480544963878037081165)
    ·
      refine ⟨6279930204361454263905437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16746480544963878037081165 6279930204361454263905437)
      ·
        refine ⟨2354973826635545348964539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6279930204361454263905437 2354973826635545348964539)
        ·
          refine ⟨3532460739953318023446809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2354973826635545348964539 3532460739953318023446809)
          ·
            refine ⟨2649345554964988517585107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3532460739953318023446809 2649345554964988517585107)
            ·
              refine ⟨3974018332447482776377661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2649345554964988517585107 3974018332447482776377661)
              ·
                refine ⟨1490256874667806041141623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3974018332447482776377661 1490256874667806041141623)
                ·
                  refine ⟨2235385312001709061712435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1490256874667806041141623 2235385312001709061712435)
                  ·
                    refine ⟨3353077968002563592568653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2235385312001709061712435 3353077968002563592568653)
                    ·
                      refine ⟨1257404238000961347213245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3353077968002563592568653 1257404238000961347213245)
                      ·
                        rfl

theorem cell23_2448786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_2448786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448786 prefixEnd_2448786 := by exact prefixLift 2448786
  have htrace : WordTrace (prefixWord ++ tailWord_2448786) baseStart_2448786 baseEnd_2448786 := by
    simpa [prefixWord, tailWord_2448786, baseEnd_2448786] using wordTrace_append hprefix tailTrace_2448786
  have hstable : (prefixWord ++ tailWord_2448786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448786).length < 2 ^ (prefixWord ++ tailWord_2448786).sum := by decide
  have hdescent : baseEnd_2448786 < baseStart_2448786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448791 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 3]
def baseStart_2448791 : Nat := 118140960795 + 2448791 * 2 ^ 59
def prefixEnd_2448791 : Nat := 4983230072969 + 3 ^ 40 * 2448791 * 2
def baseEnd_2448791 : Nat := 1257406805404233827650721

theorem tailTrace_2448791 : CollatzResearch.WordTrace tailWord_2448791 prefixEnd_2448791 1257406805404233827650721 := by
  unfold tailWord_2448791
  simp only [CollatzResearch.WordTrace]
  refine ⟨89314745271455902051698227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59543163514303934701132151 89314745271455902051698227)
  ·
    refine ⟨133972117907183853077547341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89314745271455902051698227 133972117907183853077547341)
    ·
      refine ⟨50239544215193944904080253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133972117907183853077547341 50239544215193944904080253)
      ·
        refine ⟨18839829080697729339030095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50239544215193944904080253 18839829080697729339030095)
        ·
          refine ⟨28259743621046594008545143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18839829080697729339030095 28259743621046594008545143)
          ·
            refine ⟨42389615431569891012817715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28259743621046594008545143 42389615431569891012817715)
            ·
              refine ⟨63584423147354836519226573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42389615431569891012817715 63584423147354836519226573)
              ·
                refine ⟨23844158680258063694709965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63584423147354836519226573 23844158680258063694709965)
                ·
                  refine ⟨8941559505096773885516237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23844158680258063694709965 8941559505096773885516237)
                  ·
                    refine ⟨3353084814411290207068589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8941559505096773885516237 3353084814411290207068589)
                    ·
                      refine ⟨1257406805404233827650721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3353084814411290207068589 1257406805404233827650721)
                      ·
                        rfl

theorem cell23_2448791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_2448791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448791 prefixEnd_2448791 := by exact prefixLift 2448791
  have htrace : WordTrace (prefixWord ++ tailWord_2448791) baseStart_2448791 baseEnd_2448791 := by
    simpa [prefixWord, tailWord_2448791, baseEnd_2448791] using wordTrace_append hprefix tailTrace_2448791
  have hstable : (prefixWord ++ tailWord_2448791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448791).length < 2 ^ (prefixWord ++ tailWord_2448791).sum := by decide
  have hdescent : baseEnd_2448791 < baseStart_2448791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448835 : List Nat := [1, 1, 1, 3, 1, 1, 7, 2, 1, 3, 2]
def baseStart_2448835 : Nat := 118140960795 + 2448835 * 2 ^ 59
def prefixEnd_2448835 : Nat := 4983230072969 + 3 ^ 40 * 2448835 * 2
def baseEnd_2448835 : Nat := 1257429398553031655500519

theorem tailTrace_2448835 : CollatzResearch.WordTrace tailWord_2448835 prefixEnd_2448835 1257429398553031655500519 := by
  unfold tailWord_2448835
  simp only [CollatzResearch.WordTrace]
  refine ⟨89316350083296497566299959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59544233388864331710866639 89316350083296497566299959)
  ·
    refine ⟨133974525124944746349449939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89316350083296497566299959 133974525124944746349449939)
    ·
      refine ⟨200961787687417119524174909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133974525124944746349449939 200961787687417119524174909)
      ·
        refine ⟨75360670382781419821565591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200961787687417119524174909 75360670382781419821565591)
        ·
          refine ⟨113041005574172129732348387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75360670382781419821565591 113041005574172129732348387)
          ·
            refine ⟨169561508361258194598522581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113041005574172129732348387 169561508361258194598522581)
            ·
              refine ⟨3974097852216988935902873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 169561508361258194598522581 3974097852216988935902873)
              ·
                refine ⟨2980573389162741701927155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3974097852216988935902873 2980573389162741701927155)
                ·
                  refine ⟨4470860083744112552890733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2980573389162741701927155 4470860083744112552890733)
                  ·
                    refine ⟨1676572531404042207334025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4470860083744112552890733 1676572531404042207334025)
                    ·
                      refine ⟨1257429398553031655500519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1676572531404042207334025 1257429398553031655500519)
                      ·
                        rfl

theorem cell23_2448835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 3, 2].length) (baseStart_2448835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448835 prefixEnd_2448835 := by exact prefixLift 2448835
  have htrace : WordTrace (prefixWord ++ tailWord_2448835) baseStart_2448835 baseEnd_2448835 := by
    simpa [prefixWord, tailWord_2448835, baseEnd_2448835] using wordTrace_append hprefix tailTrace_2448835
  have hstable : (prefixWord ++ tailWord_2448835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448835).length < 2 ^ (prefixWord ++ tailWord_2448835).sum := by decide
  have hdescent : baseEnd_2448835 < baseStart_2448835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448848 : List Nat := [2, 1, 1, 1, 1, 2, 2, 6, 1, 4, 2]
def baseStart_2448848 : Nat := 118140960795 + 2448848 * 2 ^ 59
def prefixEnd_2448848 : Nat := 4983230072969 + 3 ^ 40 * 2448848 * 2
def baseEnd_2448848 : Nat := 1257436073801540104637959

theorem tailTrace_2448848 : CollatzResearch.WordTrace tailWord_2448848 prefixEnd_2448848 1257436073801540104637959 := by
  unfold tailWord_2448848
  simp only [CollatzResearch.WordTrace]
  refine ⟨44658412116124700393261599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59544549488166267191015465 44658412116124700393261599)
  ·
    refine ⟨66987618174187050589892399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44658412116124700393261599 66987618174187050589892399)
    ·
      refine ⟨100481427261280575884838599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66987618174187050589892399 100481427261280575884838599)
      ·
        refine ⟨150722140891920863827257899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100481427261280575884838599 150722140891920863827257899)
        ·
          refine ⟨226083211337881295740886849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150722140891920863827257899 226083211337881295740886849)
          ·
            refine ⟨169562408503410971805665137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226083211337881295740886849 169562408503410971805665137)
            ·
              refine ⟨127171806377558228854248853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169562408503410971805665137 127171806377558228854248853)
              ·
                refine ⟨5961178423948041977542915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 127171806377558228854248853 5961178423948041977542915)
                ·
                  refine ⟨8941767635922062966314373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5961178423948041977542915 8941767635922062966314373)
                  ·
                    refine ⟨1676581431735386806183945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8941767635922062966314373 1676581431735386806183945)
                    ·
                      refine ⟨1257436073801540104637959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1676581431735386806183945 1257436073801540104637959)
                      ·
                        rfl

theorem cell23_2448848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 1, 4, 2].length) (baseStart_2448848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448848 prefixEnd_2448848 := by exact prefixLift 2448848
  have htrace : WordTrace (prefixWord ++ tailWord_2448848) baseStart_2448848 baseEnd_2448848 := by
    simpa [prefixWord, tailWord_2448848, baseEnd_2448848] using wordTrace_append hprefix tailTrace_2448848
  have hstable : (prefixWord ++ tailWord_2448848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448848).length < 2 ^ (prefixWord ++ tailWord_2448848).sum := by decide
  have hdescent : baseEnd_2448848 < baseStart_2448848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448878 : List Nat := [4, 1, 2, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_2448878 : Nat := 118140960795 + 2448878 * 2 ^ 59
def prefixEnd_2448878 : Nat := 4983230072969 + 3 ^ 40 * 2448878 * 2
def baseEnd_2448878 : Nat := 1257451478221174987262821

theorem tailTrace_2448878 : CollatzResearch.WordTrace tailWord_2448878 prefixEnd_2448878 1257451478221174987262821 := by
  unfold tailWord_2448878
  simp only [CollatzResearch.WordTrace]
  refine ⟨11164739802767589488764411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59545278948093810606743525 11164739802767589488764411)
  ·
    refine ⟨16747109704151384233146617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11164739802767589488764411 16747109704151384233146617)
    ·
      refine ⟨12560332278113538174859963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16747109704151384233146617 12560332278113538174859963)
      ·
        refine ⟨18840498417170307262289945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12560332278113538174859963 18840498417170307262289945)
        ·
          refine ⟨14130373812877730446717459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18840498417170307262289945 14130373812877730446717459)
          ·
            refine ⟨21195560719316595670076189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14130373812877730446717459 21195560719316595670076189)
            ·
              refine ⟨7948335269743723376278571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21195560719316595670076189 7948335269743723376278571)
              ·
                refine ⟨11922502904615585064417857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7948335269743723376278571 11922502904615585064417857)
                ·
                  refine ⟨8941877178461688798313393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11922502904615585064417857 8941877178461688798313393)
                  ·
                    refine ⟨6706407883846266598735045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8941877178461688798313393 6706407883846266598735045)
                    ·
                      refine ⟨1257451478221174987262821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6706407883846266598735045 1257451478221174987262821)
                      ·
                        rfl

theorem cell23_2448878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_2448878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448878 prefixEnd_2448878 := by exact prefixLift 2448878
  have htrace : WordTrace (prefixWord ++ tailWord_2448878) baseStart_2448878 baseEnd_2448878 := by
    simpa [prefixWord, tailWord_2448878, baseEnd_2448878] using wordTrace_append hprefix tailTrace_2448878
  have hstable : (prefixWord ++ tailWord_2448878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448878).length < 2 ^ (prefixWord ++ tailWord_2448878).sum := by decide
  have hdescent : baseEnd_2448878 < baseStart_2448878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448882 : List Nat := [3, 2, 1, 4, 1, 2, 2, 1, 1, 4, 2]
def baseStart_2448882 : Nat := 118140960795 + 2448882 * 2 ^ 59
def prefixEnd_2448882 : Nat := 4983230072969 + 3 ^ 40 * 2448882 * 2
def baseEnd_2448882 : Nat := 1257453532143792971612803

theorem tailTrace_2448882 : CollatzResearch.WordTrace tailWord_2448882 prefixEnd_2448882 1257453532143792971612803 := by
  unfold tailWord_2448882
  simp only [CollatzResearch.WordTrace]
  refine ⟨22329516078531556148315225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59545376209417483062173933 22329516078531556148315225)
  ·
    refine ⟨16747137058898667111236419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22329516078531556148315225 16747137058898667111236419)
    ·
      refine ⟨25120705588348000666854629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16747137058898667111236419 25120705588348000666854629)
      ·
        refine ⟨4710132297815250125035243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25120705588348000666854629 4710132297815250125035243)
        ·
          refine ⟨7065198446722875187552865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4710132297815250125035243 7065198446722875187552865)
          ·
            refine ⟨5298898835042156390664649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7065198446722875187552865 5298898835042156390664649)
            ·
              refine ⟨3974174126281617292998487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5298898835042156390664649 3974174126281617292998487)
              ·
                refine ⟨5961261189422425939497731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3974174126281617292998487 5961261189422425939497731)
                ·
                  refine ⟨8941891784133638909246597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5961261189422425939497731 8941891784133638909246597)
                  ·
                    refine ⟨1676604709525057295483737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8941891784133638909246597 1676604709525057295483737)
                    ·
                      refine ⟨1257453532143792971612803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1676604709525057295483737 1257453532143792971612803)
                      ·
                        rfl

theorem cell23_2448882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_2448882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448882 prefixEnd_2448882 := by exact prefixLift 2448882
  have htrace : WordTrace (prefixWord ++ tailWord_2448882) baseStart_2448882 baseEnd_2448882 := by
    simpa [prefixWord, tailWord_2448882, baseEnd_2448882] using wordTrace_append hprefix tailTrace_2448882
  have hstable : (prefixWord ++ tailWord_2448882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448882).length < 2 ^ (prefixWord ++ tailWord_2448882).sum := by decide
  have hdescent : baseEnd_2448882 < baseStart_2448882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448921 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 5, 3, 4]
def baseStart_2448921 : Nat := 118140960795 + 2448921 * 2 ^ 59
def prefixEnd_2448921 : Nat := 4983230072969 + 3 ^ 40 * 2448921 * 2
def baseEnd_2448921 : Nat := 1257473557889318319025123

theorem tailTrace_2448921 : CollatzResearch.WordTrace tailWord_2448921 prefixEnd_2448921 1257473557889318319025123 := by
  unfold tailWord_2448921
  simp only [CollatzResearch.WordTrace]
  refine ⟨89319486760984934253930617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59546324507323289502620411 89319486760984934253930617)
  ·
    refine ⟨66989615070738700690447963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89319486760984934253930617 66989615070738700690447963)
    ·
      refine ⟨100484422606108051035671945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66989615070738700690447963 100484422606108051035671945)
      ·
        refine ⟨75363316954581038276753959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100484422606108051035671945 75363316954581038276753959)
        ·
          refine ⟨113044975431871557415130939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75363316954581038276753959 113044975431871557415130939)
          ·
            refine ⟨169567463147807336122696409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113044975431871557415130939 169567463147807336122696409)
            ·
              refine ⟨127175597360855502092022307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169567463147807336122696409 127175597360855502092022307)
              ·
                refine ⟨190763396041283253138033461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127175597360855502092022307 190763396041283253138033461)
                ·
                  refine ⟨17884068378870304981690637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190763396041283253138033461 17884068378870304981690637)
                  ·
                    refine ⟨6706525642076364368133989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17884068378870304981690637 6706525642076364368133989)
                    ·
                      refine ⟨1257473557889318319025123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6706525642076364368133989 1257473557889318319025123)
                      ·
                        rfl

theorem cell23_2448921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_2448921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448921 prefixEnd_2448921 := by exact prefixLift 2448921
  have htrace : WordTrace (prefixWord ++ tailWord_2448921) baseStart_2448921 baseEnd_2448921 := by
    simpa [prefixWord, tailWord_2448921, baseEnd_2448921] using wordTrace_append hprefix tailTrace_2448921
  have hstable : (prefixWord ++ tailWord_2448921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448921).length < 2 ^ (prefixWord ++ tailWord_2448921).sum := by decide
  have hdescent : baseEnd_2448921 < baseStart_2448921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448938 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_2448938 : Nat := 118140960795 + 2448938 * 2 ^ 59
def prefixEnd_2448938 : Nat := 4983230072969 + 3 ^ 40 * 2448938 * 2
def baseEnd_2448938 : Nat := 1257482287060444752512545

theorem tailTrace_2448938 : CollatzResearch.WordTrace tailWord_2448938 prefixEnd_2448938 1257482287060444752512545 := by
  unfold tailWord_2448938
  simp only [CollatzResearch.WordTrace]
  refine ⟨22330026700480836539324867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59546737867948897438199645 22330026700480836539324867)
  ·
    refine ⟨33495040050721254808987301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22330026700480836539324867 33495040050721254808987301)
    ·
      refine ⟨6280320009510235276685119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33495040050721254808987301 6280320009510235276685119)
      ·
        refine ⟨9420480014265352915027679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6280320009510235276685119 9420480014265352915027679)
        ·
          refine ⟨14130720021398029372541519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9420480014265352915027679 14130720021398029372541519)
          ·
            refine ⟨21196080032097044058812279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14130720021398029372541519 21196080032097044058812279)
            ·
              refine ⟨31794120048145566088218419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21196080032097044058812279 31794120048145566088218419)
              ·
                refine ⟨47691180072218349132327629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31794120048145566088218419 47691180072218349132327629)
                ·
                  refine ⟨17884192527081880924622861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47691180072218349132327629 17884192527081880924622861)
                  ·
                    refine ⟨6706572197655705346733573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17884192527081880924622861 6706572197655705346733573)
                    ·
                      refine ⟨1257482287060444752512545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6706572197655705346733573 1257482287060444752512545)
                      ·
                        rfl

theorem cell23_2448938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_2448938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448938 prefixEnd_2448938 := by exact prefixLift 2448938
  have htrace : WordTrace (prefixWord ++ tailWord_2448938) baseStart_2448938 baseEnd_2448938 := by
    simpa [prefixWord, tailWord_2448938, baseEnd_2448938] using wordTrace_append hprefix tailTrace_2448938
  have hstable : (prefixWord ++ tailWord_2448938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448938).length < 2 ^ (prefixWord ++ tailWord_2448938).sum := by decide
  have hdescent : baseEnd_2448938 < baseStart_2448938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448978 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 8]
def baseStart_2448978 : Nat := 118140960795 + 2448978 * 2 ^ 59
def prefixEnd_2448978 : Nat := 4983230072969 + 3 ^ 40 * 2448978 * 2
def baseEnd_2448978 : Nat := 139722536254069399556929

theorem tailTrace_2448978 : CollatzResearch.WordTrace tailWord_2448978 prefixEnd_2448978 139722536254069399556929 := by
  unfold tailWord_2448978
  simp only [CollatzResearch.WordTrace]
  refine ⟨22330391430444608247188897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59547710481185621992503725 22330391430444608247188897)
  ·
    refine ⟨16747793572833456185391673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22330391430444608247188897 16747793572833456185391673)
    ·
      refine ⟨12560845179625092139043755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16747793572833456185391673 12560845179625092139043755)
      ·
        refine ⟨18841267769437638208565633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12560845179625092139043755 18841267769437638208565633)
        ·
          refine ⟨14130950827078228656424225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18841267769437638208565633 14130950827078228656424225)
          ·
            refine ⟨10598213120308671492318169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14130950827078228656424225 10598213120308671492318169)
            ·
              refine ⟨7948659840231503619238627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10598213120308671492318169 7948659840231503619238627)
              ·
                refine ⟨11922989760347255428857941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7948659840231503619238627 11922989760347255428857941)
                ·
                  refine ⟨139722536254069399556929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11922989760347255428857941 139722536254069399556929)
                  ·
                    rfl

theorem cell23_2448978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_2448978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448978 prefixEnd_2448978 := by exact prefixLift 2448978
  have htrace : WordTrace (prefixWord ++ tailWord_2448978) baseStart_2448978 baseEnd_2448978 := by
    simpa [prefixWord, tailWord_2448978, baseEnd_2448978] using wordTrace_append hprefix tailTrace_2448978
  have hstable : (prefixWord ++ tailWord_2448978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448978).length < 2 ^ (prefixWord ++ tailWord_2448978).sum := by decide
  have hdescent : baseEnd_2448978 < baseStart_2448978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448991 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 1, 11]
def baseStart_2448991 : Nat := 118140960795 + 2448991 * 2 ^ 59
def prefixEnd_2448991 : Nat := 4983230072969 + 3 ^ 40 * 2448991 * 2
def baseEnd_2448991 : Nat := 419169833845044348383267

theorem tailTrace_2448991 : CollatzResearch.WordTrace tailWord_2448991 prefixEnd_2448991 419169833845044348383267 := by
  unfold tailWord_2448991
  simp only [CollatzResearch.WordTrace]
  refine ⟨89322039870731336208978827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59548026580487557472652551 89322039870731336208978827)
  ·
    refine ⟨133983059806097004313468241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89322039870731336208978827 133983059806097004313468241)
    ·
      refine ⟨100487294854572753235101181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133983059806097004313468241 100487294854572753235101181)
      ·
        refine ⟨37682735570464782463162943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100487294854572753235101181 37682735570464782463162943)
        ·
          refine ⟨56524103355697173694744415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37682735570464782463162943 56524103355697173694744415)
          ·
            refine ⟨84786155033545760542116623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56524103355697173694744415 84786155033545760542116623)
            ·
              refine ⟨127179232550318640813174935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84786155033545760542116623 127179232550318640813174935)
              ·
                refine ⟨190768848825477961219762403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127179232550318640813174935 190768848825477961219762403)
                ·
                  refine ⟨286153273238216941829643605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190768848825477961219762403 286153273238216941829643605)
                  ·
                    refine ⟨419169833845044348383267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 286153273238216941829643605 419169833845044348383267)
                    ·
                      rfl

theorem cell23_2448991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 11].length) (baseStart_2448991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448991 prefixEnd_2448991 := by exact prefixLift 2448991
  have htrace : WordTrace (prefixWord ++ tailWord_2448991) baseStart_2448991 baseEnd_2448991 := by
    simpa [prefixWord, tailWord_2448991, baseEnd_2448991] using wordTrace_append hprefix tailTrace_2448991
  have hstable : (prefixWord ++ tailWord_2448991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448991).length < 2 ^ (prefixWord ++ tailWord_2448991).sum := by decide
  have hdescent : baseEnd_2448991 < baseStart_2448991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2448995 : List Nat := [1, 1, 1, 5, 1, 3, 4, 1, 6]
def baseStart_2448995 : Nat := 118140960795 + 2448995 * 2 ^ 59
def prefixEnd_2448995 : Nat := 4983230072969 + 3 ^ 40 * 2448995 * 2
def baseEnd_2448995 : Nat := 139723506161972336611087

theorem tailTrace_2448995 : CollatzResearch.WordTrace tailWord_2448995 prefixEnd_2448995 139723506161972336611087 := by
  unfold tailWord_2448995
  simp only [CollatzResearch.WordTrace]
  refine ⟨89322185762716844892124439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59548123841811229928082959 89322185762716844892124439)
  ·
    refine ⟨133983278644075267338186659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89322185762716844892124439 133983278644075267338186659)
    ·
      refine ⟨200974917966112901007279989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133983278644075267338186659 200974917966112901007279989)
      ·
        refine ⟨18841398559323084469432499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 200974917966112901007279989 18841398559323084469432499)
        ·
          refine ⟨28262097838984626704148749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18841398559323084469432499 28262097838984626704148749)
          ·
            refine ⟨10598286689619235014055781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28262097838984626704148749 10598286689619235014055781)
            ·
              refine ⟨1987178754303606565135459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10598286689619235014055781 1987178754303606565135459)
              ·
                refine ⟨2980768131455409847703189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1987178754303606565135459 2980768131455409847703189)
                ·
                  refine ⟨139723506161972336611087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2980768131455409847703189 139723506161972336611087)
                  ·
                    rfl

theorem cell23_2448995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 6].length) (baseStart_2448995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2448995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2448995 prefixEnd_2448995 := by exact prefixLift 2448995
  have htrace : WordTrace (prefixWord ++ tailWord_2448995) baseStart_2448995 baseEnd_2448995 := by
    simpa [prefixWord, tailWord_2448995, baseEnd_2448995] using wordTrace_append hprefix tailTrace_2448995
  have hstable : (prefixWord ++ tailWord_2448995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2448995).length < 2 ^ (prefixWord ++ tailWord_2448995).sum := by decide
  have hdescent : baseEnd_2448995 < baseStart_2448995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2448995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449079 : List Nat := [1, 1, 3, 1, 5, 3, 2, 1, 1, 1, 4]
def baseStart_2449079 : Nat := 118140960795 + 2449079 * 2 ^ 59
def prefixEnd_2449079 : Nat := 4983230072969 + 3 ^ 40 * 2449079 * 2
def baseEnd_2449079 : Nat := 1257554687832728700849397

theorem tailTrace_2449079 : CollatzResearch.WordTrace tailWord_2449079 prefixEnd_2449079 1257554687832728700849397 := by
  unfold tailWord_2449079
  simp only [CollatzResearch.WordTrace]
  refine ⟨89325249494412527238182291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59550166329608351492121527 89325249494412527238182291)
  ·
    refine ⟨133987874241618790857273437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89325249494412527238182291 133987874241618790857273437)
    ·
      refine ⟨50245452840607046571477539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133987874241618790857273437 50245452840607046571477539)
      ·
        refine ⟨75368179260910569857216309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50245452840607046571477539 75368179260910569857216309)
        ·
          refine ⟨7065766805710365924114029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75368179260910569857216309 7065766805710365924114029)
          ·
            refine ⟨2649662552141387221542761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7065766805710365924114029 2649662552141387221542761)
            ·
              refine ⟨1987246914106040416157071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2649662552141387221542761 1987246914106040416157071)
              ·
                refine ⟨2980870371159060624235607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1987246914106040416157071 2980870371159060624235607)
                ·
                  refine ⟨4471305556738590936353411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2980870371159060624235607 4471305556738590936353411)
                  ·
                    refine ⟨6706958335107886404530117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4471305556738590936353411 6706958335107886404530117)
                    ·
                      refine ⟨1257554687832728700849397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6706958335107886404530117 1257554687832728700849397)
                      ·
                        rfl

theorem cell23_2449079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 2, 1, 1, 1, 4].length) (baseStart_2449079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449079 prefixEnd_2449079 := by exact prefixLift 2449079
  have htrace : WordTrace (prefixWord ++ tailWord_2449079) baseStart_2449079 baseEnd_2449079 := by
    simpa [prefixWord, tailWord_2449079, baseEnd_2449079] using wordTrace_append hprefix tailTrace_2449079
  have hstable : (prefixWord ++ tailWord_2449079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449079).length < 2 ^ (prefixWord ++ tailWord_2449079).sum := by decide
  have hdescent : baseEnd_2449079 < baseStart_2449079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449082 : List Nat := [3, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3]
def baseStart_2449082 : Nat := 118140960795 + 2449082 * 2 ^ 59
def prefixEnd_2449082 : Nat := 4983230072969 + 3 ^ 40 * 2449082 * 2
def baseEnd_2449082 : Nat := 1257556228274692189111883

theorem tailTrace_2449082 : CollatzResearch.WordTrace tailWord_2449082 prefixEnd_2449082 1257556228274692189111883 := by
  unfold tailWord_2449082
  simp only [CollatzResearch.WordTrace]
  refine ⟨22331339728350414687635375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59550239275601105833694333 22331339728350414687635375)
  ·
    refine ⟨33497009592525622031453063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22331339728350414687635375 33497009592525622031453063)
    ·
      refine ⟨50245514388788433047179595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33497009592525622031453063 50245514388788433047179595)
      ·
        refine ⟨75368271583182649570769393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50245514388788433047179595 75368271583182649570769393)
        ·
          refine ⟨56526203687386987178077045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75368271583182649570769393 56526203687386987178077045)
          ·
            refine ⟨5299331595692530047944723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56526203687386987178077045 5299331595692530047944723)
            ·
              refine ⟨7948997393538795071917085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5299331595692530047944723 7948997393538795071917085)
              ·
                refine ⟨2980874022577048151968907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7948997393538795071917085 2980874022577048151968907)
                ·
                  refine ⟨4471311033865572227953361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2980874022577048151968907 4471311033865572227953361)
                  ·
                    refine ⟨3353483275399179170965021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4471311033865572227953361 3353483275399179170965021)
                    ·
                      refine ⟨1257556228274692189111883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3353483275399179170965021 1257556228274692189111883)
                      ·
                        rfl

theorem cell23_2449082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3].length) (baseStart_2449082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449082 prefixEnd_2449082 := by exact prefixLift 2449082
  have htrace : WordTrace (prefixWord ++ tailWord_2449082) baseStart_2449082 baseEnd_2449082 := by
    simpa [prefixWord, tailWord_2449082, baseEnd_2449082] using wordTrace_append hprefix tailTrace_2449082
  have hstable : (prefixWord ++ tailWord_2449082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449082).length < 2 ^ (prefixWord ++ tailWord_2449082).sum := by decide
  have hdescent : baseEnd_2449082 < baseStart_2449082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449116 : List Nat := [2, 2, 5, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_2449116 : Nat := 118140960795 + 2449116 * 2 ^ 59
def prefixEnd_2449116 : Nat := 4983230072969 + 3 ^ 40 * 2449116 * 2
def baseEnd_2449116 : Nat := 1257573686616945056086727

theorem tailTrace_2449116 : CollatzResearch.WordTrace tailWord_2449116 prefixEnd_2449116 1257573686616945056086727 := by
  unfold tailWord_2449116
  simp only [CollatzResearch.WordTrace]
  refine ⟨44663299497639241278639601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59551065996852321704852801 44663299497639241278639601)
  ·
    refine ⟨33497474623229430958979701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44663299497639241278639601 33497474623229430958979701)
    ·
      refine ⟨3140388245927759152404347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33497474623229430958979701 3140388245927759152404347)
      ·
        refine ⟨4710582368891638728606521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3140388245927759152404347 4710582368891638728606521)
        ·
          refine ⟨3532936776668729046454891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4710582368891638728606521 3532936776668729046454891)
          ·
            refine ⟨5299405165003093569682337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3532936776668729046454891 5299405165003093569682337)
            ·
              refine ⟨3974553873752320177261753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5299405165003093569682337 3974553873752320177261753)
              ·
                refine ⟨2980915405314240132946315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3974553873752320177261753 2980915405314240132946315)
                ·
                  refine ⟨4471373107971360199419473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2980915405314240132946315 4471373107971360199419473)
                  ·
                    refine ⟨3353529830978520149564605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4471373107971360199419473 3353529830978520149564605)
                    ·
                      refine ⟨1257573686616945056086727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3353529830978520149564605 1257573686616945056086727)
                      ·
                        rfl

theorem cell23_2449116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_2449116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449116 prefixEnd_2449116 := by exact prefixLift 2449116
  have htrace : WordTrace (prefixWord ++ tailWord_2449116) baseStart_2449116 baseEnd_2449116 := by
    simpa [prefixWord, tailWord_2449116, baseEnd_2449116] using wordTrace_append hprefix tailTrace_2449116
  have hstable : (prefixWord ++ tailWord_2449116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449116).length < 2 ^ (prefixWord ++ tailWord_2449116).sum := by decide
  have hdescent : baseEnd_2449116 < baseStart_2449116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449212 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 2, 5, 2]
def baseStart_2449212 : Nat := 118140960795 + 2449212 * 2 ^ 59
def prefixEnd_2449212 : Nat := 4983230072969 + 3 ^ 40 * 2449212 * 2
def baseEnd_2449212 : Nat := 1257622980759776680486285

theorem tailTrace_2449212 : CollatzResearch.WordTrace tailWord_2449212 prefixEnd_2449212 1257622980759776680486285 := by
  unfold tailWord_2449212
  simp only [CollatzResearch.WordTrace]
  refine ⟨44665050201465345476386945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59553400268620460635182593 44665050201465345476386945)
  ·
    refine ⟨33498787651099009107290209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44665050201465345476386945 33498787651099009107290209)
    ·
      refine ⟨25124090738324256830467657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33498787651099009107290209 25124090738324256830467657)
      ·
        refine ⟨18843068053743192622850743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25124090738324256830467657 18843068053743192622850743)
        ·
          refine ⟨28264602080614788934276115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18843068053743192622850743 28264602080614788934276115)
          ·
            refine ⟨42396903120922183401414173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28264602080614788934276115 42396903120922183401414173)
            ·
              refine ⟨15898838670345818775530315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42396903120922183401414173 15898838670345818775530315)
              ·
                refine ⟨23848258005518728163295473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15898838670345818775530315 23848258005518728163295473)
                ·
                  refine ⟨17886193504139046122471605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23848258005518728163295473 17886193504139046122471605)
                  ·
                    refine ⟨1676830641013035573981713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17886193504139046122471605 1676830641013035573981713)
                    ·
                      refine ⟨1257622980759776680486285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1676830641013035573981713 1257622980759776680486285)
                      ·
                        rfl

theorem cell23_2449212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_2449212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449212 prefixEnd_2449212 := by exact prefixLift 2449212
  have htrace : WordTrace (prefixWord ++ tailWord_2449212) baseStart_2449212 baseEnd_2449212 := by
    simpa [prefixWord, tailWord_2449212, baseEnd_2449212] using wordTrace_append hprefix tailTrace_2449212
  have hstable : (prefixWord ++ tailWord_2449212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449212).length < 2 ^ (prefixWord ++ tailWord_2449212).sum := by decide
  have hdescent : baseEnd_2449212 < baseStart_2449212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449225 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 1, 3, 4]
def baseStart_2449225 : Nat := 118140960795 + 2449225 * 2 ^ 59
def prefixEnd_2449225 : Nat := 4983230072969 + 3 ^ 40 * 2449225 * 2
def baseEnd_2449225 : Nat := 1257629656008285129623725

theorem tailTrace_2449225 : CollatzResearch.WordTrace tailWord_2449225 prefixEnd_2449225 1257629656008285129623725 := by
  unfold tailWord_2449225
  simp only [CollatzResearch.WordTrace]
  refine ⟨89330574551883594172997129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59553716367922396115331419 89330574551883594172997129)
  ·
    refine ⟨66997930913912695629747847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89330574551883594172997129 66997930913912695629747847)
    ·
      refine ⟨100496896370869043444621771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66997930913912695629747847 100496896370869043444621771)
      ·
        refine ⟨150745344556303565166932657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100496896370869043444621771 150745344556303565166932657)
        ·
          refine ⟨113059008417227673875199493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150745344556303565166932657 113059008417227673875199493)
          ·
            refine ⟨21198564078230188851599905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113059008417227673875199493 21198564078230188851599905)
            ·
              refine ⟨15898923058672641638699929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21198564078230188851599905 15898923058672641638699929)
              ·
                refine ⟨11924192294004481229024947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15898923058672641638699929 11924192294004481229024947)
                ·
                  refine ⟨17886288441006721843537421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11924192294004481229024947 17886288441006721843537421)
                  ·
                    refine ⟨6707358165377520691326533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17886288441006721843537421 6707358165377520691326533)
                    ·
                      refine ⟨1257629656008285129623725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6707358165377520691326533 1257629656008285129623725)
                      ·
                        rfl

theorem cell23_2449225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_2449225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449225 prefixEnd_2449225 := by exact prefixLift 2449225
  have htrace : WordTrace (prefixWord ++ tailWord_2449225) baseStart_2449225 baseEnd_2449225 := by
    simpa [prefixWord, tailWord_2449225, baseEnd_2449225] using wordTrace_append hprefix tailTrace_2449225
  have hstable : (prefixWord ++ tailWord_2449225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449225).length < 2 ^ (prefixWord ++ tailWord_2449225).sum := by decide
  have hdescent : baseEnd_2449225 < baseStart_2449225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449239 : List Nat := [1, 1, 3, 2, 5, 2, 1, 1, 2, 5]
def baseStart_2449239 : Nat := 118140960795 + 2449239 * 2 ^ 59
def prefixEnd_2449239 : Nat := 4983230072969 + 3 ^ 40 * 2449239 * 2
def baseEnd_2449239 : Nat := 419212281579149358282887

theorem tailTrace_2449239 : CollatzResearch.WordTrace tailWord_2449239 prefixEnd_2449239 419212281579149358282887 := by
  unfold tailWord_2449239
  simp only [CollatzResearch.WordTrace]
  refine ⟨89331085173832874564006771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59554056782555249709337847 89331085173832874564006771)
  ·
    refine ⟨133996627760749311846010157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89331085173832874564006771 133996627760749311846010157)
    ·
      refine ⟨50248735410280991942253809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133996627760749311846010157 50248735410280991942253809)
      ·
        refine ⟨37686551557710743956690357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50248735410280991942253809 37686551557710743956690357)
        ·
          refine ⟨3533114208535382245939721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37686551557710743956690357 3533114208535382245939721)
          ·
            refine ⟨2649835656401536684454791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3533114208535382245939721 2649835656401536684454791)
            ·
              refine ⟨3974753484602305026682187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2649835656401536684454791 3974753484602305026682187)
              ·
                refine ⟨5962130226903457540023281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3974753484602305026682187 5962130226903457540023281)
                ·
                  refine ⟨4471597670177593155017461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5962130226903457540023281 4471597670177593155017461)
                  ·
                    refine ⟨419212281579149358282887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4471597670177593155017461 419212281579149358282887)
                    ·
                      rfl

theorem cell23_2449239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_2449239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449239 prefixEnd_2449239 := by exact prefixLift 2449239
  have htrace : WordTrace (prefixWord ++ tailWord_2449239) baseStart_2449239 baseEnd_2449239 := by
    simpa [prefixWord, tailWord_2449239, baseEnd_2449239] using wordTrace_append hprefix tailTrace_2449239
  have hstable : (prefixWord ++ tailWord_2449239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449239).length < 2 ^ (prefixWord ++ tailWord_2449239).sum := by decide
  have hdescent : baseEnd_2449239 < baseStart_2449239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449242 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2]
def baseStart_2449242 : Nat := 118140960795 + 2449242 * 2 ^ 59
def prefixEnd_2449242 : Nat := 4983230072969 + 3 ^ 40 * 2449242 * 2
def baseEnd_2449242 : Nat := 1257638385179411563111147

theorem tailTrace_2449242 : CollatzResearch.WordTrace tailWord_2449242 prefixEnd_2449242 1257638385179411563111147 := by
  unfold tailWord_2449242
  simp only [CollatzResearch.WordTrace]
  refine ⟨22332798648205501519091495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59554129728548004050910653 22332798648205501519091495)
  ·
    refine ⟨33499197972308252278637243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22332798648205501519091495 33499197972308252278637243)
    ·
      refine ⟨50248796958462378417955865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33499197972308252278637243 50248796958462378417955865)
      ·
        refine ⟨37686597718846783813466899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50248796958462378417955865 37686597718846783813466899)
        ·
          refine ⟨56529896578270175720200349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37686597718846783813466899 56529896578270175720200349)
          ·
            refine ⟨21198711216851315895075131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56529896578270175720200349 21198711216851315895075131)
            ·
              refine ⟨31798066825276973842612697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21198711216851315895075131 31798066825276973842612697)
              ·
                refine ⟨23848550118957730381959523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31798066825276973842612697 23848550118957730381959523)
                ·
                  refine ⟨35772825178436595572939285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23848550118957730381959523 35772825178436595572939285)
                  ·
                    refine ⟨1676851180239215417481529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35772825178436595572939285 1676851180239215417481529)
                    ·
                      refine ⟨1257638385179411563111147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1676851180239215417481529 1257638385179411563111147)
                      ·
                        rfl

theorem cell23_2449242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_2449242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449242 prefixEnd_2449242 := by exact prefixLift 2449242
  have htrace : WordTrace (prefixWord ++ tailWord_2449242) baseStart_2449242 baseEnd_2449242 := by
    simpa [prefixWord, tailWord_2449242, baseEnd_2449242] using wordTrace_append hprefix tailTrace_2449242
  have hstable : (prefixWord ++ tailWord_2449242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449242).length < 2 ^ (prefixWord ++ tailWord_2449242).sum := by decide
  have hdescent : baseEnd_2449242 < baseStart_2449242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449255 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_2449255 : Nat := 118140960795 + 2449255 * 2 ^ 59
def prefixEnd_2449255 : Nat := 4983230072969 + 3 ^ 40 * 2449255 * 2
def baseEnd_2449255 : Nat := 1257645060427920012248587

theorem tailTrace_2449255 : CollatzResearch.WordTrace tailWord_2449255 prefixEnd_2449255 1257645060427920012248587 := by
  unfold tailWord_2449255
  simp only [CollatzResearch.WordTrace]
  refine ⟨89331668741774909296589219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59554445827849939531059479 89331668741774909296589219)
  ·
    refine ⟨133997503112662363944883829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89331668741774909296589219 133997503112662363944883829)
    ·
      refine ⟨12562265916812096619832859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133997503112662363944883829 12562265916812096619832859)
      ·
        refine ⟨18843398875218144929749289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12562265916812096619832859 18843398875218144929749289)
        ·
          refine ⟨14132549156413608697311967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18843398875218144929749289 14132549156413608697311967)
          ·
            refine ⟨21198823734620413045967951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14132549156413608697311967 21198823734620413045967951)
            ·
              refine ⟨31798235601930619568951927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21198823734620413045967951 31798235601930619568951927)
              ·
                refine ⟨47697353402895929353427891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31798235601930619568951927 47697353402895929353427891)
                ·
                  refine ⟨71546030104343894030141837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47697353402895929353427891 71546030104343894030141837)
                  ·
                    refine ⟨26829761289128960261303189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71546030104343894030141837 26829761289128960261303189)
                    ·
                      refine ⟨1257645060427920012248587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26829761289128960261303189 1257645060427920012248587)
                      ·
                        rfl

theorem cell23_2449255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_2449255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449255 prefixEnd_2449255 := by exact prefixLift 2449255
  have htrace : WordTrace (prefixWord ++ tailWord_2449255) baseStart_2449255 baseEnd_2449255 := by
    simpa [prefixWord, tailWord_2449255, baseEnd_2449255] using wordTrace_append hprefix tailTrace_2449255
  have hstable : (prefixWord ++ tailWord_2449255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449255).length < 2 ^ (prefixWord ++ tailWord_2449255).sum := by decide
  have hdescent : baseEnd_2449255 < baseStart_2449255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449265 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 8]
def baseStart_2449265 : Nat := 118140960795 + 2449265 * 2 ^ 59
def prefixEnd_2449265 : Nat := 4983230072969 + 3 ^ 40 * 2449265 * 2
def baseEnd_2449265 : Nat := 139738910581607219235949

theorem tailTrace_2449265 : CollatzResearch.WordTrace tailWord_2449265 prefixEnd_2449265 139738910581607219235949 := by
  unfold tailWord_2449265
  simp only [CollatzResearch.WordTrace]
  refine ⟨89332033471738681004453249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59554688981159120669635499 89332033471738681004453249)
  ·
    refine ⟨66999025103804010753339937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89332033471738681004453249 66999025103804010753339937)
    ·
      refine ⟨50249268827853008065004953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66999025103804010753339937 50249268827853008065004953)
      ·
        refine ⟨37686951620889756048753715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50249268827853008065004953 37686951620889756048753715)
        ·
          refine ⟨56530427431334634073130573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37686951620889756048753715 56530427431334634073130573)
          ·
            refine ⟨21198910286750487777423965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56530427431334634073130573 21198910286750487777423965)
            ·
              refine ⟨7949591357531432916533987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21198910286750487777423965 7949591357531432916533987)
              ·
                refine ⟨11924387036297149374800981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7949591357531432916533987 11924387036297149374800981)
                ·
                  refine ⟨139738910581607219235949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11924387036297149374800981 139738910581607219235949)
                  ·
                    rfl

theorem cell23_2449265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 8].length) (baseStart_2449265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449265 prefixEnd_2449265 := by exact prefixLift 2449265
  have htrace : WordTrace (prefixWord ++ tailWord_2449265) baseStart_2449265 baseEnd_2449265 := by
    simpa [prefixWord, tailWord_2449265, baseEnd_2449265] using wordTrace_append hprefix tailTrace_2449265
  have hstable : (prefixWord ++ tailWord_2449265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449265).length < 2 ^ (prefixWord ++ tailWord_2449265).sum := by decide
  have hdescent : baseEnd_2449265 < baseStart_2449265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449269 : List Nat := [1, 3, 4, 1, 1, 1, 4, 1, 3, 4]
def baseStart_2449269 : Nat := 118140960795 + 2449269 * 2 ^ 59
def prefixEnd_2449269 : Nat := 4983230072969 + 3 ^ 40 * 2449269 * 2
def baseEnd_2449269 : Nat := 419217416385694319157841

theorem tailTrace_2449269 : CollatzResearch.WordTrace tailWord_2449269 prefixEnd_2449269 419217416385694319157841 := by
  unfold tailWord_2449269
  simp only [CollatzResearch.WordTrace]
  refine ⟨89332179363724189687598861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59554786242482793125065907 89332179363724189687598861)
  ·
    refine ⟨33499567261396571132849573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89332179363724189687598861 33499567261396571132849573)
    ·
      refine ⟨6281168861511857087409295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33499567261396571132849573 6281168861511857087409295)
      ·
        refine ⟨9421753292267785631113943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6281168861511857087409295 9421753292267785631113943)
        ·
          refine ⟨14132629938401678446670915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9421753292267785631113943 14132629938401678446670915)
          ·
            refine ⟨21198944907602517670006373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14132629938401678446670915 21198944907602517670006373)
            ·
              refine ⟨3974802170175472063126195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21198944907602517670006373 3974802170175472063126195)
              ·
                refine ⟨5962203255263208094689293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3974802170175472063126195 5962203255263208094689293)
                ·
                  refine ⟨2235826220723703035508485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5962203255263208094689293 2235826220723703035508485)
                  ·
                    refine ⟨419217416385694319157841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2235826220723703035508485 419217416385694319157841)
                    ·
                      rfl

theorem cell23_2449269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_2449269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449269 prefixEnd_2449269 := by exact prefixLift 2449269
  have htrace : WordTrace (prefixWord ++ tailWord_2449269) baseStart_2449269 baseEnd_2449269 := by
    simpa [prefixWord, tailWord_2449269, baseEnd_2449269] using wordTrace_append hprefix tailTrace_2449269
  have hstable : (prefixWord ++ tailWord_2449269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449269).length < 2 ^ (prefixWord ++ tailWord_2449269).sum := by decide
  have hdescent : baseEnd_2449269 < baseStart_2449269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449285 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 1, 2, 6]
def baseStart_2449285 : Nat := 118140960795 + 2449285 * 2 ^ 59
def prefixEnd_2449285 : Nat := 4983230072969 + 3 ^ 40 * 2449285 * 2
def baseEnd_2449285 : Nat := 1257660464847554894873449

theorem tailTrace_2449285 : CollatzResearch.WordTrace tailWord_2449285 prefixEnd_2449285 1257660464847554894873449 := by
  unfold tailWord_2449285
  simp only [CollatzResearch.WordTrace]
  refine ⟨89332762931666224420181309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59555175287777482946787539 89332762931666224420181309)
  ·
    refine ⟨33499786099374834157567991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89332762931666224420181309 33499786099374834157567991)
    ·
      refine ⟨50249679149062251236351987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33499786099374834157567991 50249679149062251236351987)
      ·
        refine ⟨75374518723593376854527981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50249679149062251236351987 75374518723593376854527981)
        ·
          refine ⟨28265444521347516320447993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75374518723593376854527981 28265444521347516320447993)
          ·
            refine ⟨21199083391010637240335995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28265444521347516320447993 21199083391010637240335995)
            ·
              refine ⟨31798625086515955860503993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21199083391010637240335995 31798625086515955860503993)
              ·
                refine ⟨23848968814886966895377995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31798625086515955860503993 23848968814886966895377995)
                ·
                  refine ⟨35773453222330450343066993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23848968814886966895377995 35773453222330450343066993)
                  ·
                    refine ⟨26830089916747837757300245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35773453222330450343066993 26830089916747837757300245)
                    ·
                      refine ⟨1257660464847554894873449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26830089916747837757300245 1257660464847554894873449)
                      ·
                        rfl

theorem cell23_2449285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_2449285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449285 prefixEnd_2449285 := by exact prefixLift 2449285
  have htrace : WordTrace (prefixWord ++ tailWord_2449285) baseStart_2449285 baseEnd_2449285 := by
    simpa [prefixWord, tailWord_2449285, baseEnd_2449285] using wordTrace_append hprefix tailTrace_2449285
  have hstable : (prefixWord ++ tailWord_2449285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449285).length < 2 ^ (prefixWord ++ tailWord_2449285).sum := by decide
  have hdescent : baseEnd_2449285 < baseStart_2449285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449295 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 9, 5]
def baseStart_2449295 : Nat := 118140960795 + 2449295 * 2 ^ 59
def prefixEnd_2449295 : Nat := 4983230072969 + 3 ^ 40 * 2449295 * 2
def baseEnd_2449295 : Nat := 419221866551366618582801

theorem tailTrace_2449295 : CollatzResearch.WordTrace tailWord_2449295 prefixEnd_2449295 419221866551366618582801 := by
  unfold tailWord_2449295
  simp only [CollatzResearch.WordTrace]
  refine ⟨89333127661629996128045339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59555418441086664085363559 89333127661629996128045339)
  ·
    refine ⟨133999691492444994192068009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89333127661629996128045339 133999691492444994192068009)
    ·
      refine ⟨100499768619333745644051007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133999691492444994192068009 100499768619333745644051007)
      ·
        refine ⟨150749652929000618466076511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100499768619333745644051007 150749652929000618466076511)
        ·
          refine ⟨226124479393500927699114767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150749652929000618466076511 226124479393500927699114767)
          ·
            refine ⟨339186719090251391548672151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226124479393500927699114767 339186719090251391548672151)
            ·
              refine ⟨508780078635377087323008227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339186719090251391548672151 508780078635377087323008227)
              ·
                refine ⟨763170117953065630984512341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508780078635377087323008227 763170117953065630984512341)
                ·
                  refine ⟨4471699909881243931549877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 763170117953065630984512341 4471699909881243931549877)
                  ·
                    refine ⟨419221866551366618582801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4471699909881243931549877 419221866551366618582801)
                    ·
                      rfl

theorem cell23_2449295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 9, 5].length) (baseStart_2449295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449295 prefixEnd_2449295 := by exact prefixLift 2449295
  have htrace : WordTrace (prefixWord ++ tailWord_2449295) baseStart_2449295 baseEnd_2449295 := by
    simpa [prefixWord, tailWord_2449295, baseEnd_2449295] using wordTrace_append hprefix tailTrace_2449295
  have hstable : (prefixWord ++ tailWord_2449295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449295).length < 2 ^ (prefixWord ++ tailWord_2449295).sum := by decide
  have hdescent : baseEnd_2449295 < baseStart_2449295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449320 : List Nat := [2, 1, 6, 2, 2, 1, 1, 1, 3, 4]
def baseStart_2449320 : Nat := 118140960795 + 2449320 * 2 ^ 59
def prefixEnd_2449320 : Nat := 4983230072969 + 3 ^ 40 * 2449320 * 2
def baseEnd_2449320 : Nat := 419226145556820752645263

theorem tailTrace_2449320 : CollatzResearch.WordTrace tailWord_2449320 prefixEnd_2449320 419226145556820752645263 := by
  unfold tailWord_2449320
  simp only [CollatzResearch.WordTrace]
  refine ⟨44667019743269712698852707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59556026324359616931803609 44667019743269712698852707)
  ·
    refine ⟨67000529614904569048279061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44667019743269712698852707 67000529614904569048279061)
    ·
      refine ⟨3140649825698651674138081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67000529614904569048279061 3140649825698651674138081)
      ·
        refine ⟨2355487369273988755603561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3140649825698651674138081 2355487369273988755603561)
        ·
          refine ⟨1766615526955491566702671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2355487369273988755603561 1766615526955491566702671)
          ·
            refine ⟨2649923290433237350054007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1766615526955491566702671 2649923290433237350054007)
            ·
              refine ⟨3974884935649856025081011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2649923290433237350054007 3974884935649856025081011)
              ·
                refine ⟨5962327403474784037621517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3974884935649856025081011 5962327403474784037621517)
                ·
                  refine ⟨2235872776303044014108069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5962327403474784037621517 2235872776303044014108069)
                  ·
                    refine ⟨419226145556820752645263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2235872776303044014108069 419226145556820752645263)
                    ·
                      rfl

theorem cell23_2449320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_2449320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449320 prefixEnd_2449320 := by exact prefixLift 2449320
  have htrace : WordTrace (prefixWord ++ tailWord_2449320) baseStart_2449320 baseEnd_2449320 := by
    simpa [prefixWord, tailWord_2449320, baseEnd_2449320] using wordTrace_append hprefix tailTrace_2449320
  have hstable : (prefixWord ++ tailWord_2449320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449320).length < 2 ^ (prefixWord ++ tailWord_2449320).sum := by decide
  have hdescent : baseEnd_2449320 < baseStart_2449320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449355 : List Nat := [1, 1, 1, 1, 3, 4, 1, 11]
def baseStart_2449355 : Nat := 118140960795 + 2449355 * 2 ^ 59
def prefixEnd_2449355 : Nat := 4983230072969 + 3 ^ 40 * 2449355 * 2
def baseEnd_2449355 : Nat := 46581348462717393370301

theorem tailTrace_2449355 : CollatzResearch.WordTrace tailWord_2449355 prefixEnd_2449355 46581348462717393370301 := by
  unfold tailWord_2449355
  simp only [CollatzResearch.WordTrace]
  refine ⟨89335316041412626375229519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59556877360941750916819679 89335316041412626375229519)
  ·
    refine ⟨134002974062118939562844279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89335316041412626375229519 134002974062118939562844279)
    ·
      refine ⟨201004461093178409344266419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134002974062118939562844279 201004461093178409344266419)
      ·
        refine ⟨301506691639767614016399629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201004461093178409344266419 301506691639767614016399629)
        ·
          refine ⟨113065009364912855256149861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301506691639767614016399629 113065009364912855256149861)
          ·
            refine ⟨21199689255921160360528099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113065009364912855256149861 21199689255921160360528099)
            ·
              refine ⟨31799533883881740540792149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21199689255921160360528099 31799533883881740540792149)
              ·
                refine ⟨46581348462717393370301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 31799533883881740540792149 46581348462717393370301)
                ·
                  rfl

theorem cell23_2449355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 11].length) (baseStart_2449355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449355 prefixEnd_2449355 := by exact prefixLift 2449355
  have htrace : WordTrace (prefixWord ++ tailWord_2449355) baseStart_2449355 baseEnd_2449355 := by
    simpa [prefixWord, tailWord_2449355, baseEnd_2449355] using wordTrace_append hprefix tailTrace_2449355
  have hstable : (prefixWord ++ tailWord_2449355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449355).length < 2 ^ (prefixWord ++ tailWord_2449355).sum := by decide
  have hdescent : baseEnd_2449355 < baseStart_2449355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449406 : List Nat := [4, 2, 2, 2, 1, 2, 3, 7]
def baseStart_2449406 : Nat := 118140960795 + 2449406 * 2 ^ 59
def prefixEnd_2449406 : Nat := 4983230072969 + 3 ^ 40 * 2449406 * 2
def baseEnd_2449406 : Nat := 46582318370620330424459

theorem tailTrace_2449406 : CollatzResearch.WordTrace tailWord_2449406 prefixEnd_2449406 46582318370620330424459 := by
  unfold tailWord_2449406
  simp only [CollatzResearch.WordTrace]
  refine ⟨11167147020528482760667009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59558117442818574723557381 11167147020528482760667009)
  ·
    refine ⟨8375360265396362070500257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11167147020528482760667009 8375360265396362070500257)
    ·
      refine ⟨6281520199047271552875193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8375360265396362070500257 6281520199047271552875193)
      ·
        refine ⟨4711140149285453664656395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6281520199047271552875193 4711140149285453664656395)
        ·
          refine ⟨7066710223928180496984593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4711140149285453664656395 7066710223928180496984593)
          ·
            refine ⟨5300032667946135372738445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7066710223928180496984593 5300032667946135372738445)
            ·
              refine ⟨1987512250479800764776917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5300032667946135372738445 1987512250479800764776917)
              ·
                refine ⟨46582318370620330424459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1987512250479800764776917 46582318370620330424459)
                ·
                  rfl

theorem cell23_2449406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 7].length) (baseStart_2449406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449406 prefixEnd_2449406 := by exact prefixLift 2449406
  have htrace : WordTrace (prefixWord ++ tailWord_2449406) baseStart_2449406 baseEnd_2449406 := by
    simpa [prefixWord, tailWord_2449406, baseEnd_2449406] using wordTrace_append hprefix tailTrace_2449406
  have hstable : (prefixWord ++ tailWord_2449406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449406).length < 2 ^ (prefixWord ++ tailWord_2449406).sum := by decide
  have hdescent : baseEnd_2449406 < baseStart_2449406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449414 : List Nat := [6, 2, 1, 2, 1, 2, 2, 1, 1, 5]
def baseStart_2449414 : Nat := 118140960795 + 2449414 * 2 ^ 59
def prefixEnd_2449414 : Nat := 4983230072969 + 3 ^ 40 * 2449414 * 2
def baseEnd_2449414 : Nat := 419242234617328296720119

theorem tailTrace_2449414 : CollatzResearch.WordTrace tailWord_2449414 prefixEnd_2449414 419242234617328296720119 := by
  unfold tailWord_2449414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2791795873381214982863353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59558311965465919634418197 2791795873381214982863353)
  ·
    refine ⟨2093846905035911237147515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2791795873381214982863353 2093846905035911237147515)
    ·
      refine ⟨3140770357553866855721273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2093846905035911237147515 3140770357553866855721273)
      ·
        refine ⟨2355577768165400141790955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3140770357553866855721273 2355577768165400141790955)
        ·
          refine ⟨3533366652248100212686433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2355577768165400141790955 3533366652248100212686433)
          ·
            refine ⟨2650024989186075159514825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3533366652248100212686433 2650024989186075159514825)
            ·
              refine ⟨1987518741889556369636119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2650024989186075159514825 1987518741889556369636119)
              ·
                refine ⟨2981278112834334554454179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1987518741889556369636119 2981278112834334554454179)
                ·
                  refine ⟨4471917169251501831681269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2981278112834334554454179 4471917169251501831681269)
                  ·
                    refine ⟨419242234617328296720119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4471917169251501831681269 419242234617328296720119)
                    ·
                      rfl

theorem cell23_2449414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_2449414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449414 prefixEnd_2449414 := by exact prefixLift 2449414
  have htrace : WordTrace (prefixWord ++ tailWord_2449414) baseStart_2449414 baseEnd_2449414 := by
    simpa [prefixWord, tailWord_2449414, baseEnd_2449414] using wordTrace_append hprefix tailTrace_2449414
  have hstable : (prefixWord ++ tailWord_2449414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449414).length < 2 ^ (prefixWord ++ tailWord_2449414).sum := by decide
  have hdescent : baseEnd_2449414 < baseStart_2449414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449432 : List Nat := [2, 1, 2, 3, 2, 1, 1, 1, 4, 6]
def baseStart_2449432 : Nat := 118140960795 + 2449432 * 2 ^ 59
def prefixEnd_2449432 : Nat := 4983230072969 + 3 ^ 40 * 2449432 * 2
def baseEnd_2449432 : Nat := 419245315501255273245091

theorem tailTrace_2449432 : CollatzResearch.WordTrace tailWord_2449432 prefixEnd_2449432 419245315501255273245091 := by
  unfold tailWord_2449432
  simp only [CollatzResearch.WordTrace]
  refine ⟨44669062231066834262891275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59558749641422445683855033 44669062231066834262891275)
  ·
    refine ⟨67003593346600251394336913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44669062231066834262891275 67003593346600251394336913)
    ·
      refine ⟨50252695009950188545752685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67003593346600251394336913 50252695009950188545752685)
      ·
        refine ⟨18844760628731320704657257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50252695009950188545752685 18844760628731320704657257)
        ·
          refine ⟨14133570471548490528492943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18844760628731320704657257 14133570471548490528492943)
          ·
            refine ⟨21200355707322735792739415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14133570471548490528492943 21200355707322735792739415)
            ·
              refine ⟨31800533560984103689109123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21200355707322735792739415 31800533560984103689109123)
              ·
                refine ⟨47700800341476155533663685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31800533560984103689109123 47700800341476155533663685)
                ·
                  refine ⟨8943900064026779162561941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47700800341476155533663685 8943900064026779162561941)
                  ·
                    refine ⟨419245315501255273245091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8943900064026779162561941 419245315501255273245091)
                    ·
                      rfl

theorem cell23_2449432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_2449432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449432 prefixEnd_2449432 := by exact prefixLift 2449432
  have htrace : WordTrace (prefixWord ++ tailWord_2449432) baseStart_2449432 baseEnd_2449432 := by
    simpa [prefixWord, tailWord_2449432, baseEnd_2449432] using wordTrace_append hprefix tailTrace_2449432
  have hstable : (prefixWord ++ tailWord_2449432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449432).length < 2 ^ (prefixWord ++ tailWord_2449432).sum := by decide
  have hdescent : baseEnd_2449432 < baseStart_2449432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449450 : List Nat := [3, 1, 4, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_2449450 : Nat := 118140960795 + 2449450 * 2 ^ 59
def prefixEnd_2449450 : Nat := 4983230072969 + 3 ^ 40 * 2449450 * 2
def baseEnd_2449450 : Nat := 1257745189155546749310191

theorem tailTrace_2449450 : CollatzResearch.WordTrace tailWord_2449450 prefixEnd_2449450 1257745189155546749310191 := by
  unfold tailWord_2449450
  simp only [CollatzResearch.WordTrace]
  refine ⟨22334695244017114399984451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59559187317378971733291869 22334695244017114399984451)
  ·
    refine ⟨33502042866025671599976677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22334695244017114399984451 33502042866025671599976677)
    ·
      refine ⟨6281633037379813424995627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33502042866025671599976677 6281633037379813424995627)
      ·
        refine ⟨9422449556069720137493441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6281633037379813424995627 9422449556069720137493441)
        ·
          refine ⟨7066837167052290103120081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9422449556069720137493441 7066837167052290103120081)
          ·
            refine ⟨5300127875289217577340061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7066837167052290103120081 5300127875289217577340061)
            ·
              refine ⟨1987547953233456591502523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5300127875289217577340061 1987547953233456591502523)
              ·
                refine ⟨2981321929850184887253785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1987547953233456591502523 2981321929850184887253785)
                ·
                  refine ⟨2235991447387638665440339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2981321929850184887253785 2235991447387638665440339)
                  ·
                    refine ⟨3353987171081457998160509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2235991447387638665440339 3353987171081457998160509)
                    ·
                      refine ⟨1257745189155546749310191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3353987171081457998160509 1257745189155546749310191)
                      ·
                        rfl

theorem cell23_2449450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_2449450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449450 prefixEnd_2449450 := by exact prefixLift 2449450
  have htrace : WordTrace (prefixWord ++ tailWord_2449450) baseStart_2449450 baseEnd_2449450 := by
    simpa [prefixWord, tailWord_2449450, baseEnd_2449450] using wordTrace_append hprefix tailTrace_2449450
  have hstable : (prefixWord ++ tailWord_2449450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449450).length < 2 ^ (prefixWord ++ tailWord_2449450).sum := by decide
  have hdescent : baseEnd_2449450 < baseStart_2449450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449452 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 4]
def baseStart_2449452 : Nat := 118140960795 + 2449452 * 2 ^ 59
def prefixEnd_2449452 : Nat := 4983230072969 + 3 ^ 40 * 2449452 * 2
def baseEnd_2449452 : Nat := 1257746216116855741485181

theorem tailTrace_2449452 : CollatzResearch.WordTrace tailWord_2449452 prefixEnd_2449452 1257746216116855741485181 := by
  unfold tailWord_2449452
  simp only [CollatzResearch.WordTrace]
  refine ⟨44669426961030605970755305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59559235948040807961007073 44669426961030605970755305)
  ·
    refine ⟨33502070220772954478066479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44669426961030605970755305 33502070220772954478066479)
    ·
      refine ⟨50253105331159431717099719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33502070220772954478066479 50253105331159431717099719)
      ·
        refine ⟨75379657996739147575649579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50253105331159431717099719 75379657996739147575649579)
        ·
          refine ⟨113069486995108721363474369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75379657996739147575649579 113069486995108721363474369)
          ·
            refine ⟨84802115246331541022605777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113069486995108721363474369 84802115246331541022605777)
            ·
              refine ⟨63601586434748655766954333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84802115246331541022605777 63601586434748655766954333)
              ·
                refine ⟨23850594913030745912607875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63601586434748655766954333 23850594913030745912607875)
                ·
                  refine ⟨35775892369546118868911813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23850594913030745912607875 35775892369546118868911813)
                  ·
                    refine ⟨6707979819289897287920965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35775892369546118868911813 6707979819289897287920965)
                    ·
                      refine ⟨1257746216116855741485181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6707979819289897287920965 1257746216116855741485181)
                      ·
                        rfl

theorem cell23_2449452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_2449452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449452 prefixEnd_2449452 := by exact prefixLift 2449452
  have htrace : WordTrace (prefixWord ++ tailWord_2449452) baseStart_2449452 baseEnd_2449452 := by
    simpa [prefixWord, tailWord_2449452, baseEnd_2449452] using wordTrace_append hprefix tailTrace_2449452
  have hstable : (prefixWord ++ tailWord_2449452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449452).length < 2 ^ (prefixWord ++ tailWord_2449452).sum := by decide
  have hdescent : baseEnd_2449452 < baseStart_2449452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449456 : List Nat := [2, 1, 1, 1, 2, 5, 3, 1, 1, 4, 2]
def baseStart_2449456 : Nat := 118140960795 + 2449456 * 2 ^ 59
def prefixEnd_2449456 : Nat := 4983230072969 + 3 ^ 40 * 2449456 * 2
def baseEnd_2449456 : Nat := 1257748270039473725835163

theorem tailTrace_2449456 : CollatzResearch.WordTrace tailWord_2449456 prefixEnd_2449456 1257748270039473725835163 := by
  unfold tailWord_2449456
  simp only [CollatzResearch.WordTrace]
  refine ⟨44669499907023360312328111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59559333209364480416437481 44669499907023360312328111)
  ·
    refine ⟨67004249860535040468492167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44669499907023360312328111 67004249860535040468492167)
    ·
      refine ⟨100506374790802560702738251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67004249860535040468492167 100506374790802560702738251)
      ·
        refine ⟨150759562186203841054107377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100506374790802560702738251 150759562186203841054107377)
        ·
          refine ⟨113069671639652880790580533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150759562186203841054107377 113069671639652880790580533)
          ·
            refine ⟨10600281716217457574116925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113069671639652880790580533 10600281716217457574116925)
            ·
              refine ⟨3975105643581546590293847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10600281716217457574116925 3975105643581546590293847)
              ·
                refine ⟨5962658465372319885440771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3975105643581546590293847 5962658465372319885440771)
                ·
                  refine ⟨8943987698058479828161157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5962658465372319885440771 8943987698058479828161157)
                  ·
                    refine ⟨1676997693385964967780217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8943987698058479828161157 1676997693385964967780217)
                    ·
                      refine ⟨1257748270039473725835163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1676997693385964967780217 1257748270039473725835163)
                      ·
                        rfl

theorem cell23_2449456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 1, 4, 2].length) (baseStart_2449456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449456 prefixEnd_2449456 := by exact prefixLift 2449456
  have htrace : WordTrace (prefixWord ++ tailWord_2449456) baseStart_2449456 baseEnd_2449456 := by
    simpa [prefixWord, tailWord_2449456, baseEnd_2449456] using wordTrace_append hprefix tailTrace_2449456
  have hstable : (prefixWord ++ tailWord_2449456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449456).length < 2 ^ (prefixWord ++ tailWord_2449456).sum := by decide
  have hdescent : baseEnd_2449456 < baseStart_2449456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449473 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 4, 2, 2]
def baseStart_2449473 : Nat := 118140960795 + 2449473 * 2 ^ 59
def prefixEnd_2449473 : Nat := 4983230072969 + 3 ^ 40 * 2449473 * 2
def baseEnd_2449473 : Nat := 1257756999210600159322585

theorem tailTrace_2449473 : CollatzResearch.WordTrace tailWord_2449473 prefixEnd_2449473 1257756999210600159322585 := by
  unfold tailWord_2449473
  simp only [CollatzResearch.WordTrace]
  refine ⟨89339619854985132528025073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59559746569990088352016715 89339619854985132528025073)
  ·
    refine ⟨67004714891238849396018805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89339619854985132528025073 67004714891238849396018805)
    ·
      refine ⟨6281692021053642130876763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67004714891238849396018805 6281692021053642130876763)
      ·
        refine ⟨9422538031580463196315145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6281692021053642130876763 9422538031580463196315145)
        ·
          refine ⟨7066903523685347397236359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9422538031580463196315145 7066903523685347397236359)
          ·
            refine ⟨10600355285528021095854539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7066903523685347397236359 10600355285528021095854539)
            ·
              refine ⟨15900532928292031643781809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10600355285528021095854539 15900532928292031643781809)
              ·
                refine ⟨11925399696219023732836357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15900532928292031643781809 11925399696219023732836357)
                ·
                  refine ⟨2236012443041066949906817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11925399696219023732836357 2236012443041066949906817)
                  ·
                    refine ⟨1677009332280800212430113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2236012443041066949906817 1677009332280800212430113)
                    ·
                      refine ⟨1257756999210600159322585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677009332280800212430113 1257756999210600159322585)
                      ·
                        rfl

theorem cell23_2449473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_2449473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449473 prefixEnd_2449473 := by exact prefixLift 2449473
  have htrace : WordTrace (prefixWord ++ tailWord_2449473) baseStart_2449473 baseEnd_2449473 := by
    simpa [prefixWord, tailWord_2449473, baseEnd_2449473] using wordTrace_append hprefix tailTrace_2449473
  have hstable : (prefixWord ++ tailWord_2449473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449473).length < 2 ^ (prefixWord ++ tailWord_2449473).sum := by decide
  have hdescent : baseEnd_2449473 < baseStart_2449473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449526 : List Nat := [5, 1, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_2449526 : Nat := 118140960795 + 2449526 * 2 ^ 59
def prefixEnd_2449526 : Nat := 4983230072969 + 3 ^ 40 * 2449526 * 2
def baseEnd_2449526 : Nat := 419261404561762817319947

theorem tailTrace_2449526 : CollatzResearch.WordTrace tailWord_2449526 prefixEnd_2449526 419261404561762817319947 := by
  unfold tailWord_2449526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5583847057737070161231527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59561035282528748386469621 5583847057737070161231527)
  ·
    refine ⟨8375770586605605241847291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5583847057737070161231527 8375770586605605241847291)
    ·
      refine ⟨12563655879908407862770937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8375770586605605241847291 12563655879908407862770937)
      ·
        refine ⟨9422741909931305897078203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12563655879908407862770937 9422741909931305897078203)
        ·
          refine ⟨14134112864896958845617305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9422741909931305897078203 14134112864896958845617305)
          ·
            refine ⟨10600584648672719134212979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14134112864896958845617305 10600584648672719134212979)
            ·
              refine ⟨15900876973009078701319469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10600584648672719134212979 15900876973009078701319469)
              ·
                refine ⟨5962828864878404512994801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15900876973009078701319469 5962828864878404512994801)
                ·
                  refine ⟨4472121648658803384746101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5962828864878404512994801 4472121648658803384746101)
                  ·
                    refine ⟨419261404561762817319947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4472121648658803384746101 419261404561762817319947)
                    ·
                      rfl

theorem cell23_2449526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_2449526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449526 prefixEnd_2449526 := by exact prefixLift 2449526
  have htrace : WordTrace (prefixWord ++ tailWord_2449526) baseStart_2449526 baseEnd_2449526 := by
    simpa [prefixWord, tailWord_2449526, baseEnd_2449526] using wordTrace_append hprefix tailTrace_2449526
  have hstable : (prefixWord ++ tailWord_2449526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449526).length < 2 ^ (prefixWord ++ tailWord_2449526).sum := by decide
  have hdescent : baseEnd_2449526 < baseStart_2449526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449546 : List Nat := [3, 1, 2, 3, 1, 2, 2, 2, 2, 1, 4]
def baseStart_2449546 : Nat := 118140960795 + 2449546 * 2 ^ 59
def prefixEnd_2449546 : Nat := 4983230072969 + 3 ^ 40 * 2449546 * 2
def baseEnd_2449546 : Nat := 1257794483298378373709749

theorem tailTrace_2449546 : CollatzResearch.WordTrace tailWord_2449546 prefixEnd_2449546 1257794483298378373709749 := by
  unfold tailWord_2449546
  simp only [CollatzResearch.WordTrace]
  refine ⟨22335570595930166498858123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59561521589147110663621661 22335570595930166498858123)
  ·
    refine ⟨33503355893895249748287185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22335570595930166498858123 33503355893895249748287185)
    ·
      refine ⟨25127516920421437311215389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33503355893895249748287185 25127516920421437311215389)
      ·
        refine ⟨9422818845158038991705771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25127516920421437311215389 9422818845158038991705771)
        ·
          refine ⟨14134228267737058487558657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9422818845158038991705771 14134228267737058487558657)
          ·
            refine ⟨10600671200802793865668993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14134228267737058487558657 10600671200802793865668993)
            ·
              refine ⟨7950503400602095399251745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10600671200802793865668993 7950503400602095399251745)
              ·
                refine ⟨5962877550451571549438809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7950503400602095399251745 5962877550451571549438809)
                ·
                  refine ⟨4472158162838678662079107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5962877550451571549438809 4472158162838678662079107)
                  ·
                    refine ⟨6708237244258017993118661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4472158162838678662079107 6708237244258017993118661)
                    ·
                      refine ⟨1257794483298378373709749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6708237244258017993118661 1257794483298378373709749)
                      ·
                        rfl

theorem cell23_2449546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_2449546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449546 prefixEnd_2449546 := by exact prefixLift 2449546
  have htrace : WordTrace (prefixWord ++ tailWord_2449546) baseStart_2449546 baseEnd_2449546 := by
    simpa [prefixWord, tailWord_2449546, baseEnd_2449546] using wordTrace_append hprefix tailTrace_2449546
  have hstable : (prefixWord ++ tailWord_2449546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449546).length < 2 ^ (prefixWord ++ tailWord_2449546).sum := by decide
  have hdescent : baseEnd_2449546 < baseStart_2449546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449636 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 1, 8, 2]
def baseStart_2449636 : Nat := 118140960795 + 2449636 * 2 ^ 59
def prefixEnd_2449636 : Nat := 4983230072969 + 3 ^ 40 * 2449636 * 2
def baseEnd_2449636 : Nat := 1257840696557283021584335

theorem tailTrace_2449636 : CollatzResearch.WordTrace tailWord_2449636 prefixEnd_2449636 1257840696557283021584335 := by
  unfold tailWord_2449636
  simp only [CollatzResearch.WordTrace]
  refine ⟨44672782476697305683104381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59563709968929740910805841 44672782476697305683104381)
  ·
    refine ⟨16752293428761489631164143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44672782476697305683104381 16752293428761489631164143)
    ·
      refine ⟨25128440143142234446746215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16752293428761489631164143 25128440143142234446746215)
      ·
        refine ⟨37692660214713351670119323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25128440143142234446746215 37692660214713351670119323)
        ·
          refine ⟨56538990322070027505178985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37692660214713351670119323 56538990322070027505178985)
          ·
            refine ⟨42404242741552520628884239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56538990322070027505178985 42404242741552520628884239)
            ·
              refine ⟨63606364112328780943326359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42404242741552520628884239 63606364112328780943326359)
              ·
                refine ⟨95409546168493171414989539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63606364112328780943326359 95409546168493171414989539)
                ·
                  refine ⟨143114319252739757122484309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95409546168493171414989539 143114319252739757122484309)
                  ·
                    refine ⟨1677120928743044028779113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 143114319252739757122484309 1677120928743044028779113)
                    ·
                      refine ⟨1257840696557283021584335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677120928743044028779113 1257840696557283021584335)
                      ·
                        rfl

theorem cell23_2449636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_2449636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449636 prefixEnd_2449636 := by exact prefixLift 2449636
  have htrace : WordTrace (prefixWord ++ tailWord_2449636) baseStart_2449636 baseEnd_2449636 := by
    simpa [prefixWord, tailWord_2449636, baseEnd_2449636] using wordTrace_append hprefix tailTrace_2449636
  have hstable : (prefixWord ++ tailWord_2449636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449636).length < 2 ^ (prefixWord ++ tailWord_2449636).sum := by decide
  have hdescent : baseEnd_2449636 < baseStart_2449636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449647 : List Nat := [1, 1, 2, 1, 6, 3, 1, 3, 1, 1, 3]
def baseStart_2449647 : Nat := 118140960795 + 2449647 * 2 ^ 59
def prefixEnd_2449647 : Nat := 4983230072969 + 3 ^ 40 * 2449647 * 2
def baseEnd_2449647 : Nat := 1257846344844482478546785

theorem tailTrace_2449647 : CollatzResearch.WordTrace tailWord_2449647 prefixEnd_2449647 1257846344844482478546785 := by
  unfold tailWord_2449647
  simp only [CollatzResearch.WordTrace]
  refine ⟨89345966156354760244859195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59563977437569840163239463 89345966156354760244859195)
  ·
    refine ⟨134018949234532140367288793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89345966156354760244859195 134018949234532140367288793)
    ·
      refine ⟨100514211925899105275466595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134018949234532140367288793 100514211925899105275466595)
      ·
        refine ⟨150771317888848657913199893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100514211925899105275466595 150771317888848657913199893)
        ·
          refine ⟨7067405526039780839681245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 150771317888848657913199893 7067405526039780839681245)
          ·
            refine ⟨2650277072264917814880467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7067405526039780839681245 2650277072264917814880467)
            ·
              refine ⟨3975415608397376722320701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2650277072264917814880467 3975415608397376722320701)
              ·
                refine ⟨1490780853149016270870263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3975415608397376722320701 1490780853149016270870263)
                ·
                  refine ⟨2236171279723524406305395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1490780853149016270870263 2236171279723524406305395)
                  ·
                    refine ⟨3354256919585286609458093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2236171279723524406305395 3354256919585286609458093)
                    ·
                      refine ⟨1257846344844482478546785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3354256919585286609458093 1257846344844482478546785)
                      ·
                        rfl

theorem cell23_2449647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 1, 1, 3].length) (baseStart_2449647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449647 prefixEnd_2449647 := by exact prefixLift 2449647
  have htrace : WordTrace (prefixWord ++ tailWord_2449647) baseStart_2449647 baseEnd_2449647 := by
    simpa [prefixWord, tailWord_2449647, baseEnd_2449647] using wordTrace_append hprefix tailTrace_2449647
  have hstable : (prefixWord ++ tailWord_2449647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449647).length < 2 ^ (prefixWord ++ tailWord_2449647).sum := by decide
  have hdescent : baseEnd_2449647 < baseStart_2449647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449719 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 3, 8]
def baseStart_2449719 : Nat := 118140960795 + 2449719 * 2 ^ 59
def prefixEnd_2449719 : Nat := 4983230072969 + 3 ^ 40 * 2449719 * 2
def baseEnd_2449719 : Nat := 419294438483868732282151

theorem tailTrace_2449719 : CollatzResearch.WordTrace tailWord_2449719 prefixEnd_2449719 419294438483868732282151 := by
  unfold tailWord_2449719
  simp only [CollatzResearch.WordTrace]
  refine ⟨89348592212093916541480211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59565728141395944360986807 89348592212093916541480211)
  ·
    refine ⟨134022888318140874812220317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89348592212093916541480211 134022888318140874812220317)
    ·
      refine ⟨50258583119302828054582619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134022888318140874812220317 50258583119302828054582619)
      ·
        refine ⟨75387874678954242081873929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50258583119302828054582619 75387874678954242081873929)
        ·
          refine ⟨56540906009215681561405447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75387874678954242081873929 56540906009215681561405447)
          ·
            refine ⟨84811359013823522342108171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56540906009215681561405447 84811359013823522342108171)
            ·
              refine ⟨127217038520735283513162257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84811359013823522342108171 127217038520735283513162257)
              ·
                refine ⟨95412778890551462634871693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127217038520735283513162257 95412778890551462634871693)
                ·
                  refine ⟨35779792083956798488076885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95412778890551462634871693 35779792083956798488076885)
                  ·
                    refine ⟨419294438483868732282151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35779792083956798488076885 419294438483868732282151)
                    ·
                      rfl

theorem cell23_2449719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_2449719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449719 prefixEnd_2449719 := by exact prefixLift 2449719
  have htrace : WordTrace (prefixWord ++ tailWord_2449719) baseStart_2449719 baseEnd_2449719 := by
    simpa [prefixWord, tailWord_2449719, baseEnd_2449719] using wordTrace_append hprefix tailTrace_2449719
  have hstable : (prefixWord ++ tailWord_2449719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449719).length < 2 ^ (prefixWord ++ tailWord_2449719).sum := by decide
  have hdescent : baseEnd_2449719 < baseStart_2449719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449721 : List Nat := [1, 2, 1, 6, 1, 3, 2, 2, 1, 2, 2]
def baseStart_2449721 : Nat := 118140960795 + 2449721 * 2 ^ 59
def prefixEnd_2449721 : Nat := 4983230072969 + 3 ^ 40 * 2449721 * 2
def baseEnd_2449721 : Nat := 1257884342412915189021445

theorem tailTrace_2449721 : CollatzResearch.WordTrace tailWord_2449721 prefixEnd_2449721 1257884342412915189021445 := by
  unfold tailWord_2449721
  simp only [CollatzResearch.WordTrace]
  refine ⟨89348665158086670883053017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59565776772057780588702011 89348665158086670883053017)
  ·
    refine ⟨67011498868565003162289763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89348665158086670883053017 67011498868565003162289763)
    ·
      refine ⟨100517248302847504743434645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67011498868565003162289763 100517248302847504743434645)
      ·
        refine ⟨4711746014195976784848499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100517248302847504743434645 4711746014195976784848499)
        ·
          refine ⟨7067619021293965177272749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4711746014195976784848499 7067619021293965177272749)
          ·
            refine ⟨2650357132985236941477281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7067619021293965177272749 2650357132985236941477281)
            ·
              refine ⟨1987767849738927706107961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2650357132985236941477281 1987767849738927706107961)
              ·
                refine ⟨1490825887304195779580971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1987767849738927706107961 1490825887304195779580971)
                ·
                  refine ⟨2236238830956293669371457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1490825887304195779580971 2236238830956293669371457)
                  ·
                    refine ⟨1677179123217220252028593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2236238830956293669371457 1677179123217220252028593)
                    ·
                      refine ⟨1257884342412915189021445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677179123217220252028593 1257884342412915189021445)
                      ·
                        rfl

theorem cell23_2449721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_2449721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449721 prefixEnd_2449721 := by exact prefixLift 2449721
  have htrace : WordTrace (prefixWord ++ tailWord_2449721) baseStart_2449721 baseEnd_2449721 := by
    simpa [prefixWord, tailWord_2449721, baseEnd_2449721] using wordTrace_append hprefix tailTrace_2449721
  have hstable : (prefixWord ++ tailWord_2449721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449721).length < 2 ^ (prefixWord ++ tailWord_2449721).sum := by decide
  have hdescent : baseEnd_2449721 < baseStart_2449721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449746 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_2449746 : Nat := 118140960795 + 2449746 * 2 ^ 59
def prefixEnd_2449746 : Nat := 4983230072969 + 3 ^ 40 * 2449746 * 2
def baseEnd_2449746 : Nat := 1257897179429277591208829

theorem tailTrace_2449746 : CollatzResearch.WordTrace tailWord_2449746 prefixEnd_2449746 1257897179429277591208829 := by
  unfold tailWord_2449746
  simp only [CollatzResearch.WordTrace]
  refine ⟨22337394245749025038178273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59566384655330733435142061 22337394245749025038178273)
  ·
    refine ⟨16753045684311768778633705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22337394245749025038178273 16753045684311768778633705)
    ·
      refine ⟨12564784263233826583975279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16753045684311768778633705 12564784263233826583975279)
      ·
        refine ⟨18847176394850739875962919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12564784263233826583975279 18847176394850739875962919)
        ·
          refine ⟨28270764592276109813944379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18847176394850739875962919 28270764592276109813944379)
          ·
            refine ⟨42406146888414164720916569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28270764592276109813944379 42406146888414164720916569)
            ·
              refine ⟨31804610166310623540687427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42406146888414164720916569 31804610166310623540687427)
              ·
                refine ⟨47706915249465935311031141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31804610166310623540687427 47706915249465935311031141)
                ·
                  refine ⟨8945046609274862870818339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47706915249465935311031141 8945046609274862870818339)
                  ·
                    refine ⟨13417569913912294306227509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8945046609274862870818339 13417569913912294306227509)
                    ·
                      refine ⟨1257897179429277591208829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13417569913912294306227509 1257897179429277591208829)
                      ·
                        rfl

theorem cell23_2449746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_2449746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449746 prefixEnd_2449746 := by exact prefixLift 2449746
  have htrace : WordTrace (prefixWord ++ tailWord_2449746) baseStart_2449746 baseEnd_2449746 := by
    simpa [prefixWord, tailWord_2449746, baseEnd_2449746] using wordTrace_append hprefix tailTrace_2449746
  have hstable : (prefixWord ++ tailWord_2449746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449746).length < 2 ^ (prefixWord ++ tailWord_2449746).sum := by decide
  have hdescent : baseEnd_2449746 < baseStart_2449746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449796 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 3, 7]
def baseStart_2449796 : Nat := 118140960795 + 2449796 * 2 ^ 59
def prefixEnd_2449796 : Nat := 4983230072969 + 3 ^ 40 * 2449796 * 2
def baseEnd_2449796 : Nat := 419307617820667465194533

theorem tailTrace_2449796 : CollatzResearch.WordTrace tailWord_2449796 prefixEnd_2449796 419307617820667465194533 := by
  unfold tailWord_2449796
  simp only [CollatzResearch.WordTrace]
  refine ⟨44675700316407479346016621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59567600421876639128022161 44675700316407479346016621)
  ·
    refine ⟨16753387618652804754756233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44675700316407479346016621 16753387618652804754756233)
    ·
      refine ⟨12565040713989603566067175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16753387618652804754756233 12565040713989603566067175)
      ·
        refine ⟨18847561070984405349100763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12565040713989603566067175 18847561070984405349100763)
        ·
          refine ⟨28271341606476608023651145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18847561070984405349100763 28271341606476608023651145)
          ·
            refine ⟨21203506204857456017738359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28271341606476608023651145 21203506204857456017738359)
            ·
              refine ⟨31805259307286184026607539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21203506204857456017738359 31805259307286184026607539)
              ·
                refine ⟨47707888960929276039911309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31805259307286184026607539 47707888960929276039911309)
                ·
                  refine ⟨17890458360348478514966741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47707888960929276039911309 17890458360348478514966741)
                  ·
                    refine ⟨419307617820667465194533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17890458360348478514966741 419307617820667465194533)
                    ·
                      rfl

theorem cell23_2449796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_2449796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449796 prefixEnd_2449796 := by exact prefixLift 2449796
  have htrace : WordTrace (prefixWord ++ tailWord_2449796) baseStart_2449796 baseEnd_2449796 := by
    simpa [prefixWord, tailWord_2449796, baseEnd_2449796] using wordTrace_append hprefix tailTrace_2449796
  have hstable : (prefixWord ++ tailWord_2449796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449796).length < 2 ^ (prefixWord ++ tailWord_2449796).sum := by decide
  have hdescent : baseEnd_2449796 < baseStart_2449796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449814 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2449814 : Nat := 118140960795 + 2449814 * 2 ^ 59
def prefixEnd_2449814 : Nat := 4983230072969 + 3 ^ 40 * 2449814 * 2
def baseEnd_2449814 : Nat := 1257932096113783325158517

theorem tailTrace_2449814 : CollatzResearch.WordTrace tailWord_2449814 prefixEnd_2449814 1257932096113783325158517 := by
  unfold tailWord_2449814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5584503571671859235386781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59568038097833165177458997 5584503571671859235386781)
  ·
    refine ⟨2094188839376947213270043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5584503571671859235386781 2094188839376947213270043)
    ·
      refine ⟨3141283259065420819905065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2094188839376947213270043 3141283259065420819905065)
      ·
        refine ⟨2355962444299065614928799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3141283259065420819905065 2355962444299065614928799)
        ·
          refine ⟨3533943666448598422393199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2355962444299065614928799 3533943666448598422393199)
          ·
            refine ⟨5300915499672897633589799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3533943666448598422393199 5300915499672897633589799)
            ·
              refine ⟨7951373249509346450384699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5300915499672897633589799 7951373249509346450384699)
              ·
                refine ⟨11927059874264019675577049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7951373249509346450384699 11927059874264019675577049)
                ·
                  refine ⟨8945294905698014756682787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11927059874264019675577049 8945294905698014756682787)
                  ·
                    refine ⟨13417942358547022135024181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8945294905698014756682787 13417942358547022135024181)
                    ·
                      refine ⟨1257932096113783325158517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13417942358547022135024181 1257932096113783325158517)
                      ·
                        rfl

theorem cell23_2449814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2449814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449814 prefixEnd_2449814 := by exact prefixLift 2449814
  have htrace : WordTrace (prefixWord ++ tailWord_2449814) baseStart_2449814 baseEnd_2449814 := by
    simpa [prefixWord, tailWord_2449814, baseEnd_2449814] using wordTrace_append hprefix tailTrace_2449814
  have hstable : (prefixWord ++ tailWord_2449814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449814).length < 2 ^ (prefixWord ++ tailWord_2449814).sum := by decide
  have hdescent : baseEnd_2449814 < baseStart_2449814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449833 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 4, 4, 2]
def baseStart_2449833 : Nat := 118140960795 + 2449833 * 2 ^ 59
def prefixEnd_2449833 : Nat := 4983230072969 + 3 ^ 40 * 2449833 * 2
def baseEnd_2449833 : Nat := 1257941852246218750820929

theorem tailTrace_2449833 : CollatzResearch.WordTrace tailWord_2449833 prefixEnd_2449833 1257941852246218750820929 := by
  unfold tailWord_2449833
  simp only [CollatzResearch.WordTrace]
  refine ⟨89352750133680914011130153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59568500089120609340753435 89352750133680914011130153)
  ·
    refine ⟨67014562600260685508347615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89352750133680914011130153 67014562600260685508347615)
    ·
      refine ⟨100521843900391028262521423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67014562600260685508347615 100521843900391028262521423)
      ·
        refine ⟨150782765850586542393782135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100521843900391028262521423 150782765850586542393782135)
        ·
          refine ⟨226174148775879813590673203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150782765850586542393782135 226174148775879813590673203)
          ·
            refine ⟨339261223163819720386009805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226174148775879813590673203 339261223163819720386009805)
            ·
              refine ⟨127222958686432395144753677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 339261223163819720386009805 127222958686432395144753677)
              ·
                refine ⟨47708609507412148179282629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127222958686432395144753677 47708609507412148179282629)
                ·
                  refine ⟨8945364282639777783615493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47708609507412148179282629 8945364282639777783615493)
                  ·
                    refine ⟨1677255802994958334427905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8945364282639777783615493 1677255802994958334427905)
                    ·
                      refine ⟨1257941852246218750820929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677255802994958334427905 1257941852246218750820929)
                      ·
                        rfl

theorem cell23_2449833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 4, 2].length) (baseStart_2449833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449833 prefixEnd_2449833 := by exact prefixLift 2449833
  have htrace : WordTrace (prefixWord ++ tailWord_2449833) baseStart_2449833 baseEnd_2449833 := by
    simpa [prefixWord, tailWord_2449833, baseEnd_2449833] using wordTrace_append hprefix tailTrace_2449833
  have hstable : (prefixWord ++ tailWord_2449833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449833).length < 2 ^ (prefixWord ++ tailWord_2449833).sum := by decide
  have hdescent : baseEnd_2449833 < baseStart_2449833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449834 : List Nat := [3, 1, 6, 1, 1, 2, 1, 1, 7]
def baseStart_2449834 : Nat := 118140960795 + 2449834 * 2 ^ 59
def prefixEnd_2449834 : Nat := 4983230072969 + 3 ^ 40 * 2449834 * 2
def baseEnd_2449834 : Nat := 139771373969652582989825

theorem tailTrace_2449834 : CollatzResearch.WordTrace tailWord_2449834 prefixEnd_2449834 139771373969652582989825 := by
  unfold tailWord_2449834
  simp only [CollatzResearch.WordTrace]
  refine ⟨22338196651669322795479139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59568524404451527454611037 22338196651669322795479139)
  ·
    refine ⟨33507294977503984193218709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22338196651669322795479139 33507294977503984193218709)
    ·
      refine ⟨1570654452070499259057127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33507294977503984193218709 1570654452070499259057127)
      ·
        refine ⟨2355981678105748888585691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1570654452070499259057127 2355981678105748888585691)
        ·
          refine ⟨3533972517158623332878537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2355981678105748888585691 3533972517158623332878537)
          ·
            refine ⟨2650479387868967499658903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3533972517158623332878537 2650479387868967499658903)
            ·
              refine ⟨3975719081803451249488355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2650479387868967499658903 3975719081803451249488355)
              ·
                refine ⟨5963578622705176874232533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3975719081803451249488355 5963578622705176874232533)
                ·
                  refine ⟨139771373969652582989825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5963578622705176874232533 139771373969652582989825)
                  ·
                    rfl

theorem cell23_2449834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 7].length) (baseStart_2449834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449834 prefixEnd_2449834 := by exact prefixLift 2449834
  have htrace : WordTrace (prefixWord ++ tailWord_2449834) baseStart_2449834 baseEnd_2449834 := by
    simpa [prefixWord, tailWord_2449834, baseEnd_2449834] using wordTrace_append hprefix tailTrace_2449834
  have hstable : (prefixWord ++ tailWord_2449834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449834).length < 2 ^ (prefixWord ++ tailWord_2449834).sum := by decide
  have hdescent : baseEnd_2449834 < baseStart_2449834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449900 : List Nat := [2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 3]
def baseStart_2449900 : Nat := 118140960795 + 2449900 * 2 ^ 59
def prefixEnd_2449900 : Nat := 4983230072969 + 3 ^ 40 * 2449900 * 2
def baseEnd_2449900 : Nat := 1257976255450069988683121

theorem tailTrace_2449900 : CollatzResearch.WordTrace tailWord_2449900 prefixEnd_2449900 1257976255450069988683121 := by
  unfold tailWord_2449900
  simp only [CollatzResearch.WordTrace]
  refine ⟨44677596912219092226909577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59570129216292122969212769 44677596912219092226909577)
  ·
    refine ⟨33508197684164319170182183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44677596912219092226909577 33508197684164319170182183)
    ·
      refine ⟨50262296526246478755273275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33508197684164319170182183 50262296526246478755273275)
      ·
        refine ⟨75393444789369718132909913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50262296526246478755273275 75393444789369718132909913)
        ·
          refine ⟨56545083592027288599682435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75393444789369718132909913 56545083592027288599682435)
          ·
            refine ⟨84817625388040932899523653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56545083592027288599682435 84817625388040932899523653)
            ·
              refine ⟨15903304760257674918660685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84817625388040932899523653 15903304760257674918660685)
              ·
                refine ⟨5963739285096628094497757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15903304760257674918660685 5963739285096628094497757)
                ·
                  refine ⟨2236402231911235535436659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5963739285096628094497757 2236402231911235535436659)
                  ·
                    refine ⟨3354603347866853303154989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2236402231911235535436659 3354603347866853303154989)
                    ·
                      refine ⟨1257976255450069988683121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3354603347866853303154989 1257976255450069988683121)
                      ·
                        rfl

theorem cell23_2449900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 3].length) (baseStart_2449900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449900 prefixEnd_2449900 := by exact prefixLift 2449900
  have htrace : WordTrace (prefixWord ++ tailWord_2449900) baseStart_2449900 baseEnd_2449900 := by
    simpa [prefixWord, tailWord_2449900, baseEnd_2449900] using wordTrace_append hprefix tailTrace_2449900
  have hstable : (prefixWord ++ tailWord_2449900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449900).length < 2 ^ (prefixWord ++ tailWord_2449900).sum := by decide
  have hdescent : baseEnd_2449900 < baseStart_2449900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449923 : List Nat := [1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 4]
def baseStart_2449923 : Nat := 118140960795 + 2449923 * 2 ^ 59
def prefixEnd_2449923 : Nat := 4983230072969 + 3 ^ 40 * 2449923 * 2
def baseEnd_2449923 : Nat := 1257988065505123398695515

theorem tailTrace_2449923 : CollatzResearch.WordTrace tailWord_2449923 prefixEnd_2449923 1257988065505123398695515 := by
  unfold tailWord_2449923
  simp only [CollatzResearch.WordTrace]
  refine ⟨89356032703354859381906423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59570688468903239587937615 89356032703354859381906423)
  ·
    refine ⟨134034049055032289072859635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89356032703354859381906423 134034049055032289072859635)
    ·
      refine ⟨201051073582548433609289453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134034049055032289072859635 201051073582548433609289453)
      ·
        refine ⟨75394152593455662603483545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201051073582548433609289453 75394152593455662603483545)
        ·
          refine ⟨56545614445091746952612659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75394152593455662603483545 56545614445091746952612659)
          ·
            refine ⟨84818421667637620428918989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56545614445091746952612659 84818421667637620428918989)
            ·
              refine ⟨31806908125364107660844621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84818421667637620428918989 31806908125364107660844621)
              ·
                refine ⟨11927590547011540372816733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31806908125364107660844621 11927590547011540372816733)
                ·
                  refine ⟨4472846455129327639806275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11927590547011540372816733 4472846455129327639806275)
                  ·
                    refine ⟨6709269682693991459709413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4472846455129327639806275 6709269682693991459709413)
                    ·
                      refine ⟨1257988065505123398695515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6709269682693991459709413 1257988065505123398695515)
                      ·
                        rfl

theorem cell23_2449923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_2449923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449923 prefixEnd_2449923 := by exact prefixLift 2449923
  have htrace : WordTrace (prefixWord ++ tailWord_2449923) baseStart_2449923 baseEnd_2449923 := by
    simpa [prefixWord, tailWord_2449923, baseEnd_2449923] using wordTrace_append hprefix tailTrace_2449923
  have hstable : (prefixWord ++ tailWord_2449923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449923).length < 2 ^ (prefixWord ++ tailWord_2449923).sum := by decide
  have hdescent : baseEnd_2449923 < baseStart_2449923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449927 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 1, 5, 2]
def baseStart_2449927 : Nat := 118140960795 + 2449927 * 2 ^ 59
def prefixEnd_2449927 : Nat := 4983230072969 + 3 ^ 40 * 2449927 * 2
def baseEnd_2449927 : Nat := 1257990119427741383045497

theorem tailTrace_2449927 : CollatzResearch.WordTrace tailWord_2449927 prefixEnd_2449927 1257990119427741383045497 := by
  unfold tailWord_2449927
  simp only [CollatzResearch.WordTrace]
  refine ⟨89356178595340368065052035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59570785730226912043368023 89356178595340368065052035)
  ·
    refine ⟨134034267893010552097578053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89356178595340368065052035 134034267893010552097578053)
    ·
      refine ⟨25131425229939478518295885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134034267893010552097578053 25131425229939478518295885)
      ·
        refine ⟨9424284461227304444360957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25131425229939478518295885 9424284461227304444360957)
        ·
          refine ⟨3534106672960239166635359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9424284461227304444360957 3534106672960239166635359)
          ·
            refine ⟨5301160009440358749953039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3534106672960239166635359 5301160009440358749953039)
            ·
              refine ⟨7951740014160538124929559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5301160009440358749953039 7951740014160538124929559)
              ·
                refine ⟨11927610021240807187394339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7951740014160538124929559 11927610021240807187394339)
                ·
                  refine ⟨17891415031861210781091509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11927610021240807187394339 17891415031861210781091509)
                  ·
                    refine ⟨1677320159236988510727329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17891415031861210781091509 1677320159236988510727329)
                    ·
                      refine ⟨1257990119427741383045497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677320159236988510727329 1257990119427741383045497)
                      ·
                        rfl

theorem cell23_2449927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_2449927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449927 prefixEnd_2449927 := by exact prefixLift 2449927
  have htrace : WordTrace (prefixWord ++ tailWord_2449927) baseStart_2449927 baseEnd_2449927 := by
    simpa [prefixWord, tailWord_2449927, baseEnd_2449927] using wordTrace_append hprefix tailTrace_2449927
  have hstable : (prefixWord ++ tailWord_2449927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449927).length < 2 ^ (prefixWord ++ tailWord_2449927).sum := by decide
  have hdescent : baseEnd_2449927 < baseStart_2449927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449934 : List Nat := [4, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3]
def baseStart_2449934 : Nat := 118140960795 + 2449934 * 2 ^ 59
def prefixEnd_2449934 : Nat := 4983230072969 + 3 ^ 40 * 2449934 * 2
def baseEnd_2449934 : Nat := 1257993713792322855657965

theorem tailTrace_2449934 : CollatzResearch.WordTrace tailWord_2449934 prefixEnd_2449934 1257993713792322855657965 := by
  unfold tailWord_2449934
  simp only [CollatzResearch.WordTrace]
  refine ⟨11169554238289376032569607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59570955937543338840371237 11169554238289376032569607)
  ·
    refine ⟨16754331357434064048854411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11169554238289376032569607 16754331357434064048854411)
    ·
      refine ⟨25131497036151096073281617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16754331357434064048854411 25131497036151096073281617)
      ·
        refine ⟨18848622777113322054961213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25131497036151096073281617 18848622777113322054961213)
        ·
          refine ⟨7068233541417495770610455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18848622777113322054961213 7068233541417495770610455)
          ·
            refine ⟨10602350312126243655915683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7068233541417495770610455 10602350312126243655915683)
            ·
              refine ⟨15903525468189365483873525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10602350312126243655915683 15903525468189365483873525)
              ·
                refine ⟨1490955512642753014113143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15903525468189365483873525 1490955512642753014113143)
                ·
                  refine ⟨2236433268964129521169715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1490955512642753014113143 2236433268964129521169715)
                  ·
                    refine ⟨3354649903446194281754573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2236433268964129521169715 3354649903446194281754573)
                    ·
                      refine ⟨1257993713792322855657965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3354649903446194281754573 1257993713792322855657965)
                      ·
                        rfl

theorem cell23_2449934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_2449934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449934 prefixEnd_2449934 := by exact prefixLift 2449934
  have htrace : WordTrace (prefixWord ++ tailWord_2449934) baseStart_2449934 baseEnd_2449934 := by
    simpa [prefixWord, tailWord_2449934, baseEnd_2449934] using wordTrace_append hprefix tailTrace_2449934
  have hstable : (prefixWord ++ tailWord_2449934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449934).length < 2 ^ (prefixWord ++ tailWord_2449934).sum := by decide
  have hdescent : baseEnd_2449934 < baseStart_2449934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449953 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 1, 1, 6]
def baseStart_2449953 : Nat := 118140960795 + 2449953 * 2 ^ 59
def prefixEnd_2449953 : Nat := 4983230072969 + 3 ^ 40 * 2449953 * 2
def baseEnd_2449953 : Nat := 1258003469924758281320377

theorem tailTrace_2449953 : CollatzResearch.WordTrace tailWord_2449953 prefixEnd_2449953 1258003469924758281320377 := by
  unfold tailWord_2449953
  simp only [CollatzResearch.WordTrace]
  refine ⟨89357126893246174505498513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59571417928830783003665675 89357126893246174505498513)
  ·
    refine ⟨67017845169934630879123885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89357126893246174505498513 67017845169934630879123885)
    ·
      refine ⟨25131691938725486579671457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67017845169934630879123885 25131691938725486579671457)
      ·
        refine ⟨18848768954044114934753593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25131691938725486579671457 18848768954044114934753593)
        ·
          refine ⟨14136576715533086201065195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18848768954044114934753593 14136576715533086201065195)
          ·
            refine ⟨21204865073299629301597793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14136576715533086201065195 21204865073299629301597793)
            ·
              refine ⟨15903648804974721976198345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21204865073299629301597793 15903648804974721976198345)
              ·
                refine ⟨11927736603731041482148759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15903648804974721976198345 11927736603731041482148759)
                ·
                  refine ⟨17891604905596562223223139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11927736603731041482148759 17891604905596562223223139)
                  ·
                    refine ⟨26837407358394843334834709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17891604905596562223223139 26837407358394843334834709)
                    ·
                      refine ⟨1258003469924758281320377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26837407358394843334834709 1258003469924758281320377)
                      ·
                        rfl

theorem cell23_2449953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_2449953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449953 prefixEnd_2449953 := by exact prefixLift 2449953
  have htrace : WordTrace (prefixWord ++ tailWord_2449953) baseStart_2449953 baseEnd_2449953 := by
    simpa [prefixWord, tailWord_2449953, baseEnd_2449953] using wordTrace_append hprefix tailTrace_2449953
  have hstable : (prefixWord ++ tailWord_2449953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449953).length < 2 ^ (prefixWord ++ tailWord_2449953).sum := by decide
  have hdescent : baseEnd_2449953 < baseStart_2449953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449957 : List Nat := [1, 3, 1, 2, 2, 1, 3, 3, 3, 2, 2]
def baseStart_2449957 : Nat := 118140960795 + 2449957 * 2 ^ 59
def prefixEnd_2449957 : Nat := 4983230072969 + 3 ^ 40 * 2449957 * 2
def baseEnd_2449957 : Nat := 1258005523847376265670359

theorem tailTrace_2449957 : CollatzResearch.WordTrace tailWord_2449957 prefixEnd_2449957 1258005523847376265670359 := by
  unfold tailWord_2449957
  simp only [CollatzResearch.WordTrace]
  refine ⟨89357272785231683188644125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59571515190154455459096083 89357272785231683188644125)
  ·
    refine ⟨33508977294461881195741547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89357272785231683188644125 33508977294461881195741547)
    ·
      refine ⟨50263465941692821793612321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33508977294461881195741547 50263465941692821793612321)
      ·
        refine ⟨37697599456269616345209241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50263465941692821793612321 37697599456269616345209241)
        ·
          refine ⟨28273199592202212258906931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37697599456269616345209241 28273199592202212258906931)
          ·
            refine ⟨42409799388303318388360397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28273199592202212258906931 42409799388303318388360397)
            ·
              refine ⟨15903674770613744395635149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42409799388303318388360397 15903674770613744395635149)
              ·
                refine ⟨5963878038980154148363181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15903674770613744395635149 5963878038980154148363181)
                ·
                  refine ⟨2236454264617557805636193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5963878038980154148363181 2236454264617557805636193)
                  ·
                    refine ⟨1677340698463168354227145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2236454264617557805636193 1677340698463168354227145)
                    ·
                      refine ⟨1258005523847376265670359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677340698463168354227145 1258005523847376265670359)
                      ·
                        rfl

theorem cell23_2449957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 3, 2, 2].length) (baseStart_2449957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449957 prefixEnd_2449957 := by exact prefixLift 2449957
  have htrace : WordTrace (prefixWord ++ tailWord_2449957) baseStart_2449957 baseEnd_2449957 := by
    simpa [prefixWord, tailWord_2449957, baseEnd_2449957] using wordTrace_append hprefix tailTrace_2449957
  have hstable : (prefixWord ++ tailWord_2449957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449957).length < 2 ^ (prefixWord ++ tailWord_2449957).sum := by decide
  have hdescent : baseEnd_2449957 < baseStart_2449957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449960 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2449960 : Nat := 118140960795 + 2449960 * 2 ^ 59
def prefixEnd_2449960 : Nat := 4983230072969 + 3 ^ 40 * 2449960 * 2
def baseEnd_2449960 : Nat := 1258007064289339753932845

theorem tailTrace_2449960 : CollatzResearch.WordTrace tailWord_2449960 prefixEnd_2449960 1258007064289339753932845 := by
  unfold tailWord_2449960
  simp only [CollatzResearch.WordTrace]
  refine ⟨44678691102110407350501667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59571588136147209800668889 44678691102110407350501667)
  ·
    refine ⟨67018036653165611025752501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44678691102110407350501667 67018036653165611025752501)
    ·
      refine ⟨6282940936234276033664297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67018036653165611025752501 6282940936234276033664297)
      ·
        refine ⟨4712205702175707025248223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6282940936234276033664297 4712205702175707025248223)
        ·
          refine ⟨7068308553263560537872335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4712205702175707025248223 7068308553263560537872335)
          ·
            refine ⟨10602462829895340806808503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7068308553263560537872335 10602462829895340806808503)
            ·
              refine ⟨15903694244843011210212755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10602462829895340806808503 15903694244843011210212755)
              ·
                refine ⟨23855541367264516815319133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15903694244843011210212755 23855541367264516815319133)
                ·
                  refine ⟨8945828012724193805744675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23855541367264516815319133 8945828012724193805744675)
                  ·
                    refine ⟨13418742019086290708617013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8945828012724193805744675 13418742019086290708617013)
                    ·
                      refine ⟨1258007064289339753932845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13418742019086290708617013 1258007064289339753932845)
                      ·
                        rfl

theorem cell23_2449960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2449960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449960 prefixEnd_2449960 := by exact prefixLift 2449960
  have htrace : WordTrace (prefixWord ++ tailWord_2449960) baseStart_2449960 baseEnd_2449960 := by
    simpa [prefixWord, tailWord_2449960, baseEnd_2449960] using wordTrace_append hprefix tailTrace_2449960
  have hstable : (prefixWord ++ tailWord_2449960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449960).length < 2 ^ (prefixWord ++ tailWord_2449960).sum := by decide
  have hdescent : baseEnd_2449960 < baseStart_2449960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449970 : List Nat := [3, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4]
def baseStart_2449970 : Nat := 118140960795 + 2449970 * 2 ^ 59
def prefixEnd_2449970 : Nat := 4983230072969 + 3 ^ 40 * 2449970 * 2
def baseEnd_2449970 : Nat := 1258012199095884714807799

theorem tailTrace_2449970 : CollatzResearch.WordTrace tailWord_2449970 prefixEnd_2449970 1258012199095884714807799 := by
  unfold tailWord_2449970
  simp only [CollatzResearch.WordTrace]
  refine ⟨22339436733546146602216841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59571831289456390939244909 22339436733546146602216841)
  ·
    refine ⟨16754577550159609951662631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22339436733546146602216841 16754577550159609951662631)
    ·
      refine ⟨25131866325239414927493947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16754577550159609951662631 25131866325239414927493947)
      ·
        refine ⟨37697799487859122391240921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25131866325239414927493947 37697799487859122391240921)
        ·
          refine ⟨28273349615894341793430691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37697799487859122391240921 28273349615894341793430691)
          ·
            refine ⟨42410024423841512690146037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28273349615894341793430691 42410024423841512690146037)
            ·
              refine ⟨3975939789735141814701191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42410024423841512690146037 3975939789735141814701191)
              ·
                refine ⟨5963909684602712722051787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3975939789735141814701191 5963909684602712722051787)
                ·
                  refine ⟨8945864526904069083077681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5963909684602712722051787 8945864526904069083077681)
                  ·
                    refine ⟨6709398395178051812308261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8945864526904069083077681 6709398395178051812308261)
                    ·
                      refine ⟨1258012199095884714807799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6709398395178051812308261 1258012199095884714807799)
                      ·
                        rfl

theorem cell23_2449970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_2449970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449970 prefixEnd_2449970 := by exact prefixLift 2449970
  have htrace : WordTrace (prefixWord ++ tailWord_2449970) baseStart_2449970 baseEnd_2449970 := by
    simpa [prefixWord, tailWord_2449970, baseEnd_2449970] using wordTrace_append hprefix tailTrace_2449970
  have hstable : (prefixWord ++ tailWord_2449970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449970).length < 2 ^ (prefixWord ++ tailWord_2449970).sum := by decide
  have hdescent : baseEnd_2449970 < baseStart_2449970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449974 : List Nat := [5, 1, 2, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_2449974 : Nat := 118140960795 + 2449974 * 2 ^ 59
def prefixEnd_2449974 : Nat := 4983230072969 + 3 ^ 40 * 2449974 * 2
def baseEnd_2449974 : Nat := 1258014253018502699157781

theorem tailTrace_2449974 : CollatzResearch.WordTrace tailWord_2449974 prefixEnd_2449974 1258014253018502699157781 := by
  unfold tailWord_2449974
  simp only [CollatzResearch.WordTrace]
  refine ⟨5584868301635630943250811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59571928550780063394675317 5584868301635630943250811)
  ·
    refine ⟨8377302452453446414876217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5584868301635630943250811 8377302452453446414876217)
    ·
      refine ⟨6282976839340084811157163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8377302452453446414876217 6282976839340084811157163)
      ·
        refine ⟨9424465259010127216735745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6282976839340084811157163 9424465259010127216735745)
        ·
          refine ⟨7068348944257595412551809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9424465259010127216735745 7068348944257595412551809)
          ·
            refine ⟨5301261708193196559413857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7068348944257595412551809 5301261708193196559413857)
            ·
              refine ⟨3975946281144897419560393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5301261708193196559413857 3975946281144897419560393)
              ·
                refine ⟨2981959710858673064670295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3975946281144897419560393 2981959710858673064670295)
                ·
                  refine ⟨4472939566288009597005443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2981959710858673064670295 4472939566288009597005443)
                  ·
                    refine ⟨6709409349432014395508165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4472939566288009597005443 6709409349432014395508165)
                    ·
                      refine ⟨1258014253018502699157781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6709409349432014395508165 1258014253018502699157781)
                      ·
                        rfl

theorem cell23_2449974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_2449974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449974 prefixEnd_2449974 := by exact prefixLift 2449974
  have htrace : WordTrace (prefixWord ++ tailWord_2449974) baseStart_2449974 baseEnd_2449974 := by
    simpa [prefixWord, tailWord_2449974, baseEnd_2449974] using wordTrace_append hprefix tailTrace_2449974
  have hstable : (prefixWord ++ tailWord_2449974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449974).length < 2 ^ (prefixWord ++ tailWord_2449974).sum := by decide
  have hdescent : baseEnd_2449974 < baseStart_2449974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449977 : List Nat := [1, 2, 1, 5, 1, 1, 4, 2, 1, 2, 3]
def baseStart_2449977 : Nat := 118140960795 + 2449977 * 2 ^ 59
def prefixEnd_2449977 : Nat := 4983230072969 + 3 ^ 40 * 2449977 * 2
def baseEnd_2449977 : Nat := 1258015793460466187420267

theorem tailTrace_2449977 : CollatzResearch.WordTrace tailWord_2449977 prefixEnd_2449977 1258015793460466187420267 := by
  unfold tailWord_2449977
  simp only [CollatzResearch.WordTrace]
  refine ⟨89358002245159226604372185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59572001496772817736248123 89358002245159226604372185)
  ·
    refine ⟨67018501683869419953279139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89358002245159226604372185 67018501683869419953279139)
    ·
      refine ⟨100527752525804129929918709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67018501683869419953279139 100527752525804129929918709)
      ·
        refine ⟨9424476799294137180929879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100527752525804129929918709 9424476799294137180929879)
        ·
          refine ⟨14136715198941205771394819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9424476799294137180929879 14136715198941205771394819)
          ·
            refine ⟨21205072798411808657092229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14136715198941205771394819 21205072798411808657092229)
            ·
              refine ⟨3975951149702214123204793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21205072798411808657092229 3975951149702214123204793)
              ·
                refine ⟨2981963362276660592403595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3975951149702214123204793 2981963362276660592403595)
                ·
                  refine ⟨4472945043414990888605393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2981963362276660592403595 4472945043414990888605393)
                  ·
                    refine ⟨3354708782561243166454045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4472945043414990888605393 3354708782561243166454045)
                    ·
                      refine ⟨1258015793460466187420267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3354708782561243166454045 1258015793460466187420267)
                      ·
                        rfl

theorem cell23_2449977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_2449977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449977 prefixEnd_2449977 := by exact prefixLift 2449977
  have htrace : WordTrace (prefixWord ++ tailWord_2449977) baseStart_2449977 baseEnd_2449977 := by
    simpa [prefixWord, tailWord_2449977, baseEnd_2449977] using wordTrace_append hprefix tailTrace_2449977
  have hstable : (prefixWord ++ tailWord_2449977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449977).length < 2 ^ (prefixWord ++ tailWord_2449977).sum := by decide
  have hdescent : baseEnd_2449977 < baseStart_2449977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449980 : List Nat := [2, 2, 2, 2, 3, 1, 4, 7]
def baseStart_2449980 : Nat := 118140960795 + 2449980 * 2 ^ 59
def prefixEnd_2449980 : Nat := 4983230072969 + 3 ^ 40 * 2449980 * 2
def baseEnd_2449980 : Nat := 46593234588978876877139

theorem tailTrace_2449980 : CollatzResearch.WordTrace tailWord_2449980 prefixEnd_2449980 46593234588978876877139 := by
  unfold tailWord_2449980
  simp only [CollatzResearch.WordTrace]
  refine ⟨44679055832074179058365697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59572074442765572077820929 44679055832074179058365697)
  ·
    refine ⟨33509291874055634293774273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44679055832074179058365697 33509291874055634293774273)
    ·
      refine ⟨25131968905541725720330705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33509291874055634293774273 25131968905541725720330705)
      ·
        refine ⟨18848976679156294290248029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25131968905541725720330705 18848976679156294290248029)
        ·
          refine ⟨7068366254683610358843011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18848976679156294290248029 7068366254683610358843011)
          ·
            refine ⟨10602549382025415538264517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7068366254683610358843011 10602549382025415538264517)
            ·
              refine ⟨1987978009129765413424597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10602549382025415538264517 1987978009129765413424597)
              ·
                refine ⟨46593234588978876877139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1987978009129765413424597 46593234588978876877139)
                ·
                  rfl

theorem cell23_2449980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 7].length) (baseStart_2449980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449980 prefixEnd_2449980 := by exact prefixLift 2449980
  have htrace : WordTrace (prefixWord ++ tailWord_2449980) baseStart_2449980 baseEnd_2449980 := by
    simpa [prefixWord, tailWord_2449980, baseEnd_2449980] using wordTrace_append hprefix tailTrace_2449980
  have hstable : (prefixWord ++ tailWord_2449980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449980).length < 2 ^ (prefixWord ++ tailWord_2449980).sum := by decide
  have hdescent : baseEnd_2449980 < baseStart_2449980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2449991 : List Nat := [1, 1, 4, 1, 4, 1, 3, 3, 1, 2, 2]
def baseStart_2449991 : Nat := 118140960795 + 2449991 * 2 ^ 59
def prefixEnd_2449991 : Nat := 4983230072969 + 3 ^ 40 * 2449991 * 2
def baseEnd_2449991 : Nat := 1258022982189629132645203

theorem tailTrace_2449991 : CollatzResearch.WordTrace tailWord_2449991 prefixEnd_2449991 1258022982189629132645203 := by
  unfold tailWord_2449991
  simp only [CollatzResearch.WordTrace]
  refine ⟨89358512867108506995381827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59572341911405671330254551 89358512867108506995381827)
  ·
    refine ⟨134037769300662760493072741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89358512867108506995381827 134037769300662760493072741)
    ·
      refine ⟨25132081743874267592451139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134037769300662760493072741 25132081743874267592451139)
      ·
        refine ⟨37698122615811401388676709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25132081743874267592451139 37698122615811401388676709)
        ·
          refine ⟨7068397990464637760376883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37698122615811401388676709 7068397990464637760376883)
          ·
            refine ⟨10602596985696956640565325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7068397990464637760376883 10602596985696956640565325)
            ·
              refine ⟨3975973869636358740211997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10602596985696956640565325 3975973869636358740211997)
              ·
                refine ⟨1490990201113634527579499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3975973869636358740211997 1490990201113634527579499)
                ·
                  refine ⟨2236485301670451791369249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1490990201113634527579499 2236485301670451791369249)
                  ·
                    refine ⟨1677363976252838843526937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2236485301670451791369249 1677363976252838843526937)
                    ·
                      refine ⟨1258022982189629132645203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677363976252838843526937 1258022982189629132645203)
                      ·
                        rfl

theorem cell23_2449991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 3, 3, 1, 2, 2].length) (baseStart_2449991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2449991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2449991 prefixEnd_2449991 := by exact prefixLift 2449991
  have htrace : WordTrace (prefixWord ++ tailWord_2449991) baseStart_2449991 baseEnd_2449991 := by
    simpa [prefixWord, tailWord_2449991, baseEnd_2449991] using wordTrace_append hprefix tailTrace_2449991
  have hstable : (prefixWord ++ tailWord_2449991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2449991).length < 2 ^ (prefixWord ++ tailWord_2449991).sum := by decide
  have hdescent : baseEnd_2449991 < baseStart_2449991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2449991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450007 : List Nat := [1, 1, 3, 2, 2, 2, 2, 4, 2, 1, 3]
def baseStart_2450007 : Nat := 118140960795 + 2450007 * 2 ^ 59
def prefixEnd_2450007 : Nat := 4983230072969 + 3 ^ 40 * 2450007 * 2
def baseEnd_2450007 : Nat := 1258031197880101070045129

theorem tailTrace_2450007 : CollatzResearch.WordTrace tailWord_2450007 prefixEnd_2450007 1258031197880101070045129 := by
  unfold tailWord_2450007
  simp only [CollatzResearch.WordTrace]
  refine ⟨89359096435050541727964275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59572730956700361151976183 89359096435050541727964275)
  ·
    refine ⟨134038644652575812591946413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89359096435050541727964275 134038644652575812591946413)
    ·
      refine ⟨50264491744715929721979905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134038644652575812591946413 50264491744715929721979905)
      ·
        refine ⟨37698368808536947291484929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50264491744715929721979905 37698368808536947291484929)
        ·
          refine ⟨28273776606402710468613697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37698368808536947291484929 28273776606402710468613697)
          ·
            refine ⟨21205332454802032851460273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28273776606402710468613697 21205332454802032851460273)
            ·
              refine ⟨15903999341101524638595205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21205332454802032851460273 15903999341101524638595205)
              ·
                refine ⟨2981999876456535869736601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15903999341101524638595205 2981999876456535869736601)
                ·
                  refine ⟨2236499907342401902302451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2981999876456535869736601 2236499907342401902302451)
                  ·
                    refine ⟨3354749861013602853453677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2236499907342401902302451 3354749861013602853453677)
                    ·
                      refine ⟨1258031197880101070045129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3354749861013602853453677 1258031197880101070045129)
                      ·
                        rfl

theorem cell23_2450007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_2450007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450007 prefixEnd_2450007 := by exact prefixLift 2450007
  have htrace : WordTrace (prefixWord ++ tailWord_2450007) baseStart_2450007 baseEnd_2450007 := by
    simpa [prefixWord, tailWord_2450007, baseEnd_2450007] using wordTrace_append hprefix tailTrace_2450007
  have hstable : (prefixWord ++ tailWord_2450007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450007).length < 2 ^ (prefixWord ++ tailWord_2450007).sum := by decide
  have hdescent : baseEnd_2450007 < baseStart_2450007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450018 : List Nat := [3, 3, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_2450018 : Nat := 118140960795 + 2450018 * 2 ^ 59
def prefixEnd_2450018 : Nat := 4983230072969 + 3 ^ 40 * 2450018 * 2
def baseEnd_2450018 : Nat := 419345615389100175669193

theorem tailTrace_2450018 : CollatzResearch.WordTrace tailWord_2450018 prefixEnd_2450018 419345615389100175669193 := by
  unfold tailWord_2450018
  simp only [CollatzResearch.WordTrace]
  refine ⟨22339874409502672651653677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59572998425340460404409805 22339874409502672651653677)
  ·
    refine ⟨8377452903563502244370129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22339874409502672651653677 8377452903563502244370129)
    ·
      refine ⟨6283089677672626683277597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8377452903563502244370129 6283089677672626683277597)
      ·
        refine ⟨2356158629127235006229099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6283089677672626683277597 2356158629127235006229099)
        ·
          refine ⟨3534237943690852509343649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2356158629127235006229099 3534237943690852509343649)
          ·
            refine ⟨2650678457768139382007737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3534237943690852509343649 2650678457768139382007737)
            ·
              refine ⟨1988008843326104536505803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2650678457768139382007737 1988008843326104536505803)
              ·
                refine ⟨2982013264989156804758705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1988008843326104536505803 2982013264989156804758705)
                ·
                  refine ⟨2236509948741867603569029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2982013264989156804758705 2236509948741867603569029)
                  ·
                    refine ⟨419345615389100175669193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2236509948741867603569029 419345615389100175669193)
                    ·
                      rfl

theorem cell23_2450018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_2450018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450018 prefixEnd_2450018 := by exact prefixLift 2450018
  have htrace : WordTrace (prefixWord ++ tailWord_2450018) baseStart_2450018 baseEnd_2450018 := by
    simpa [prefixWord, tailWord_2450018, baseEnd_2450018] using wordTrace_append hprefix tailTrace_2450018
  have hstable : (prefixWord ++ tailWord_2450018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450018).length < 2 ^ (prefixWord ++ tailWord_2450018).sum := by decide
  have hdescent : baseEnd_2450018 < baseStart_2450018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450023 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 1, 8]
def baseStart_2450023 : Nat := 118140960795 + 2450023 * 2 ^ 59
def prefixEnd_2450023 : Nat := 4983230072969 + 3 ^ 40 * 2450023 * 2
def baseEnd_2450023 : Nat := 419346471190191002481685

theorem tailTrace_2450023 : CollatzResearch.WordTrace tailWord_2450023 prefixEnd_2450023 419346471190191002481685 := by
  unfold tailWord_2450023
  simp only [CollatzResearch.WordTrace]
  refine ⟨89359680002992576460546723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59573120001995050973697815 89359680002992576460546723)
  ·
    refine ⟨134039520004488864690820085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89359680002992576460546723 134039520004488864690820085)
    ·
      refine ⟨12566205000420831064764383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134039520004488864690820085 12566205000420831064764383)
      ·
        refine ⟨18849307500631246597146575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12566205000420831064764383 18849307500631246597146575)
        ·
          refine ⟨28273961250946869895719863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18849307500631246597146575 28273961250946869895719863)
          ·
            refine ⟨42410941876420304843579795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28273961250946869895719863 42410941876420304843579795)
            ·
              refine ⟨63616412814630457265369693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42410941876420304843579795 63616412814630457265369693)
              ·
                refine ⟨23856154805486421474513635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63616412814630457265369693 23856154805486421474513635)
                ·
                  refine ⟨35784232208229632211770453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23856154805486421474513635 35784232208229632211770453)
                  ·
                    refine ⟨419346471190191002481685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35784232208229632211770453 419346471190191002481685)
                    ·
                      rfl

theorem cell23_2450023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_2450023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450023 prefixEnd_2450023 := by exact prefixLift 2450023
  have htrace : WordTrace (prefixWord ++ tailWord_2450023) baseStart_2450023 baseEnd_2450023 := by
    simpa [prefixWord, tailWord_2450023, baseEnd_2450023] using wordTrace_append hprefix tailTrace_2450023
  have hstable : (prefixWord ++ tailWord_2450023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450023).length < 2 ^ (prefixWord ++ tailWord_2450023).sum := by decide
  have hdescent : baseEnd_2450023 < baseStart_2450023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450034 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 3, 3, 2]
def baseStart_2450034 : Nat := 118140960795 + 2450034 * 2 ^ 59
def prefixEnd_2450034 : Nat := 4983230072969 + 3 ^ 40 * 2450034 * 2
def baseEnd_2450034 : Nat := 1258045061857772464407505

theorem tailTrace_2450034 : CollatzResearch.WordTrace tailWord_2450034 prefixEnd_2450034 1258045061857772464407505 := by
  unfold tailWord_2450034
  simp only [CollatzResearch.WordTrace]
  refine ⟨22340020301488181334799289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59573387470635150226131437 22340020301488181334799289)
  ·
    refine ⟨16755015226116136001099467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22340020301488181334799289 16755015226116136001099467)
    ·
      refine ⟨25132522839174204001649201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16755015226116136001099467 25132522839174204001649201)
      ·
        refine ⟨18849392129380653001236901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25132522839174204001649201 18849392129380653001236901)
        ·
          refine ⟨3534261024258872437731919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18849392129380653001236901 3534261024258872437731919)
          ·
            refine ⟨5301391536388308656597879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3534261024258872437731919 5301391536388308656597879)
            ·
              refine ⟨7952087304582462984896819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5301391536388308656597879 7952087304582462984896819)
              ·
                refine ⟨11928130956873694477345229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7952087304582462984896819 11928130956873694477345229)
                ·
                  refine ⟨4473049108827635429004461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11928130956873694477345229 4473049108827635429004461)
                  ·
                    refine ⟨1677393415810363285876673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4473049108827635429004461 1677393415810363285876673)
                    ·
                      refine ⟨1258045061857772464407505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677393415810363285876673 1258045061857772464407505)
                      ·
                        rfl

theorem cell23_2450034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_2450034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450034 prefixEnd_2450034 := by exact prefixLift 2450034
  have htrace : WordTrace (prefixWord ++ tailWord_2450034) baseStart_2450034 baseEnd_2450034 := by
    simpa [prefixWord, tailWord_2450034, baseEnd_2450034] using wordTrace_append hprefix tailTrace_2450034
  have hstable : (prefixWord ++ tailWord_2450034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450034).length < 2 ^ (prefixWord ++ tailWord_2450034).sum := by decide
  have hdescent : baseEnd_2450034 < baseStart_2450034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450043 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 4]
def baseStart_2450043 : Nat := 118140960795 + 2450043 * 2 ^ 59
def prefixEnd_2450043 : Nat := 4983230072969 + 3 ^ 40 * 2450043 * 2
def baseEnd_2450043 : Nat := 1258049683183662929194963

theorem tailTrace_2450043 : CollatzResearch.WordTrace tailWord_2450043 prefixEnd_2450043 1258049683183662929194963 := by
  unfold tailWord_2450043
  simp only [CollatzResearch.WordTrace]
  refine ⟨89360409462920119876274783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59573606308613413250849855 89360409462920119876274783)
  ·
    refine ⟨134040614194380179814412175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89360409462920119876274783 134040614194380179814412175)
    ·
      refine ⟨201060921291570269721618263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134040614194380179814412175 201060921291570269721618263)
      ·
        refine ⟨301591381937355404582427395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201060921291570269721618263 301591381937355404582427395)
        ·
          refine ⟨452387072906033106873641093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301591381937355404582427395 452387072906033106873641093)
          ·
            refine ⟨84822576169881207538807705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 452387072906033106873641093 84822576169881207538807705)
            ·
              refine ⟨63616932127410905654105779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84822576169881207538807705 63616932127410905654105779)
              ·
                refine ⟨95425398191116358481158669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63616932127410905654105779 95425398191116358481158669)
                ·
                  refine ⟨35784524321668634430434501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95425398191116358481158669 35784524321668634430434501)
                  ·
                    refine ⟨6709598310312868955706469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35784524321668634430434501 6709598310312868955706469)
                    ·
                      refine ⟨1258049683183662929194963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6709598310312868955706469 1258049683183662929194963)
                      ·
                        rfl

theorem cell23_2450043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 4].length) (baseStart_2450043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450043 prefixEnd_2450043 := by exact prefixLift 2450043
  have htrace : WordTrace (prefixWord ++ tailWord_2450043) baseStart_2450043 baseEnd_2450043 := by
    simpa [prefixWord, tailWord_2450043, baseEnd_2450043] using wordTrace_append hprefix tailTrace_2450043
  have hstable : (prefixWord ++ tailWord_2450043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450043).length < 2 ^ (prefixWord ++ tailWord_2450043).sum := by decide
  have hdescent : baseEnd_2450043 < baseStart_2450043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450047 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 4, 2, 2]
def baseStart_2450047 : Nat := 118140960795 + 2450047 * 2 ^ 59
def prefixEnd_2450047 : Nat := 4983230072969 + 3 ^ 40 * 2450047 * 2
def baseEnd_2450047 : Nat := 1258051737106280913544945

theorem tailTrace_2450047 : CollatzResearch.WordTrace tailWord_2450047 prefixEnd_2450047 1258051737106280913544945 := by
  unfold tailWord_2450047
  simp only [CollatzResearch.WordTrace]
  refine ⟨89360555354905628559420395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59573703569937085706280263 89360555354905628559420395)
  ·
    refine ⟨134040833032358442839130593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89360555354905628559420395 134040833032358442839130593)
    ·
      refine ⟨100530624774268832129347945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134040833032358442839130593 100530624774268832129347945)
      ·
        refine ⟨75397968580701624097010959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100530624774268832129347945 75397968580701624097010959)
        ·
          refine ⟨113096952871052436145516439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75397968580701624097010959 113096952871052436145516439)
          ·
            refine ⟨169645429306578654218274659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113096952871052436145516439 169645429306578654218274659)
            ·
              refine ⟨254468143959867981327411989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169645429306578654218274659 254468143959867981327411989)
              ·
                refine ⟨11928194248118811624722437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 254468143959867981327411989 11928194248118811624722437)
                ·
                  refine ⟨2236536421522277179635457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11928194248118811624722437 2236536421522277179635457)
                  ·
                    refine ⟨1677402316141707884726593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2236536421522277179635457 1677402316141707884726593)
                    ·
                      refine ⟨1258051737106280913544945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677402316141707884726593 1258051737106280913544945)
                      ·
                        rfl

theorem cell23_2450047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 4, 2, 2].length) (baseStart_2450047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450047 prefixEnd_2450047 := by exact prefixLift 2450047
  have htrace : WordTrace (prefixWord ++ tailWord_2450047) baseStart_2450047 baseEnd_2450047 := by
    simpa [prefixWord, tailWord_2450047, baseEnd_2450047] using wordTrace_append hprefix tailTrace_2450047
  have hstable : (prefixWord ++ tailWord_2450047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450047).length < 2 ^ (prefixWord ++ tailWord_2450047).sum := by decide
  have hdescent : baseEnd_2450047 < baseStart_2450047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450102 : List Nat := [5, 1, 3, 1, 3, 1, 2, 1, 1, 3, 2]
def baseStart_2450102 : Nat := 118140960795 + 2450102 * 2 ^ 59
def prefixEnd_2450102 : Nat := 4983230072969 + 3 ^ 40 * 2450102 * 2
def baseEnd_2450102 : Nat := 1258079978542278198357193

theorem tailTrace_2450102 : CollatzResearch.WordTrace tailWord_2450102 prefixEnd_2450102 1258079978542278198357193 := by
  unfold tailWord_2450102
  simp only [CollatzResearch.WordTrace]
  refine ⟨5585160085606648309542035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59575040913137581968448373 5585160085606648309542035)
  ·
    refine ⟨8377740128409972464313053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5585160085606648309542035 8377740128409972464313053)
    ·
      refine ⟨3141652548153739674117395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8377740128409972464313053 3141652548153739674117395)
      ·
        refine ⟨4712478822230609511176093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3141652548153739674117395 4712478822230609511176093)
        ·
          refine ⟨1767179558336478566691035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4712478822230609511176093 1767179558336478566691035)
          ·
            refine ⟨2650769337504717850036553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1767179558336478566691035 2650769337504717850036553)
            ·
              refine ⟨1988077003128538387527415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2650769337504717850036553 1988077003128538387527415)
              ·
                refine ⟨2982115504692807581291123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1988077003128538387527415 2982115504692807581291123)
                ·
                  refine ⟨4473173257039211371936685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2982115504692807581291123 4473173257039211371936685)
                  ·
                    refine ⟨1677439971389704264476257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4473173257039211371936685 1677439971389704264476257)
                    ·
                      refine ⟨1258079978542278198357193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677439971389704264476257 1258079978542278198357193)
                      ·
                        rfl

theorem cell23_2450102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_2450102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450102 prefixEnd_2450102 := by exact prefixLift 2450102
  have htrace : WordTrace (prefixWord ++ tailWord_2450102) baseStart_2450102 baseEnd_2450102 := by
    simpa [prefixWord, tailWord_2450102, baseEnd_2450102] using wordTrace_append hprefix tailTrace_2450102
  have hstable : (prefixWord ++ tailWord_2450102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450102).length < 2 ^ (prefixWord ++ tailWord_2450102).sum := by decide
  have hdescent : baseEnd_2450102 < baseStart_2450102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450137 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 2, 4, 2]
def baseStart_2450137 : Nat := 118140960795 + 2450137 * 2 ^ 59
def prefixEnd_2450137 : Nat := 4983230072969 + 3 ^ 40 * 2450137 * 2
def baseEnd_2450137 : Nat := 1258097950365185561419531

theorem tailTrace_2450137 : CollatzResearch.WordTrace tailWord_2450137 prefixEnd_2450137 1258097950365185561419531 := by
  unfold tailWord_2450137
  simp only [CollatzResearch.WordTrace]
  refine ⟨89363837924579573930196665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59575891949719715953464443 89363837924579573930196665)
  ·
    refine ⟨67022878443434680447647499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89363837924579573930196665 67022878443434680447647499)
    ·
      refine ⟨100534317665152020671471249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67022878443434680447647499 100534317665152020671471249)
      ·
        refine ⟨75400738248864015503603437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100534317665152020671471249 75400738248864015503603437)
        ·
          refine ⟨28275276843324005813851289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75400738248864015503603437 28275276843324005813851289)
          ·
            refine ⟨21206457632493004360388467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28275276843324005813851289 21206457632493004360388467)
            ·
              refine ⟨31809686448739506540582701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21206457632493004360388467 31809686448739506540582701)
              ·
                refine ⟨11928632418277314952718513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31809686448739506540582701 11928632418277314952718513)
                ·
                  refine ⟨8946474313707986214538885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11928632418277314952718513 8946474313707986214538885)
                  ·
                    refine ⟨1677463933820247415226041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8946474313707986214538885 1677463933820247415226041)
                    ·
                      refine ⟨1258097950365185561419531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677463933820247415226041 1258097950365185561419531)
                      ·
                        rfl

theorem cell23_2450137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 4, 2].length) (baseStart_2450137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450137 prefixEnd_2450137 := by exact prefixLift 2450137
  have htrace : WordTrace (prefixWord ++ tailWord_2450137) baseStart_2450137 baseEnd_2450137 := by
    simpa [prefixWord, tailWord_2450137, baseEnd_2450137] using wordTrace_append hprefix tailTrace_2450137
  have hstable : (prefixWord ++ tailWord_2450137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450137).length < 2 ^ (prefixWord ++ tailWord_2450137).sum := by decide
  have hdescent : baseEnd_2450137 < baseStart_2450137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450157 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_2450157 : Nat := 118140960795 + 2450157 * 2 ^ 59
def prefixEnd_2450157 : Nat := 4983230072969 + 3 ^ 40 * 2450157 * 2
def baseEnd_2450157 : Nat := 1258108219978275483169439

theorem tailTrace_2450157 : CollatzResearch.WordTrace tailWord_2450157 prefixEnd_2450157 1258108219978275483169439 := by
  unfold tailWord_2450157
  simp only [CollatzResearch.WordTrace]
  refine ⟨89364567384507117345924725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59576378256338078230616483 89364567384507117345924725)
  ·
    refine ⟨8377928192297542251180443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89364567384507117345924725 8377928192297542251180443)
    ·
      refine ⟨12566892288446313376770665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8377928192297542251180443 12566892288446313376770665)
      ·
        refine ⟨9425169216334735032577999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12566892288446313376770665 9425169216334735032577999)
        ·
          refine ⟨14137753824502102548866999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9425169216334735032577999 14137753824502102548866999)
          ·
            refine ⟨21206630736753153823300499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14137753824502102548866999 21206630736753153823300499)
            ·
              refine ⟨31809946105129730734950749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21206630736753153823300499 31809946105129730734950749)
              ·
                refine ⟨11928729789423649025606531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31809946105129730734950749 11928729789423649025606531)
                ·
                  refine ⟨17893094684135473538409797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11928729789423649025606531 17893094684135473538409797)
                  ·
                    refine ⟨3354955253275401288451837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17893094684135473538409797 3354955253275401288451837)
                    ·
                      refine ⟨1258108219978275483169439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3354955253275401288451837 1258108219978275483169439)
                      ·
                        rfl

theorem cell23_2450157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_2450157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450157 prefixEnd_2450157 := by exact prefixLift 2450157
  have htrace : WordTrace (prefixWord ++ tailWord_2450157) baseStart_2450157 baseEnd_2450157 := by
    simpa [prefixWord, tailWord_2450157, baseEnd_2450157] using wordTrace_append hprefix tailTrace_2450157
  have hstable : (prefixWord ++ tailWord_2450157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450157).length < 2 ^ (prefixWord ++ tailWord_2450157).sum := by decide
  have hdescent : baseEnd_2450157 < baseStart_2450157 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450174 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_2450174 : Nat := 118140960795 + 2450174 * 2 ^ 59
def prefixEnd_2450174 : Nat := 4983230072969 + 3 ^ 40 * 2450174 * 2
def baseEnd_2450174 : Nat := 1258116949149401916656861

theorem tailTrace_2450174 : CollatzResearch.WordTrace tailWord_2450174 prefixEnd_2450174 1258116949149401916656861 := by
  unfold tailWord_2450174
  simp only [CollatzResearch.WordTrace]
  refine ⟨11170648428180691156161697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59576791616963686166195717 11170648428180691156161697)
  ·
    refine ⟨8377986321135518367121273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11170648428180691156161697 8377986321135518367121273)
    ·
      refine ⟨6283489740851638775340955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8377986321135518367121273 6283489740851638775340955)
      ·
        refine ⟨9425234611277458163011433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6283489740851638775340955 9425234611277458163011433)
        ·
          refine ⟨7068925958458093622258575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9425234611277458163011433 7068925958458093622258575)
          ·
            refine ⟨10603388937687140433387863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7068925958458093622258575 10603388937687140433387863)
            ·
              refine ⟨15905083406530710650081795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10603388937687140433387863 15905083406530710650081795)
              ·
                refine ⟨23857625109796065975122693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15905083406530710650081795 23857625109796065975122693)
                ·
                  refine ⟨4473304708086762370335505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23857625109796065975122693 4473304708086762370335505)
                  ·
                    refine ⟨3354978531065071777751629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4473304708086762370335505 3354978531065071777751629)
                    ·
                      refine ⟨1258116949149401916656861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3354978531065071777751629 1258116949149401916656861)
                      ·
                        rfl

theorem cell23_2450174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_2450174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450174 prefixEnd_2450174 := by exact prefixLift 2450174
  have htrace : WordTrace (prefixWord ++ tailWord_2450174) baseStart_2450174 baseEnd_2450174 := by
    simpa [prefixWord, tailWord_2450174, baseEnd_2450174] using wordTrace_append hprefix tailTrace_2450174
  have hstable : (prefixWord ++ tailWord_2450174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450174).length < 2 ^ (prefixWord ++ tailWord_2450174).sum := by decide
  have hdescent : baseEnd_2450174 < baseStart_2450174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450190 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 2, 9]
def baseStart_2450190 : Nat := 118140960795 + 2450190 * 2 ^ 59
def prefixEnd_2450190 : Nat := 4983230072969 + 3 ^ 40 * 2450190 * 2
def baseEnd_2450190 : Nat := 419375054946624618018929

theorem tailTrace_2450190 : CollatzResearch.WordTrace tailWord_2450190 prefixEnd_2450190 419375054946624618018929 := by
  unfold tailWord_2450190
  simp only [CollatzResearch.WordTrace]
  refine ⟨11170721374173445497734503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59577180662258375987917349 11170721374173445497734503)
  ·
    refine ⟨16756082061260168246601755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11170721374173445497734503 16756082061260168246601755)
    ·
      refine ⟨25134123091890252369902633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16756082061260168246601755 25134123091890252369902633)
      ·
        refine ⟨18850592318917689277426975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25134123091890252369902633 18850592318917689277426975)
        ·
          refine ⟨28275888478376533916140463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18850592318917689277426975 28275888478376533916140463)
          ·
            refine ⟨42413832717564800874210695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28275888478376533916140463 42413832717564800874210695)
            ·
              refine ⟨63620749076347201311316043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42413832717564800874210695 63620749076347201311316043)
              ·
                refine ⟨95431123614520801966974065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63620749076347201311316043 95431123614520801966974065)
                ·
                  refine ⟨71573342710890601475230549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95431123614520801966974065 71573342710890601475230549)
                  ·
                    refine ⟨419375054946624618018929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 71573342710890601475230549 419375054946624618018929)
                    ·
                      rfl

theorem cell23_2450190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_2450190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450190 prefixEnd_2450190 := by exact prefixLift 2450190
  have htrace : WordTrace (prefixWord ++ tailWord_2450190) baseStart_2450190 baseEnd_2450190 := by
    simpa [prefixWord, tailWord_2450190, baseEnd_2450190] using wordTrace_append hprefix tailTrace_2450190
  have hstable : (prefixWord ++ tailWord_2450190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450190).length < 2 ^ (prefixWord ++ tailWord_2450190).sum := by decide
  have hdescent : baseEnd_2450190 < baseStart_2450190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450207 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 3, 5]
def baseStart_2450207 : Nat := 118140960795 + 2450207 * 2 ^ 59
def prefixEnd_2450207 : Nat := 4983230072969 + 3 ^ 40 * 2450207 * 2
def baseEnd_2450207 : Nat := 419377964670333429181403

theorem tailTrace_2450207 : CollatzResearch.WordTrace tailWord_2450207 prefixEnd_2450207 419377964670333429181403 := by
  unfold tailWord_2450207
  simp only [CollatzResearch.WordTrace]
  refine ⟨89366391034325975885244875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59577594022883983923496583 89366391034325975885244875)
  ·
    refine ⟨134049586551488963827867313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89366391034325975885244875 134049586551488963827867313)
    ·
      refine ⟨100537189913616722870900485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134049586551488963827867313 100537189913616722870900485)
      ·
        refine ⟨18850723108803135538293841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100537189913616722870900485 18850723108803135538293841)
        ·
          refine ⟨14138042331602351653720381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18850723108803135538293841 14138042331602351653720381)
          ·
            refine ⟨5301765874350881870145143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14138042331602351653720381 5301765874350881870145143)
            ·
              refine ⟨7952648811526322805217715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5301765874350881870145143 7952648811526322805217715)
              ·
                refine ⟨11928973217289484207826573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7952648811526322805217715 11928973217289484207826573)
                ·
                  refine ⟨4473364956483556577934965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11928973217289484207826573 4473364956483556577934965)
                  ·
                    refine ⟨419377964670333429181403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4473364956483556577934965 419377964670333429181403)
                    ·
                      rfl

theorem cell23_2450207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 5].length) (baseStart_2450207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450207 prefixEnd_2450207 := by exact prefixLift 2450207
  have htrace : WordTrace (prefixWord ++ tailWord_2450207) baseStart_2450207 baseEnd_2450207 := by
    simpa [prefixWord, tailWord_2450207, baseEnd_2450207] using wordTrace_append hprefix tailTrace_2450207
  have hstable : (prefixWord ++ tailWord_2450207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450207).length < 2 ^ (prefixWord ++ tailWord_2450207).sum := by decide
  have hdescent : baseEnd_2450207 < baseStart_2450207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450240 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 6]
def baseStart_2450240 : Nat := 118140960795 + 2450240 * 2 ^ 59
def prefixEnd_2450240 : Nat := 4983230072969 + 3 ^ 40 * 2450240 * 2
def baseEnd_2450240 : Nat := 1258150838872598658431557

theorem tailTrace_2450240 : CollatzResearch.WordTrace tailWord_2450240 prefixEnd_2450240 1258150838872598658431557 := by
  unfold tailWord_2450240
  simp only [CollatzResearch.WordTrace]
  refine ⟨44683797321603211260598087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59578396428804281680797449 44683797321603211260598087)
  ·
    refine ⟨67025695982404816890897131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44683797321603211260598087 67025695982404816890897131)
    ·
      refine ⟨100538543973607225336345697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67025695982404816890897131 100538543973607225336345697)
      ·
        refine ⟨75403907980205419002259273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100538543973607225336345697 75403907980205419002259273)
        ·
          refine ⟨56552930985154064251694455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75403907980205419002259273 56552930985154064251694455)
          ·
            refine ⟨84829396477731096377541683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56552930985154064251694455 84829396477731096377541683)
            ·
              refine ⟨127244094716596644566312525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84829396477731096377541683 127244094716596644566312525)
              ·
                refine ⟨47716535518723741712367197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127244094716596644566312525 47716535518723741712367197)
                ·
                  refine ⟨17893700819521403142137699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47716535518723741712367197 17893700819521403142137699)
                  ·
                    refine ⟨26840551229282104713206549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17893700819521403142137699 26840551229282104713206549)
                    ·
                      refine ⟨1258150838872598658431557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26840551229282104713206549 1258150838872598658431557)
                      ·
                        rfl

theorem cell23_2450240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_2450240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450240 prefixEnd_2450240 := by exact prefixLift 2450240
  have htrace : WordTrace (prefixWord ++ tailWord_2450240) baseStart_2450240 baseEnd_2450240 := by
    simpa [prefixWord, tailWord_2450240, baseEnd_2450240] using wordTrace_append hprefix tailTrace_2450240
  have hstable : (prefixWord ++ tailWord_2450240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450240).length < 2 ^ (prefixWord ++ tailWord_2450240).sum := by decide
  have hdescent : baseEnd_2450240 < baseStart_2450240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450250 : List Nat := [3, 1, 2, 1, 1, 1, 2, 12]
def baseStart_2450250 : Nat := 118140960795 + 2450250 * 2 ^ 59
def prefixEnd_2450250 : Nat := 4983230072969 + 3 ^ 40 * 2450250 * 2
def baseEnd_2450250 : Nat := 46598369395523837752093

theorem tailTrace_2450250 : CollatzResearch.WordTrace tailWord_2450250 prefixEnd_2450250 46598369395523837752093 := by
  unfold tailWord_2450250
  simp only [CollatzResearch.WordTrace]
  refine ⟨22341989843292548557265051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59578639582113462819373469 22341989843292548557265051)
  ·
    refine ⟨33512984764938822835897577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22341989843292548557265051 33512984764938822835897577)
    ·
      refine ⟨25134738573704117126923183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33512984764938822835897577 25134738573704117126923183)
      ·
        refine ⟨37702107860556175690384775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25134738573704117126923183 37702107860556175690384775)
        ·
          refine ⟨56553161790834263535577163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37702107860556175690384775 56553161790834263535577163)
          ·
            refine ⟨84829742686251395303365745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56553161790834263535577163 84829742686251395303365745)
            ·
              refine ⟨63622307014688546477524309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84829742686251395303365745 63622307014688546477524309)
              ·
                refine ⟨46598369395523837752093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 63622307014688546477524309 46598369395523837752093)
                ·
                  rfl

theorem cell23_2450250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 12].length) (baseStart_2450250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450250 prefixEnd_2450250 := by exact prefixLift 2450250
  have htrace : WordTrace (prefixWord ++ tailWord_2450250) baseStart_2450250 baseEnd_2450250 := by
    simpa [prefixWord, tailWord_2450250, baseEnd_2450250] using wordTrace_append hprefix tailTrace_2450250
  have hstable : (prefixWord ++ tailWord_2450250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450250).length < 2 ^ (prefixWord ++ tailWord_2450250).sum := by decide
  have hdescent : baseEnd_2450250 < baseStart_2450250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450261 : List Nat := [1, 3, 2, 2, 2, 1, 3, 2, 3, 2, 2]
def baseStart_2450261 : Nat := 118140960795 + 2450261 * 2 ^ 59
def prefixEnd_2450261 : Nat := 4983230072969 + 3 ^ 40 * 2450261 * 2
def baseEnd_2450261 : Nat := 1258161621966343076268961

theorem tailTrace_2450261 : CollatzResearch.WordTrace tailWord_2450261 prefixEnd_2450261 1258161621966343076268961 := by
  unfold tailWord_2450261
  simp only [CollatzResearch.WordTrace]
  refine ⟨89368360576130343107710637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59578907050753562071807091 89368360576130343107710637)
  ·
    refine ⟨33513135216048878665391489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89368360576130343107710637 33513135216048878665391489)
    ·
      refine ⟨25134851412036658999043617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33513135216048878665391489 25134851412036658999043617)
      ·
        refine ⟨18851138559027494249282713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25134851412036658999043617 18851138559027494249282713)
        ·
          refine ⟨14138353919270620686962035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18851138559027494249282713 14138353919270620686962035)
          ·
            refine ⟨21207530878905931030443053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14138353919270620686962035 21207530878905931030443053)
            ·
              refine ⟨7952824079589724136416145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21207530878905931030443053 7952824079589724136416145)
              ·
                refine ⟨5964618059692293102312109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7952824079589724136416145 5964618059692293102312109)
                ·
                  refine ⟨2236731772384609913367041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5964618059692293102312109 2236731772384609913367041)
                  ·
                    refine ⟨1677548829288457435025281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2236731772384609913367041 1677548829288457435025281)
                    ·
                      refine ⟨1258161621966343076268961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677548829288457435025281 1258161621966343076268961)
                      ·
                        rfl

theorem cell23_2450261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_2450261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450261 prefixEnd_2450261 := by exact prefixLift 2450261
  have htrace : WordTrace (prefixWord ++ tailWord_2450261) baseStart_2450261 baseEnd_2450261 := by
    simpa [prefixWord, tailWord_2450261, baseEnd_2450261] using wordTrace_append hprefix tailTrace_2450261
  have hstable : (prefixWord ++ tailWord_2450261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450261).length < 2 ^ (prefixWord ++ tailWord_2450261).sum := by decide
  have hdescent : baseEnd_2450261 < baseStart_2450261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450304 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 3, 3, 2]
def baseStart_2450304 : Nat := 118140960795 + 2450304 * 2 ^ 59
def prefixEnd_2450304 : Nat := 4983230072969 + 3 ^ 40 * 2450304 * 2
def baseEnd_2450304 : Nat := 1258183701634486408031263

theorem tailTrace_2450304 : CollatzResearch.WordTrace tailWord_2450304 prefixEnd_2450304 1258183701634486408031263 := by
  unfold tailWord_2450304
  simp only [CollatzResearch.WordTrace]
  refine ⟨44684964457487280725762983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59579952609983040967683977 44684964457487280725762983)
  ·
    refine ⟨67027446686230921088644475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44684964457487280725762983 67027446686230921088644475)
    ·
      refine ⟨100541170029346381632966713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67027446686230921088644475 100541170029346381632966713)
      ·
        refine ⟨75405877522009786224725035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100541170029346381632966713 75405877522009786224725035)
        ·
          refine ⟨113108816283014679337087553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75405877522009786224725035 113108816283014679337087553)
          ·
            refine ⟨84831612212261009502815665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113108816283014679337087553 84831612212261009502815665)
            ·
              refine ⟨63623709159195757127111749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84831612212261009502815665 63623709159195757127111749)
              ·
                refine ⟨11929445467349204461333453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63623709159195757127111749 11929445467349204461333453)
                ·
                  refine ⟨4473542050255951673000045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11929445467349204461333453 4473542050255951673000045)
                  ·
                    refine ⟨1677578268845981877375017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4473542050255951673000045 1677578268845981877375017)
                    ·
                      refine ⟨1258183701634486408031263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677578268845981877375017 1258183701634486408031263)
                      ·
                        rfl

theorem cell23_2450304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 3, 3, 2].length) (baseStart_2450304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450304 prefixEnd_2450304 := by exact prefixLift 2450304
  have htrace : WordTrace (prefixWord ++ tailWord_2450304) baseStart_2450304 baseEnd_2450304 := by
    simpa [prefixWord, tailWord_2450304, baseEnd_2450304] using wordTrace_append hprefix tailTrace_2450304
  have hstable : (prefixWord ++ tailWord_2450304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450304).length < 2 ^ (prefixWord ++ tailWord_2450304).sum := by decide
  have hdescent : baseEnd_2450304 < baseStart_2450304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450311 : List Nat := [1, 1, 4, 2, 3, 3, 1, 1, 1, 3, 3]
def baseStart_2450311 : Nat := 118140960795 + 2450311 * 2 ^ 59
def prefixEnd_2450311 : Nat := 4983230072969 + 3 ^ 40 * 2450311 * 2
def baseEnd_2450311 : Nat := 1258187295999067880643731

theorem tailTrace_2450311 : CollatzResearch.WordTrace tailWord_2450311 prefixEnd_2450311 1258187295999067880643731 := by
  unfold tailWord_2450311
  simp only [CollatzResearch.WordTrace]
  refine ⟨89370184225949201647030787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59580122817299467764687191 89370184225949201647030787)
  ·
    refine ⟨134055276338923802470546181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89370184225949201647030787 134055276338923802470546181)
    ·
      refine ⟨25135364313548212963227409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134055276338923802470546181 25135364313548212963227409)
      ·
        refine ⟨18851523235161159722420557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25135364313548212963227409 18851523235161159722420557)
        ·
          refine ⟨7069321213185434895907709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18851523235161159722420557 7069321213185434895907709)
          ·
            refine ⟨2650995454944538085965391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7069321213185434895907709 2650995454944538085965391)
            ·
              refine ⟨3976493182416807128948087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2650995454944538085965391 3976493182416807128948087)
              ·
                refine ⟨5964739773625210693422131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3976493182416807128948087 5964739773625210693422131)
                ·
                  refine ⟨8947109660437816040133197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5964739773625210693422131 8947109660437816040133197)
                  ·
                    refine ⟨3355166122664181015049949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8947109660437816040133197 3355166122664181015049949)
                    ·
                      refine ⟨1258187295999067880643731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3355166122664181015049949 1258187295999067880643731)
                      ·
                        rfl

theorem cell23_2450311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_2450311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450311 prefixEnd_2450311 := by exact prefixLift 2450311
  have htrace : WordTrace (prefixWord ++ tailWord_2450311) baseStart_2450311 baseEnd_2450311 := by
    simpa [prefixWord, tailWord_2450311, baseEnd_2450311] using wordTrace_append hprefix tailTrace_2450311
  have hstable : (prefixWord ++ tailWord_2450311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450311).length < 2 ^ (prefixWord ++ tailWord_2450311).sum := by decide
  have hdescent : baseEnd_2450311 < baseStart_2450311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450338 : List Nat := [3, 3, 1, 2, 2, 1, 2, 3, 1, 3, 2]
def baseStart_2450338 : Nat := 118140960795 + 2450338 * 2 ^ 59
def prefixEnd_2450338 : Nat := 4983230072969 + 3 ^ 40 * 2450338 * 2
def baseEnd_2450338 : Nat := 1258201159976739275006107

theorem tailTrace_2450338 : CollatzResearch.WordTrace tailWord_2450338 prefixEnd_2450338 1258201159976739275006107 := by
  unfold tailWord_2450338
  simp only [CollatzResearch.WordTrace]
  refine ⟨22342792249212846314565917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59580779331234256838842445 22342792249212846314565917)
  ·
    refine ⟨8378547093454817367962219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22342792249212846314565917 8378547093454817367962219)
    ·
      refine ⟨12567820640182226051943329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8378547093454817367962219 12567820640182226051943329)
      ·
        refine ⟨9425865480136669538957497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12567820640182226051943329 9425865480136669538957497)
        ·
          refine ⟨7069399110102502154218123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9425865480136669538957497 7069399110102502154218123)
          ·
            refine ⟨10604098665153753231327185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7069399110102502154218123 10604098665153753231327185)
            ·
              refine ⟨7953073998865314923495389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10604098665153753231327185 7953073998865314923495389)
              ·
                refine ⟨2982402749574493096310771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7953073998865314923495389 2982402749574493096310771)
                ·
                  refine ⟨4473604124361739644466157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2982402749574493096310771 4473604124361739644466157)
                  ·
                    refine ⟨1677601546635652366674809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4473604124361739644466157 1677601546635652366674809)
                    ·
                      refine ⟨1258201159976739275006107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677601546635652366674809 1258201159976739275006107)
                      ·
                        rfl

theorem cell23_2450338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_2450338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450338 prefixEnd_2450338 := by exact prefixLift 2450338
  have htrace : WordTrace (prefixWord ++ tailWord_2450338) baseStart_2450338 baseEnd_2450338 := by
    simpa [prefixWord, tailWord_2450338, baseEnd_2450338] using wordTrace_append hprefix tailTrace_2450338
  have hstable : (prefixWord ++ tailWord_2450338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450338).length < 2 ^ (prefixWord ++ tailWord_2450338).sum := by decide
  have hdescent : baseEnd_2450338 < baseStart_2450338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450368 : List Nat := [2, 1, 1, 2, 3, 4, 1, 3, 2, 2, 2]
def baseStart_2450368 : Nat := 118140960795 + 2450368 * 2 ^ 59
def prefixEnd_2450368 : Nat := 4983230072969 + 3 ^ 40 * 2450368 * 2
def baseEnd_2450368 : Nat := 1258216564396374157630969

theorem tailTrace_2450368 : CollatzResearch.WordTrace tailWord_2450368 prefixEnd_2450368 1258216564396374157630969 := by
  unfold tailWord_2450368
  simp only [CollatzResearch.WordTrace]
  refine ⟨44686131593371350190927879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59581508791161800254570505 44686131593371350190927879)
  ·
    refine ⟨67029197390057025286391819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44686131593371350190927879 67029197390057025286391819)
    ·
      refine ⟨100543796085085537929587729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67029197390057025286391819 100543796085085537929587729)
      ·
        refine ⟨75407847063814153447190797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100543796085085537929587729 75407847063814153447190797)
        ·
          refine ⟨28277942648930307542696549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75407847063814153447190797 28277942648930307542696549)
          ·
            refine ⟨5302114246674432664255603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28277942648930307542696549 5302114246674432664255603)
            ·
              refine ⟨7953171370011648996383405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5302114246674432664255603 7953171370011648996383405)
              ·
                refine ⟨2982439263754368373643777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7953171370011648996383405 2982439263754368373643777)
                ·
                  refine ⟨2236829447815776280232833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2982439263754368373643777 2236829447815776280232833)
                  ·
                    refine ⟨1677622085861832210174625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2236829447815776280232833 1677622085861832210174625)
                    ·
                      refine ⟨1258216564396374157630969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677622085861832210174625 1258216564396374157630969)
                      ·
                        rfl

theorem cell23_2450368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 3, 2, 2, 2].length) (baseStart_2450368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450368 prefixEnd_2450368 := by exact prefixLift 2450368
  have htrace : WordTrace (prefixWord ++ tailWord_2450368) baseStart_2450368 baseEnd_2450368 := by
    simpa [prefixWord, tailWord_2450368, baseEnd_2450368] using wordTrace_append hprefix tailTrace_2450368
  have hstable : (prefixWord ++ tailWord_2450368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450368).length < 2 ^ (prefixWord ++ tailWord_2450368).sum := by decide
  have hdescent : baseEnd_2450368 < baseStart_2450368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450372 : List Nat := [2, 3, 3, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_2450372 : Nat := 118140960795 + 2450372 * 2 ^ 59
def prefixEnd_2450372 : Nat := 4983230072969 + 3 ^ 40 * 2450372 * 2
def baseEnd_2450372 : Nat := 1258218618318992141980951

theorem tailTrace_2450372 : CollatzResearch.WordTrace tailWord_2450372 prefixEnd_2450372 1258218618318992141980951 := by
  unfold tailWord_2450372
  simp only [CollatzResearch.WordTrace]
  refine ⟨44686204539364104532500685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59581606052485472710000913 44686204539364104532500685)
  ·
    refine ⟨16757326702261539199687757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44686204539364104532500685 16757326702261539199687757)
    ·
      refine ⟨6283997513348077199882909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16757326702261539199687757 6283997513348077199882909)
      ·
        refine ⟨2356499067505528949956091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6283997513348077199882909 2356499067505528949956091)
        ·
          refine ⟨3534748601258293424934137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2356499067505528949956091 3534748601258293424934137)
          ·
            refine ⟨2651061450943720068700603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3534748601258293424934137 2651061450943720068700603)
            ·
              refine ⟨3976592176415580103050905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2651061450943720068700603 3976592176415580103050905)
              ·
                refine ⟨2982444132311685077288179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3976592176415580103050905 2982444132311685077288179)
                ·
                  refine ⟨4473666198467527615932269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2982444132311685077288179 4473666198467527615932269)
                  ·
                    refine ⟨1677624824425322855974601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4473666198467527615932269 1677624824425322855974601)
                    ·
                      refine ⟨1258218618318992141980951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677624824425322855974601 1258218618318992141980951)
                      ·
                        rfl

theorem cell23_2450372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_2450372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450372 prefixEnd_2450372 := by exact prefixLift 2450372
  have htrace : WordTrace (prefixWord ++ tailWord_2450372) baseStart_2450372 baseEnd_2450372 := by
    simpa [prefixWord, tailWord_2450372, baseEnd_2450372] using wordTrace_append hprefix tailTrace_2450372
  have hstable : (prefixWord ++ tailWord_2450372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450372).length < 2 ^ (prefixWord ++ tailWord_2450372).sum := by decide
  have hdescent : baseEnd_2450372 < baseStart_2450372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450402 : List Nat := [3, 3, 3, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_2450402 : Nat := 118140960795 + 2450402 * 2 ^ 59
def prefixEnd_2450402 : Nat := 4983230072969 + 3 ^ 40 * 2450402 * 2
def baseEnd_2450402 : Nat := 1258234022738627024605813

theorem tailTrace_2450402 : CollatzResearch.WordTrace tailWord_2450402 prefixEnd_2450402 1258234022738627024605813 := by
  unfold tailWord_2450402
  simp only [CollatzResearch.WordTrace]
  refine ⟨22343375817154881047148365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59582335512413016125728973 22343375817154881047148365)
  ·
    refine ⟨8378765931433080392680637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22343375817154881047148365 8378765931433080392680637)
    ·
      refine ⟨3142037224287405147255239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8378765931433080392680637 3142037224287405147255239)
      ·
        refine ⟨4713055836431107720882859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3142037224287405147255239 4713055836431107720882859)
        ·
          refine ⟨7069583754646661581324289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4713055836431107720882859 7069583754646661581324289)
          ·
            refine ⟨5302187815984996185993217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7069583754646661581324289 5302187815984996185993217)
            ·
              refine ⟨3976640861988747139494913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5302187815984996185993217 3976640861988747139494913)
              ·
                refine ⟨2982480646491560354621185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3976640861988747139494913 2982480646491560354621185)
                ·
                  refine ⟨2236860484868670265965889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2982480646491560354621185 2236860484868670265965889)
                  ·
                    refine ⟨1677645363651502699474417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2236860484868670265965889 1677645363651502699474417)
                    ·
                      refine ⟨1258234022738627024605813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677645363651502699474417 1258234022738627024605813)
                      ·
                        rfl

theorem cell23_2450402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_2450402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450402 prefixEnd_2450402 := by exact prefixLift 2450402
  have htrace : WordTrace (prefixWord ++ tailWord_2450402) baseStart_2450402 baseEnd_2450402 := by
    simpa [prefixWord, tailWord_2450402, baseEnd_2450402] using wordTrace_append hprefix tailTrace_2450402
  have hstable : (prefixWord ++ tailWord_2450402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450402).length < 2 ^ (prefixWord ++ tailWord_2450402).sum := by decide
  have hdescent : baseEnd_2450402 < baseStart_2450402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450418 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 2, 3, 3]
def baseStart_2450418 : Nat := 118140960795 + 2450418 * 2 ^ 59
def prefixEnd_2450418 : Nat := 4983230072969 + 3 ^ 40 * 2450418 * 2
def baseEnd_2450418 : Nat := 1258242238429098962005739

theorem tailTrace_2450418 : CollatzResearch.WordTrace tailWord_2450418 prefixEnd_2450418 1258242238429098962005739 := by
  unfold tailWord_2450418
  simp only [CollatzResearch.WordTrace]
  refine ⟨22343521709140389730293977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59582724557707705947450605 22343521709140389730293977)
  ·
    refine ⟨16757641281855292297720483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22343521709140389730293977 16757641281855292297720483)
    ·
      refine ⟨25136461922782938446580725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16757641281855292297720483 25136461922782938446580725)
      ·
        refine ⟨2356543305260900479366943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25136461922782938446580725 2356543305260900479366943)
        ·
          refine ⟨3534814957891350719050415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2356543305260900479366943 3534814957891350719050415)
          ·
            refine ⟨5302222436837026078575623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3534814957891350719050415 5302222436837026078575623)
            ·
              refine ⟨7953333655255539117863435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5302222436837026078575623 7953333655255539117863435)
              ·
                refine ⟨11930000482883308676795153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7953333655255539117863435 11930000482883308676795153)
                ·
                  refine ⟨8947500362162481507596365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11930000482883308676795153 8947500362162481507596365)
                  ·
                    refine ⟨3355312635810930565348637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8947500362162481507596365 3355312635810930565348637)
                    ·
                      refine ⟨1258242238429098962005739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3355312635810930565348637 1258242238429098962005739)
                      ·
                        rfl

theorem cell23_2450418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_2450418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450418 prefixEnd_2450418 := by exact prefixLift 2450418
  have htrace : WordTrace (prefixWord ++ tailWord_2450418) baseStart_2450418 baseEnd_2450418 := by
    simpa [prefixWord, tailWord_2450418, baseEnd_2450418] using wordTrace_append hprefix tailTrace_2450418
  have hstable : (prefixWord ++ tailWord_2450418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450418).length < 2 ^ (prefixWord ++ tailWord_2450418).sum := by decide
  have hdescent : baseEnd_2450418 < baseStart_2450418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450468 : List Nat := [2, 3, 1, 4, 1, 2, 2, 1, 3, 4]
def baseStart_2450468 : Nat := 118140960795 + 2450468 * 2 ^ 59
def prefixEnd_2450468 : Nat := 4983230072969 + 3 ^ 40 * 2450468 * 2
def baseEnd_2450468 : Nat := 419422637487274588793503

theorem tailTrace_2450468 : CollatzResearch.WordTrace tailWord_2450468 prefixEnd_2450468 419422637487274588793503 := by
  unfold tailWord_2450468
  simp only [CollatzResearch.WordTrace]
  refine ⟨44687955243190208730248029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59583940324253611640330705 44687955243190208730248029)
  ·
    refine ⟨16757983216196328273843011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44687955243190208730248029 16757983216196328273843011)
    ·
      refine ⟨25136974824294492410764517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16757983216196328273843011 25136974824294492410764517)
      ·
        refine ⟨4713182779555217327018347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25136974824294492410764517 4713182779555217327018347)
        ·
          refine ⟨7069774169332825990527521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4713182779555217327018347 7069774169332825990527521)
          ·
            refine ⟨5302330626999619492895641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7069774169332825990527521 5302330626999619492895641)
            ·
              refine ⟨3976747970249714619671731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5302330626999619492895641 3976747970249714619671731)
              ·
                refine ⟨5965121955374571929507597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3976747970249714619671731 5965121955374571929507597)
                ·
                  refine ⟨2236920733265464473565349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5965121955374571929507597 2236920733265464473565349)
                  ·
                    refine ⟨419422637487274588793503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2236920733265464473565349 419422637487274588793503)
                    ·
                      rfl

theorem cell23_2450468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_2450468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450468 prefixEnd_2450468 := by exact prefixLift 2450468
  have htrace : WordTrace (prefixWord ++ tailWord_2450468) baseStart_2450468 baseEnd_2450468 := by
    simpa [prefixWord, tailWord_2450468, baseEnd_2450468] using wordTrace_append hprefix tailTrace_2450468
  have hstable : (prefixWord ++ tailWord_2450468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450468).length < 2 ^ (prefixWord ++ tailWord_2450468).sum := by decide
  have hdescent : baseEnd_2450468 < baseStart_2450468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450481 : List Nat := [1, 2, 2, 3, 1, 2, 5, 1, 6]
def baseStart_2450481 : Nat := 118140960795 + 2450481 * 2 ^ 59
def prefixEnd_2450481 : Nat := 4983230072969 + 3 ^ 40 * 2450481 * 2
def baseEnd_2450481 : Nat := 139808287523370246168661

theorem tailTrace_2450481 : CollatzResearch.WordTrace tailWord_2450481 prefixEnd_2450481 139808287523370246168661 := by
  unfold tailWord_2450481
  simp only [CollatzResearch.WordTrace]
  refine ⟨89376384635333320680719297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59584256423555547120479531 89376384635333320680719297)
  ·
    refine ⟨67032288476499990510539473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89376384635333320680719297 67032288476499990510539473)
    ·
      refine ⟨50274216357374992882904605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67032288476499990510539473 50274216357374992882904605)
      ·
        refine ⟨18852831134015622331089227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50274216357374992882904605 18852831134015622331089227)
        ·
          refine ⟨28279246701023433496633841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18852831134015622331089227 28279246701023433496633841)
          ·
            refine ⟨21209435025767575122475381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28279246701023433496633841 21209435025767575122475381)
            ·
              refine ⟨1988384533665710167732067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21209435025767575122475381 1988384533665710167732067)
              ·
                refine ⟨2982576800498565251598101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1988384533665710167732067 2982576800498565251598101)
                ·
                  refine ⟨139808287523370246168661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2982576800498565251598101 139808287523370246168661)
                  ·
                    rfl

theorem cell23_2450481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 6].length) (baseStart_2450481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450481 prefixEnd_2450481 := by exact prefixLift 2450481
  have htrace : WordTrace (prefixWord ++ tailWord_2450481) baseStart_2450481 baseEnd_2450481 := by
    simpa [prefixWord, tailWord_2450481, baseEnd_2450481] using wordTrace_append hprefix tailTrace_2450481
  have hstable : (prefixWord ++ tailWord_2450481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450481).length < 2 ^ (prefixWord ++ tailWord_2450481).sum := by decide
  have hdescent : baseEnd_2450481 < baseStart_2450481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450501 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 1, 5, 2]
def baseStart_2450501 : Nat := 118140960795 + 2450501 * 2 ^ 59
def prefixEnd_2450501 : Nat := 4983230072969 + 3 ^ 40 * 2450501 * 2
def baseEnd_2450501 : Nat := 1258284857323422137267857

theorem tailTrace_2450501 : CollatzResearch.WordTrace tailWord_2450501 prefixEnd_2450501 1258284857323422137267857 := by
  unfold tailWord_2450501
  simp only [CollatzResearch.WordTrace]
  refine ⟨89377114095260864096447357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59584742730173909397631571 89377114095260864096447357)
  ·
    refine ⟨33516417785722824036167759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89377114095260864096447357 33516417785722824036167759)
    ·
      refine ⟨50274626678584236054251639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33516417785722824036167759 50274626678584236054251639)
      ·
        refine ⟨75411940017876354081377459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50274626678584236054251639 75411940017876354081377459)
        ·
          refine ⟨113117910026814531122066189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75411940017876354081377459 113117910026814531122066189)
          ·
            refine ⟨42419216260055449170774821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113117910026814531122066189 42419216260055449170774821)
            ·
              refine ⟨7953603048760396719520279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42419216260055449170774821 7953603048760396719520279)
              ·
                refine ⟨11930404573140595079280419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7953603048760396719520279 11930404573140595079280419)
                ·
                  refine ⟨17895606859710892618920629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11930404573140595079280419 17895606859710892618920629)
                  ·
                    refine ⟨1677713143097896183023809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17895606859710892618920629 1677713143097896183023809)
                    ·
                      refine ⟨1258284857323422137267857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677713143097896183023809 1258284857323422137267857)
                      ·
                        rfl

theorem cell23_2450501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 5, 2].length) (baseStart_2450501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450501 prefixEnd_2450501 := by exact prefixLift 2450501
  have htrace : WordTrace (prefixWord ++ tailWord_2450501) baseStart_2450501 baseEnd_2450501 := by
    simpa [prefixWord, tailWord_2450501, baseEnd_2450501] using wordTrace_append hprefix tailTrace_2450501
  have hstable : (prefixWord ++ tailWord_2450501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450501).length < 2 ^ (prefixWord ++ tailWord_2450501).sum := by decide
  have hdescent : baseEnd_2450501 < baseStart_2450501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450502 : List Nat := [6, 1, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_2450502 : Nat := 118140960795 + 2450502 * 2 ^ 59
def prefixEnd_2450502 : Nat := 4983230072969 + 3 ^ 40 * 2450502 * 2
def baseEnd_2450502 : Nat := 419428456934692211118451

theorem tailTrace_2450502 : CollatzResearch.WordTrace tailWord_2450502 prefixEnd_2450502 419428456934692211118451 := by
  unfold tailWord_2450502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2793035955258038789601055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 59584767045504827511489173 2793035955258038789601055)
  ·
    refine ⟨4189553932887058184401583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2793035955258038789601055 4189553932887058184401583)
    ·
      refine ⟨6284330899330587276602375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4189553932887058184401583 6284330899330587276602375)
      ·
        refine ⟨9426496348995880914903563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6284330899330587276602375 9426496348995880914903563)
        ·
          refine ⟨14139744523493821372355345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9426496348995880914903563 14139744523493821372355345)
          ·
            refine ⟨10604808392620366029266509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14139744523493821372355345 10604808392620366029266509)
            ·
              refine ⟨3976803147232637260974941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10604808392620366029266509 3976803147232637260974941)
              ·
                refine ⟨1491301180212238972865603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3976803147232637260974941 1491301180212238972865603)
                ·
                  refine ⟨2236951770318358459298405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1491301180212238972865603 2236951770318358459298405)
                  ·
                    refine ⟨419428456934692211118451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2236951770318358459298405 419428456934692211118451)
                    ·
                      rfl

theorem cell23_2450502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_2450502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450502 prefixEnd_2450502 := by exact prefixLift 2450502
  have htrace : WordTrace (prefixWord ++ tailWord_2450502) baseStart_2450502 baseEnd_2450502 := by
    simpa [prefixWord, tailWord_2450502, baseEnd_2450502] using wordTrace_append hprefix tailTrace_2450502
  have hstable : (prefixWord ++ tailWord_2450502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450502).length < 2 ^ (prefixWord ++ tailWord_2450502).sum := by decide
  have hdescent : baseEnd_2450502 < baseStart_2450502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450544 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 6]
def baseStart_2450544 : Nat := 118140960795 + 2450544 * 2 ^ 59
def prefixEnd_2450544 : Nat := 4983230072969 + 3 ^ 40 * 2450544 * 2
def baseEnd_2450544 : Nat := 1258306936991565469030159

theorem tailTrace_2450544 : CollatzResearch.WordTrace tailWord_2450544 prefixEnd_2450544 1258306936991565469030159 := by
  unfold tailWord_2450544
  simp only [CollatzResearch.WordTrace]
  refine ⟨44689341217052541220131343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59585788289403388293508457 44689341217052541220131343)
  ·
    refine ⟨67034011825578811830197015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44689341217052541220131343 67034011825578811830197015)
    ·
      refine ⟨100551017738368217745295523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67034011825578811830197015 100551017738368217745295523)
      ·
        refine ⟨150826526607552326617943285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100551017738368217745295523 150826526607552326617943285)
        ·
          refine ⟨14139986869458030620432183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 150826526607552326617943285 14139986869458030620432183)
          ·
            refine ⟨21209980304187045930648275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14139986869458030620432183 21209980304187045930648275)
            ·
              refine ⟨31814970456280568895972413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21209980304187045930648275 31814970456280568895972413)
              ·
                refine ⟨11930613921105213335989655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31814970456280568895972413 11930613921105213335989655)
                ·
                  refine ⟨17895920881657820003984483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11930613921105213335989655 17895920881657820003984483)
                  ·
                    refine ⟨26843881322486730005976725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17895920881657820003984483 26843881322486730005976725)
                    ·
                      refine ⟨1258306936991565469030159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26843881322486730005976725 1258306936991565469030159)
                      ·
                        rfl

theorem cell23_2450544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_2450544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450544 prefixEnd_2450544 := by exact prefixLift 2450544
  have htrace : WordTrace (prefixWord ++ tailWord_2450544) baseStart_2450544 baseEnd_2450544 := by
    simpa [prefixWord, tailWord_2450544, baseEnd_2450544] using wordTrace_append hprefix tailTrace_2450544
  have hstable : (prefixWord ++ tailWord_2450544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450544).length < 2 ^ (prefixWord ++ tailWord_2450544).sum := by decide
  have hdescent : baseEnd_2450544 < baseStart_2450544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450551 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 3]
def baseStart_2450551 : Nat := 118140960795 + 2450551 * 2 ^ 59
def prefixEnd_2450551 : Nat := 4983230072969 + 3 ^ 40 * 2450551 * 2
def baseEnd_2450551 : Nat := 1258310531356146941642627

theorem tailTrace_2450551 : CollatzResearch.WordTrace tailWord_2450551 prefixEnd_2450551 1258310531356146941642627 := by
  unfold tailWord_2450551
  simp only [CollatzResearch.WordTrace]
  refine ⟨89378937745079722635767507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59585958496719815090511671 89378937745079722635767507)
  ·
    refine ⟨134068406617619583953651261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89378937745079722635767507 134068406617619583953651261)
    ·
      refine ⟨50275652481607343982619223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134068406617619583953651261 50275652481607343982619223)
      ·
        refine ⟨75413478722411015973928835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50275652481607343982619223 75413478722411015973928835)
        ·
          refine ⟨113120218083616523960893253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75413478722411015973928835 113120218083616523960893253)
          ·
            refine ⟨21210040890678098242667485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113120218083616523960893253 21210040890678098242667485)
            ·
              refine ⟨7953765334004286841000307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21210040890678098242667485 7953765334004286841000307)
              ·
                refine ⟨11930648001006430261500461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7953765334004286841000307 11930648001006430261500461)
                ·
                  refine ⟨4473993000377411348062673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11930648001006430261500461 4473993000377411348062673)
                  ·
                    refine ⟨3355494750283058511047005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4473993000377411348062673 3355494750283058511047005)
                    ·
                      refine ⟨1258310531356146941642627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3355494750283058511047005 1258310531356146941642627)
                      ·
                        rfl

theorem cell23_2450551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_2450551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450551 prefixEnd_2450551 := by exact prefixLift 2450551
  have htrace : WordTrace (prefixWord ++ tailWord_2450551) baseStart_2450551 baseEnd_2450551 := by
    simpa [prefixWord, tailWord_2450551, baseEnd_2450551] using wordTrace_append hprefix tailTrace_2450551
  have hstable : (prefixWord ++ tailWord_2450551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450551).length < 2 ^ (prefixWord ++ tailWord_2450551).sum := by decide
  have hdescent : baseEnd_2450551 < baseStart_2450551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450561 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_2450561 : Nat := 118140960795 + 2450561 * 2 ^ 59
def prefixEnd_2450561 : Nat := 4983230072969 + 3 ^ 40 * 2450561 * 2
def baseEnd_2450561 : Nat := 1258315666162691902517581

theorem tailTrace_2450561 : CollatzResearch.WordTrace tailWord_2450561 prefixEnd_2450561 1258315666162691902517581 := by
  unfold tailWord_2450561
  simp only [CollatzResearch.WordTrace]
  refine ⟨89379302475043494343631537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59586201650028996229087691 89379302475043494343631537)
  ·
    refine ⟨67034476856282620757723653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89379302475043494343631537 67034476856282620757723653)
    ·
      refine ⟨12568964410552991392073185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67034476856282620757723653 12568964410552991392073185)
      ·
        refine ⟨9426723307914743544054889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12568964410552991392073185 9426723307914743544054889)
        ·
          refine ⟨7070042480936057658041167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9426723307914743544054889 7070042480936057658041167)
          ·
            refine ⟨10605063721404086487061751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7070042480936057658041167 10605063721404086487061751)
            ·
              refine ⟨15907595582106129730592627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10605063721404086487061751 15907595582106129730592627)
              ·
                refine ⟨23861393373159194595888941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15907595582106129730592627 23861393373159194595888941)
                ·
                  refine ⟨8948022514934697973458353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23861393373159194595888941 8948022514934697973458353)
                  ·
                    refine ⟨6711016886201023480093765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8948022514934697973458353 6711016886201023480093765)
                    ·
                      refine ⟨1258315666162691902517581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6711016886201023480093765 1258315666162691902517581)
                      ·
                        rfl

theorem cell23_2450561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_2450561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450561 prefixEnd_2450561 := by exact prefixLift 2450561
  have htrace : WordTrace (prefixWord ++ tailWord_2450561) baseStart_2450561 baseEnd_2450561 := by
    simpa [prefixWord, tailWord_2450561, baseEnd_2450561] using wordTrace_append hprefix tailTrace_2450561
  have hstable : (prefixWord ++ tailWord_2450561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450561).length < 2 ^ (prefixWord ++ tailWord_2450561).sum := by decide
  have hdescent : baseEnd_2450561 < baseStart_2450561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450565 : List Nat := [1, 3, 1, 1, 6, 1, 3, 1, 1, 1, 4]
def baseStart_2450565 : Nat := 118140960795 + 2450565 * 2 ^ 59
def prefixEnd_2450565 : Nat := 4983230072969 + 3 ^ 40 * 2450565 * 2
def baseEnd_2450565 : Nat := 1258317720085309886867563

theorem tailTrace_2450565 : CollatzResearch.WordTrace tailWord_2450565 prefixEnd_2450565 1258317720085309886867563 := by
  unfold tailWord_2450565
  simp only [CollatzResearch.WordTrace]
  refine ⟨89379448367029003026777149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59586298911352668684518099 89379448367029003026777149)
  ·
    refine ⟨33517293137635876135041431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89379448367029003026777149 33517293137635876135041431)
    ·
      refine ⟨50275939706453814202562147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33517293137635876135041431 50275939706453814202562147)
      ·
        refine ⟨75413909559680721303843221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50275939706453814202562147 75413909559680721303843221)
        ·
          refine ⟨3535027010610033811117651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 75413909559680721303843221 3535027010610033811117651)
          ·
            refine ⟨5302540515915050716676477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3535027010610033811117651 5302540515915050716676477)
            ·
              refine ⟨1988452693468144018753679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5302540515915050716676477 1988452693468144018753679)
              ·
                refine ⟨2982679040202216028130519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1988452693468144018753679 2982679040202216028130519)
                ·
                  refine ⟨4474018560303324042195779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2982679040202216028130519 4474018560303324042195779)
                  ·
                    refine ⟨6711027840454986063293669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4474018560303324042195779 6711027840454986063293669)
                    ·
                      refine ⟨1258317720085309886867563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6711027840454986063293669 1258317720085309886867563)
                      ·
                        rfl

theorem cell23_2450565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 1, 1, 1, 4].length) (baseStart_2450565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450565 prefixEnd_2450565 := by exact prefixLift 2450565
  have htrace : WordTrace (prefixWord ++ tailWord_2450565) baseStart_2450565 baseEnd_2450565 := by
    simpa [prefixWord, tailWord_2450565, baseEnd_2450565] using wordTrace_append hprefix tailTrace_2450565
  have hstable : (prefixWord ++ tailWord_2450565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450565).length < 2 ^ (prefixWord ++ tailWord_2450565).sum := by decide
  have hdescent : baseEnd_2450565 < baseStart_2450565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450626 : List Nat := [3, 5, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_2450626 : Nat := 118140960795 + 2450626 * 2 ^ 59
def prefixEnd_2450626 : Nat := 4983230072969 + 3 ^ 40 * 2450626 * 2
def baseEnd_2450626 : Nat := 419449680801744716068261

theorem tailTrace_2450626 : CollatzResearch.WordTrace tailWord_2450626 prefixEnd_2450626 419449680801744716068261 := by
  unfold tailWord_2450626
  simp only [CollatzResearch.WordTrace]
  refine ⟨22345418304952002611186933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59587782146538673629831821 22345418304952002611186933)
  ·
    refine ⟨2094882966089250244798775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22345418304952002611186933 2094882966089250244798775)
    ·
      refine ⟨3142324449133875367198163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2094882966089250244798775 3142324449133875367198163)
      ·
        refine ⟨4713486673700813050797245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3142324449133875367198163 4713486673700813050797245)
        ·
          refine ⟨1767557502637804894048967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4713486673700813050797245 1767557502637804894048967)
          ·
            refine ⟨2651336253956707341073451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1767557502637804894048967 2651336253956707341073451)
            ·
              refine ⟨3977004380935061011610177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2651336253956707341073451 3977004380935061011610177)
              ·
                refine ⟨2982753285701295758707633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3977004380935061011610177 2982753285701295758707633)
                ·
                  refine ⟨2237064964275971819030725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2982753285701295758707633 2237064964275971819030725)
                  ·
                    refine ⟨419449680801744716068261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2237064964275971819030725 419449680801744716068261)
                    ·
                      rfl

theorem cell23_2450626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_2450626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450626 prefixEnd_2450626 := by exact prefixLift 2450626
  have htrace : WordTrace (prefixWord ++ tailWord_2450626) baseStart_2450626 baseEnd_2450626 := by
    simpa [prefixWord, tailWord_2450626, baseEnd_2450626] using wordTrace_append hprefix tailTrace_2450626
  have hstable : (prefixWord ++ tailWord_2450626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450626).length < 2 ^ (prefixWord ++ tailWord_2450626).sum := by decide
  have hdescent : baseEnd_2450626 < baseStart_2450626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450655 : List Nat := [1, 1, 2, 3, 2, 1, 2, 5, 2, 2, 2]
def baseStart_2450655 : Nat := 118140960795 + 2450655 * 2 ^ 59
def prefixEnd_2450655 : Nat := 4983230072969 + 3 ^ 40 * 2450655 * 2
def baseEnd_2450655 : Nat := 1258363933344214534742149

theorem tailTrace_2450655 : CollatzResearch.WordTrace tailWord_2450655 prefixEnd_2450655 1258363933344214534742149 := by
  unfold tailWord_2450655
  simp only [CollatzResearch.WordTrace]
  refine ⟨89382730936702948397553419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59588487291135298931702279 89382730936702948397553419)
  ·
    refine ⟨134074096405054422596330129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89382730936702948397553419 134074096405054422596330129)
    ·
      refine ⟨100555572303790816947247597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134074096405054422596330129 100555572303790816947247597)
      ·
        refine ⟨37708339613921556355217849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100555572303790816947247597 37708339613921556355217849)
        ·
          refine ⟨28281254710441167266413387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37708339613921556355217849 28281254710441167266413387)
          ·
            refine ⟨42421882065661750899620081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28281254710441167266413387 42421882065661750899620081)
            ·
              refine ⟨31816411549246313174715061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42421882065661750899620081 31816411549246313174715061)
              ·
                refine ⟨2982788582741841860129537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31816411549246313174715061 2982788582741841860129537)
                ·
                  refine ⟨2237091437056381395097153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2982788582741841860129537 2237091437056381395097153)
                  ·
                    refine ⟨1677818577792286046322865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2237091437056381395097153 1677818577792286046322865)
                    ·
                      refine ⟨1258363933344214534742149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677818577792286046322865 1258363933344214534742149)
                      ·
                        rfl

theorem cell23_2450655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_2450655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450655 prefixEnd_2450655 := by exact prefixLift 2450655
  have htrace : WordTrace (prefixWord ++ tailWord_2450655) baseStart_2450655 baseEnd_2450655 := by
    simpa [prefixWord, tailWord_2450655, baseEnd_2450655] using wordTrace_append hprefix tailTrace_2450655
  have hstable : (prefixWord ++ tailWord_2450655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450655).length < 2 ^ (prefixWord ++ tailWord_2450655).sum := by decide
  have hdescent : baseEnd_2450655 < baseStart_2450655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450691 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 4, 5]
def baseStart_2450691 : Nat := 118140960795 + 2450691 * 2 ^ 59
def prefixEnd_2450691 : Nat := 4983230072969 + 3 ^ 40 * 2450691 * 2
def baseEnd_2450691 : Nat := 419460806215925464630661

theorem tailTrace_2450691 : CollatzResearch.WordTrace tailWord_2450691 prefixEnd_2450691 419460806215925464630661 := by
  unfold tailWord_2450691
  simp only [CollatzResearch.WordTrace]
  refine ⟨89384043964572526545863927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59589362643048351030575951 89384043964572526545863927)
  ·
    refine ⟨134076065946858789818795891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89384043964572526545863927 134076065946858789818795891)
    ·
      refine ⟨201114098920288184728193837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134076065946858789818795891 201114098920288184728193837)
      ·
        refine ⟨75417787095108069273072689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201114098920288184728193837 75417787095108069273072689)
        ·
          refine ⟨56563340321331051954804517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75417787095108069273072689 56563340321331051954804517)
          ·
            refine ⟨10605626310249572241525847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56563340321331051954804517 10605626310249572241525847)
            ·
              refine ⟨15908439465374358362288771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10605626310249572241525847 15908439465374358362288771)
              ·
                refine ⟨23862659198061537543433157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15908439465374358362288771 23862659198061537543433157)
                ·
                  refine ⟨4474248599636538289393717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23862659198061537543433157 4474248599636538289393717)
                  ·
                    refine ⟨419460806215925464630661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4474248599636538289393717 419460806215925464630661)
                    ·
                      rfl

theorem cell23_2450691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 5].length) (baseStart_2450691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450691 prefixEnd_2450691 := by exact prefixLift 2450691
  have htrace : WordTrace (prefixWord ++ tailWord_2450691) baseStart_2450691 baseEnd_2450691 := by
    simpa [prefixWord, tailWord_2450691, baseEnd_2450691] using wordTrace_append hprefix tailTrace_2450691
  have hstable : (prefixWord ++ tailWord_2450691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450691).length < 2 ^ (prefixWord ++ tailWord_2450691).sum := by decide
  have hdescent : baseEnd_2450691 < baseStart_2450691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450698 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2]
def baseStart_2450698 : Nat := 118140960795 + 2450698 * 2 ^ 59
def prefixEnd_2450698 : Nat := 4983230072969 + 3 ^ 40 * 2450698 * 2
def baseEnd_2450698 : Nat := 1258386013012357866504451

theorem tailTrace_2450698 : CollatzResearch.WordTrace tailWord_2450698 prefixEnd_2450698 1258386013012357866504451 := by
  unfold tailWord_2450698
  simp only [CollatzResearch.WordTrace]
  refine ⟨22346074818886791685342187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59589532850364777827579165 22346074818886791685342187)
  ·
    refine ⟨33519112228330187528013281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22346074818886791685342187 33519112228330187528013281)
    ·
      refine ⟨25139334171247640646009961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33519112228330187528013281 25139334171247640646009961)
      ·
        refine ⟨18854500628435730484507471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25139334171247640646009961 18854500628435730484507471)
        ·
          refine ⟨28281750942653595726761207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18854500628435730484507471 28281750942653595726761207)
          ·
            refine ⟨42422626413980393590141811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28281750942653595726761207 42422626413980393590141811)
            ·
              refine ⟨63633939620970590385212717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42422626413980393590141811 63633939620970590385212717)
              ·
                refine ⟨23862727357863971394454769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63633939620970590385212717 23862727357863971394454769)
                ·
                  refine ⟨17897045518397978545841077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23862727357863971394454769 17897045518397978545841077)
                  ·
                    refine ⟨1677848017349810488672601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17897045518397978545841077 1677848017349810488672601)
                    ·
                      refine ⟨1258386013012357866504451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677848017349810488672601 1258386013012357866504451)
                      ·
                        rfl

theorem cell23_2450698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_2450698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450698 prefixEnd_2450698 := by exact prefixLift 2450698
  have htrace : WordTrace (prefixWord ++ tailWord_2450698) baseStart_2450698 baseEnd_2450698 := by
    simpa [prefixWord, tailWord_2450698, baseEnd_2450698] using wordTrace_append hprefix tailTrace_2450698
  have hstable : (prefixWord ++ tailWord_2450698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450698).length < 2 ^ (prefixWord ++ tailWord_2450698).sum := by decide
  have hdescent : baseEnd_2450698 < baseStart_2450698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450706 : List Nat := [3, 2, 4, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_2450706 : Nat := 118140960795 + 2450706 * 2 ^ 59
def prefixEnd_2450706 : Nat := 4983230072969 + 3 ^ 40 * 2450706 * 2
def baseEnd_2450706 : Nat := 1258390120857593835204415

theorem tailTrace_2450706 : CollatzResearch.WordTrace tailWord_2450706 prefixEnd_2450706 1258390120857593835204415 := by
  unfold tailWord_2450706
  simp only [CollatzResearch.WordTrace]
  refine ⟨22346147764879546026914993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59589727373012122738439981 22346147764879546026914993)
  ·
    refine ⟨16759610823659659520186245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22346147764879546026914993 16759610823659659520186245)
    ·
      refine ⟨3142427029436186160034921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16759610823659659520186245 3142427029436186160034921)
      ·
        refine ⟨2356820272077139620026191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3142427029436186160034921 2356820272077139620026191)
        ·
          refine ⟨3535230408115709430039287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2356820272077139620026191 3535230408115709430039287)
          ·
            refine ⟨5302845612173564145058931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3535230408115709430039287 5302845612173564145058931)
            ·
              refine ⟨7954268418260346217588397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5302845612173564145058931 7954268418260346217588397)
              ·
                refine ⟨2982850656847629831595649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7954268418260346217588397 2982850656847629831595649)
                ·
                  refine ⟨2237137992635722373696737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2982850656847629831595649 2237137992635722373696737)
                  ·
                    refine ⟨1677853494476791780272553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2237137992635722373696737 1677853494476791780272553)
                    ·
                      refine ⟨1258390120857593835204415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677853494476791780272553 1258390120857593835204415)
                      ·
                        rfl

theorem cell23_2450706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_2450706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450706 prefixEnd_2450706 := by exact prefixLift 2450706
  have htrace : WordTrace (prefixWord ++ tailWord_2450706) baseStart_2450706 baseEnd_2450706 := by
    simpa [prefixWord, tailWord_2450706, baseEnd_2450706] using wordTrace_append hprefix tailTrace_2450706
  have hstable : (prefixWord ++ tailWord_2450706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450706).length < 2 ^ (prefixWord ++ tailWord_2450706).sum := by decide
  have hdescent : baseEnd_2450706 < baseStart_2450706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450812 : List Nat := [2, 2, 2, 1, 1, 1, 3, 6, 1, 1, 3]
def baseStart_2450812 : Nat := 118140960795 + 2450812 * 2 ^ 59
def prefixEnd_2450812 : Nat := 4983230072969 + 3 ^ 40 * 2450812 * 2
def baseEnd_2450812 : Nat := 1258444549806970420478927

theorem tailTrace_2450812 : CollatzResearch.WordTrace tailWord_2450812 prefixEnd_2450812 1258444549806970420478927 := by
  unfold tailWord_2450812
  simp only [CollatzResearch.WordTrace]
  refine ⟨44694228598567082105509345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59592304798089442807345793 44694228598567082105509345)
  ·
    refine ⟨33520671448925311579132009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44694228598567082105509345 33520671448925311579132009)
    ·
      refine ⟨25140503586693983684349007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33520671448925311579132009 25140503586693983684349007)
      ·
        refine ⟨37710755380040975526523511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25140503586693983684349007 37710755380040975526523511)
        ·
          refine ⟨56566133070061463289785267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37710755380040975526523511 56566133070061463289785267)
          ·
            refine ⟨84849199605092194934677901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56566133070061463289785267 84849199605092194934677901)
            ·
              refine ⟨31818449851909573100504213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84849199605092194934677901 31818449851909573100504213)
              ·
                refine ⟨1491489836808261239086135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31818449851909573100504213 1491489836808261239086135)
                ·
                  refine ⟨2237234755212391858629203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1491489836808261239086135 2237234755212391858629203)
                  ·
                    refine ⟨3355852132818587787943805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2237234755212391858629203 3355852132818587787943805)
                    ·
                      refine ⟨1258444549806970420478927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3355852132818587787943805 1258444549806970420478927)
                      ·
                        rfl

theorem cell23_2450812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 1, 1, 3].length) (baseStart_2450812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450812 prefixEnd_2450812 := by exact prefixLift 2450812
  have htrace : WordTrace (prefixWord ++ tailWord_2450812) baseStart_2450812 baseEnd_2450812 := by
    simpa [prefixWord, tailWord_2450812, baseEnd_2450812] using wordTrace_append hprefix tailTrace_2450812
  have hstable : (prefixWord ++ tailWord_2450812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450812).length < 2 ^ (prefixWord ++ tailWord_2450812).sum := by decide
  have hdescent : baseEnd_2450812 < baseStart_2450812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450845 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 4, 4]
def baseStart_2450845 : Nat := 118140960795 + 2450845 * 2 ^ 59
def prefixEnd_2450845 : Nat := 4983230072969 + 3 ^ 40 * 2450845 * 2
def baseEnd_2450845 : Nat := 419487164889522930455425

theorem tailTrace_2450845 : CollatzResearch.WordTrace tailWord_2450845 prefixEnd_2450845 419487164889522930455425 := by
  unfold tailWord_2450845
  simp only [CollatzResearch.WordTrace]
  refine ⟨89389660806014610846969989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59593107204009740564646659 89389660806014610846969989)
  ·
    refine ⟨16760561401127739533806873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89389660806014610846969989 16760561401127739533806873)
    ·
      refine ⟨12570421050845804650355155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16760561401127739533806873 12570421050845804650355155)
      ·
        refine ⟨18855631576268706975532733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12570421050845804650355155 18855631576268706975532733)
        ·
          refine ⟨7070861841100765115824775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18855631576268706975532733 7070861841100765115824775)
          ·
            refine ⟨10606292761651147673737163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7070861841100765115824775 10606292761651147673737163)
            ·
              refine ⟨15909439142476721510605745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10606292761651147673737163 15909439142476721510605745)
              ·
                refine ⟨11932079356857541132954309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15909439142476721510605745 11932079356857541132954309)
                ·
                  refine ⟨2237264879410788962428933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11932079356857541132954309 2237264879410788962428933)
                  ·
                    refine ⟨419487164889522930455425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2237264879410788962428933 419487164889522930455425)
                    ·
                      rfl

theorem cell23_2450845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_2450845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450845 prefixEnd_2450845 := by exact prefixLift 2450845
  have htrace : WordTrace (prefixWord ++ tailWord_2450845) baseStart_2450845 baseEnd_2450845 := by
    simpa [prefixWord, tailWord_2450845, baseEnd_2450845] using wordTrace_append hprefix tailTrace_2450845
  have hstable : (prefixWord ++ tailWord_2450845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450845).length < 2 ^ (prefixWord ++ tailWord_2450845).sum := by decide
  have hdescent : baseEnd_2450845 < baseStart_2450845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450848 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 4]
def baseStart_2450848 : Nat := 118140960795 + 2450848 * 2 ^ 59
def prefixEnd_2450848 : Nat := 4983230072969 + 3 ^ 40 * 2450848 * 2
def baseEnd_2450848 : Nat := 1258463035110532279628761

theorem tailTrace_2450848 : CollatzResearch.WordTrace tailWord_2450848 prefixEnd_2450848 1258463035110532279628761 := by
  unfold tailWord_2450848
  simp only [CollatzResearch.WordTrace]
  refine ⟨44694885112501871179664599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59593180150002494906219465 44694885112501871179664599)
  ·
    refine ⟨67042327668752806769496899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44694885112501871179664599 67042327668752806769496899)
    ·
      refine ⟨100563491503129210154245349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67042327668752806769496899 100563491503129210154245349)
      ·
        refine ⟨18855654656836726903921003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100563491503129210154245349 18855654656836726903921003)
        ·
          refine ⟨28283481985255090355881505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18855654656836726903921003 28283481985255090355881505)
          ·
            refine ⟨21212611488941317766911129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28283481985255090355881505 21212611488941317766911129)
            ·
              refine ⟨15909458616705988325183347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21212611488941317766911129 15909458616705988325183347)
              ·
                refine ⟨23864187925058982487775021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15909458616705988325183347 23864187925058982487775021)
                ·
                  refine ⟨8949070471897118432915633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23864187925058982487775021 8949070471897118432915633)
                  ·
                    refine ⟨6711802853922838824686725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8949070471897118432915633 6711802853922838824686725)
                    ·
                      refine ⟨1258463035110532279628761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6711802853922838824686725 1258463035110532279628761)
                      ·
                        rfl

theorem cell23_2450848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_2450848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450848 prefixEnd_2450848 := by exact prefixLift 2450848
  have htrace : WordTrace (prefixWord ++ tailWord_2450848) baseStart_2450848 baseEnd_2450848 := by
    simpa [prefixWord, tailWord_2450848, baseEnd_2450848] using wordTrace_append hprefix tailTrace_2450848
  have hstable : (prefixWord ++ tailWord_2450848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450848).length < 2 ^ (prefixWord ++ tailWord_2450848).sum := by decide
  have hdescent : baseEnd_2450848 < baseStart_2450848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450855 : List Nat := [1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_2450855 : Nat := 118140960795 + 2450855 * 2 ^ 59
def prefixEnd_2450855 : Nat := 4983230072969 + 3 ^ 40 * 2450855 * 2
def baseEnd_2450855 : Nat := 1258466629475113752241229

theorem tailTrace_2450855 : CollatzResearch.WordTrace tailWord_2450855 prefixEnd_2450855 1258466629475113752241229 := by
  unfold tailWord_2450855
  simp only [CollatzResearch.WordTrace]
  refine ⟨89390025535978382554834019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59593350357318921703222679 89390025535978382554834019)
  ·
    refine ⟨134085038303967573832251029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89390025535978382554834019 134085038303967573832251029)
    ·
      refine ⟨6285236170498480023386767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 134085038303967573832251029 6285236170498480023386767)
      ·
        refine ⟨9427854255747720035080151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6285236170498480023386767 9427854255747720035080151)
        ·
          refine ⟨14141781383621580052620227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9427854255747720035080151 14141781383621580052620227)
          ·
            refine ⟨21212672075432370078930341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14141781383621580052620227 21212672075432370078930341)
            ·
              refine ⟨3977376014143569389799439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21212672075432370078930341 3977376014143569389799439)
              ·
                refine ⟨5966064021215354084699159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3977376014143569389799439 5966064021215354084699159)
                ·
                  refine ⟨8949096031823031127048739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5966064021215354084699159 8949096031823031127048739)
                  ·
                    refine ⟨13423644047734546690573109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8949096031823031127048739 13423644047734546690573109)
                    ·
                      refine ⟨1258466629475113752241229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13423644047734546690573109 1258466629475113752241229)
                      ·
                        rfl

theorem cell23_2450855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_2450855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450855 prefixEnd_2450855 := by exact prefixLift 2450855
  have htrace : WordTrace (prefixWord ++ tailWord_2450855) baseStart_2450855 baseEnd_2450855 := by
    simpa [prefixWord, tailWord_2450855, baseEnd_2450855] using wordTrace_append hprefix tailTrace_2450855
  have hstable : (prefixWord ++ tailWord_2450855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450855).length < 2 ^ (prefixWord ++ tailWord_2450855).sum := by decide
  have hdescent : baseEnd_2450855 < baseStart_2450855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450869 : List Nat := [1, 3, 3, 2, 2, 1, 3, 1, 3, 2, 2]
def baseStart_2450869 : Nat := 118140960795 + 2450869 * 2 ^ 59
def prefixEnd_2450869 : Nat := 4983230072969 + 3 ^ 40 * 2450869 * 2
def baseEnd_2450869 : Nat := 1258473818204276697466165

theorem tailTrace_2450869 : CollatzResearch.WordTrace tailWord_2450869 prefixEnd_2450869 1258473818204276697466165 := by
  unfold tailWord_2450869
  simp only [CollatzResearch.WordTrace]
  refine ⟨89390536157927662945843661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59593690771951775297229107 89390536157927662945843661)
  ·
    refine ⟨33521451059222873604691373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89390536157927662945843661 33521451059222873604691373)
    ·
      refine ⟨12570544147208577601759265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33521451059222873604691373 12570544147208577601759265)
      ·
        refine ⟨9427908110406433201319449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12570544147208577601759265 9427908110406433201319449)
        ·
          refine ⟨7070931082804824900989587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9427908110406433201319449 7070931082804824900989587)
          ·
            refine ⟨10606396624207237351484381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7070931082804824900989587 10606396624207237351484381)
            ·
              refine ⟨3977398734077714006806643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10606396624207237351484381 3977398734077714006806643)
              ·
                refine ⟨5966098101116571010209965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3977398734077714006806643 5966098101116571010209965)
                ·
                  refine ⟨2237286787918714128828737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5966098101116571010209965 2237286787918714128828737)
                  ·
                    refine ⟨1677965090939035596621553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2237286787918714128828737 1677965090939035596621553)
                    ·
                      refine ⟨1258473818204276697466165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1677965090939035596621553 1258473818204276697466165)
                      ·
                        rfl

theorem cell23_2450869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_2450869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450869 prefixEnd_2450869 := by exact prefixLift 2450869
  have htrace : WordTrace (prefixWord ++ tailWord_2450869) baseStart_2450869 baseEnd_2450869 := by
    simpa [prefixWord, tailWord_2450869, baseEnd_2450869] using wordTrace_append hprefix tailTrace_2450869
  have hstable : (prefixWord ++ tailWord_2450869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450869).length < 2 ^ (prefixWord ++ tailWord_2450869).sum := by decide
  have hdescent : baseEnd_2450869 < baseStart_2450869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450878 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_2450878 : Nat := 118140960795 + 2450878 * 2 ^ 59
def prefixEnd_2450878 : Nat := 4983230072969 + 3 ^ 40 * 2450878 * 2
def baseEnd_2450878 : Nat := 1258478439530167162253623

theorem tailTrace_2450878 : CollatzResearch.WordTrace tailWord_2450878 prefixEnd_2450878 1258478439530167162253623 := by
  unfold tailWord_2450878
  simp only [CollatzResearch.WordTrace]
  refine ⟨11173858051861882185365161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59593909609930038321947525 11173858051861882185365161)
  ·
    refine ⟨8380393538896411639023871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11173858051861882185365161 8380393538896411639023871)
    ·
      refine ⟨12570590308344617458535807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8380393538896411639023871 12570590308344617458535807)
      ·
        refine ⟨18855885462516926187803711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12570590308344617458535807 18855885462516926187803711)
        ·
          refine ⟨28283828193775389281705567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18855885462516926187803711 28283828193775389281705567)
          ·
            refine ⟨42425742290663083922558351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28283828193775389281705567 42425742290663083922558351)
            ·
              refine ⟨63638613435994625883837527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42425742290663083922558351 63638613435994625883837527)
              ·
                refine ⟨95457920153991938825756291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63638613435994625883837527 95457920153991938825756291)
                ·
                  refine ⟨143186880230987908238634437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95457920153991938825756291 143186880230987908238634437)
                  ·
                    refine ⟨26847540043310232794743957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 143186880230987908238634437 26847540043310232794743957)
                    ·
                      refine ⟨1258478439530167162253623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26847540043310232794743957 1258478439530167162253623)
                      ·
                        rfl

theorem cell23_2450878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_2450878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450878 prefixEnd_2450878 := by exact prefixLift 2450878
  have htrace : WordTrace (prefixWord ++ tailWord_2450878) baseStart_2450878 baseEnd_2450878 := by
    simpa [prefixWord, tailWord_2450878, baseEnd_2450878] using wordTrace_append hprefix tailTrace_2450878
  have hstable : (prefixWord ++ tailWord_2450878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450878).length < 2 ^ (prefixWord ++ tailWord_2450878).sum := by decide
  have hdescent : baseEnd_2450878 < baseStart_2450878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450902 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_2450902 : Nat := 118140960795 + 2450902 * 2 ^ 59
def prefixEnd_2450902 : Nat := 4983230072969 + 3 ^ 40 * 2450902 * 2
def baseEnd_2450902 : Nat := 1258490763065875068353513

theorem tailTrace_2450902 : CollatzResearch.WordTrace tailWord_2450902 prefixEnd_2450902 1258490763065875068353513 := by
  unfold tailWord_2450902
  simp only [CollatzResearch.WordTrace]
  refine ⟨5586983735425506848862185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59594493177872073054529973 5586983735425506848862185)
  ·
    refine ⟨4190237801569130136646639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5586983735425506848862185 4190237801569130136646639)
    ·
      refine ⟨6285356702353695204969959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4190237801569130136646639 6285356702353695204969959)
      ·
        refine ⟨9428035053530542807454939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6285356702353695204969959 9428035053530542807454939)
        ·
          refine ⟨14142052580295814211182409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9428035053530542807454939 14142052580295814211182409)
          ·
            refine ⟨10606539435221860658386807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14142052580295814211182409 10606539435221860658386807)
            ·
              refine ⟨15909809152832790987580211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10606539435221860658386807 15909809152832790987580211)
              ·
                refine ⟨23864713729249186481370317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15909809152832790987580211 23864713729249186481370317)
                ·
                  refine ⟨8949267648468444930513869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23864713729249186481370317 8949267648468444930513869)
                  ·
                    refine ⟨3355975368175666848942701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8949267648468444930513869 3355975368175666848942701)
                    ·
                      refine ⟨1258490763065875068353513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3355975368175666848942701 1258490763065875068353513)
                      ·
                        rfl

theorem cell23_2450902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_2450902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450902 prefixEnd_2450902 := by exact prefixLift 2450902
  have htrace : WordTrace (prefixWord ++ tailWord_2450902) baseStart_2450902 baseEnd_2450902 := by
    simpa [prefixWord, tailWord_2450902, baseEnd_2450902] using wordTrace_append hprefix tailTrace_2450902
  have hstable : (prefixWord ++ tailWord_2450902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450902).length < 2 ^ (prefixWord ++ tailWord_2450902).sum := by decide
  have hdescent : baseEnd_2450902 < baseStart_2450902 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450919 : List Nat := [1, 1, 5, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_2450919 : Nat := 118140960795 + 2450919 * 2 ^ 59
def prefixEnd_2450919 : Nat := 4983230072969 + 3 ^ 40 * 2450919 * 2
def baseEnd_2450919 : Nat := 1258499492237001501840935

theorem tailTrace_2450919 : CollatzResearch.WordTrace tailWord_2450919 prefixEnd_2450919 1258499492237001501840935 := by
  unfold tailWord_2450919
  simp only [CollatzResearch.WordTrace]
  refine ⟨89392359807746521485163811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59594906538497680990109207 89392359807746521485163811)
  ·
    refine ⟨134088539711619782227745717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89392359807746521485163811 134088539711619782227745717)
    ·
      refine ⟨12570800597964354583851161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134088539711619782227745717 12570800597964354583851161)
      ·
        refine ⟨9428100448473265937888371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12570800597964354583851161 9428100448473265937888371)
        ·
          refine ⟨14142150672709898906832557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9428100448473265937888371 14142150672709898906832557)
          ·
            refine ⟨5303306502266212090062209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14142150672709898906832557 5303306502266212090062209)
            ·
              refine ⟨3977479876699659067546657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5303306502266212090062209 3977479876699659067546657)
              ·
                refine ⟨2983109907524744300659993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3977479876699659067546657 2983109907524744300659993)
                ·
                  refine ⟨2237332430643558225494995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2983109907524744300659993 2237332430643558225494995)
                  ·
                    refine ⟨3355998645965337338242493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2237332430643558225494995 3355998645965337338242493)
                    ·
                      refine ⟨1258499492237001501840935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3355998645965337338242493 1258499492237001501840935)
                      ·
                        rfl

theorem cell23_2450919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_2450919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450919 prefixEnd_2450919 := by exact prefixLift 2450919
  have htrace : WordTrace (prefixWord ++ tailWord_2450919) baseStart_2450919 baseEnd_2450919 := by
    simpa [prefixWord, tailWord_2450919, baseEnd_2450919] using wordTrace_append hprefix tailTrace_2450919
  have hstable : (prefixWord ++ tailWord_2450919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450919).length < 2 ^ (prefixWord ++ tailWord_2450919).sum := by decide
  have hdescent : baseEnd_2450919 < baseStart_2450919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450975 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 3]
def baseStart_2450975 : Nat := 118140960795 + 2450975 * 2 ^ 59
def prefixEnd_2450975 : Nat := 4983230072969 + 3 ^ 40 * 2450975 * 2
def baseEnd_2450975 : Nat := 1258528247153653282740677

theorem tailTrace_2450975 : CollatzResearch.WordTrace tailWord_2450975 prefixEnd_2450975 1258528247153653282740677 := by
  unfold tailWord_2450975
  simp only [CollatzResearch.WordTrace]
  refine ⟨89394402295543643049202379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59596268197029095366134919 89394402295543643049202379)
  ·
    refine ⟨134091603443315464573803569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89394402295543643049202379 134091603443315464573803569)
    ·
      refine ⟨100568702582486598430352677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134091603443315464573803569 100568702582486598430352677)
      ·
        refine ⟨18856631734216237205691127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100568702582486598430352677 18856631734216237205691127)
        ·
          refine ⟨28284947601324355808536691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18856631734216237205691127 28284947601324355808536691)
          ·
            refine ⟨42427421401986533712805037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28284947601324355808536691 42427421401986533712805037)
            ·
              refine ⟨15910283025744950142301889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42427421401986533712805037 15910283025744950142301889)
              ·
                refine ⟨11932712269308712606726417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15910283025744950142301889 11932712269308712606726417)
                ·
                  refine ⟨8949534201981534455044813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11932712269308712606726417 8949534201981534455044813)
                  ·
                    refine ⟨3356075325743075420641805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8949534201981534455044813 3356075325743075420641805)
                    ·
                      refine ⟨1258528247153653282740677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3356075325743075420641805 1258528247153653282740677)
                      ·
                        rfl

theorem cell23_2450975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_2450975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450975 prefixEnd_2450975 := by exact prefixLift 2450975
  have htrace : WordTrace (prefixWord ++ tailWord_2450975) baseStart_2450975 baseEnd_2450975 := by
    simpa [prefixWord, tailWord_2450975, baseEnd_2450975] using wordTrace_append hprefix tailTrace_2450975
  have hstable : (prefixWord ++ tailWord_2450975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450975).length < 2 ^ (prefixWord ++ tailWord_2450975).sum := by decide
  have hdescent : baseEnd_2450975 < baseStart_2450975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2450976 : List Nat := [2, 1, 1, 6, 1, 1, 3, 2, 2, 2, 2]
def baseStart_2450976 : Nat := 118140960795 + 2450976 * 2 ^ 59
def prefixEnd_2450976 : Nat := 4983230072969 + 3 ^ 40 * 2450976 * 2
def baseEnd_2450976 : Nat := 1258528760634307778828173

theorem tailTrace_2450976 : CollatzResearch.WordTrace tailWord_2450976 prefixEnd_2450976 1258528760634307778828173 := by
  unfold tailWord_2450976
  simp only [CollatzResearch.WordTrace]
  refine ⟨44697219384270010109994391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59596292512360013479992521 44697219384270010109994391)
  ·
    refine ⟨67045829076405015164991587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44697219384270010109994391 67045829076405015164991587)
    ·
      refine ⟨100568743614607522747487381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67045829076405015164991587 100568743614607522747487381)
      ·
        refine ⟨4714159856934727628788471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 100568743614607522747487381 4714159856934727628788471)
        ·
          refine ⟨7071239785402091443182707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4714159856934727628788471 7071239785402091443182707)
          ·
            refine ⟨10606859678103137164774061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7071239785402091443182707 10606859678103137164774061)
            ·
              refine ⟨3977572379288676436790273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10606859678103137164774061 3977572379288676436790273)
              ·
                refine ⟨2983179284466507327592705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3977572379288676436790273 2983179284466507327592705)
                ·
                  refine ⟨2237384463349880495694529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2983179284466507327592705 2237384463349880495694529)
                  ·
                    refine ⟨1678038347512410371770897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2237384463349880495694529 1678038347512410371770897)
                    ·
                      refine ⟨1258528760634307778828173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1678038347512410371770897 1258528760634307778828173)
                      ·
                        rfl

theorem cell23_2450976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_2450976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2450976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2450976 prefixEnd_2450976 := by exact prefixLift 2450976
  have htrace : WordTrace (prefixWord ++ tailWord_2450976) baseStart_2450976 baseEnd_2450976 := by
    simpa [prefixWord, tailWord_2450976, baseEnd_2450976] using wordTrace_append hprefix tailTrace_2450976
  have hstable : (prefixWord ++ tailWord_2450976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2450976).length < 2 ^ (prefixWord ++ tailWord_2450976).sum := by decide
  have hdescent : baseEnd_2450976 < baseStart_2450976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2450976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451008 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 1, 10]
def baseStart_2451008 : Nat := 118140960795 + 2451008 * 2 ^ 59
def prefixEnd_2451008 : Nat := 4983230072969 + 3 ^ 40 * 2451008 * 2
def baseEnd_2451008 : Nat := 419515064005083884542675

theorem tailTrace_2451008 : CollatzResearch.WordTrace tailWord_2451008 prefixEnd_2451008 419515064005083884542675 := by
  unfold tailWord_2451008
  simp only [CollatzResearch.WordTrace]
  refine ⟨44697802952212044842576839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59597070602949393123435785 44697802952212044842576839)
  ·
    refine ⟨67046704428318067263865259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44697802952212044842576839 67046704428318067263865259)
    ·
      refine ⟨100570056642477100895797889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67046704428318067263865259 100570056642477100895797889)
      ·
        refine ⟨75427542481857825671848417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100570056642477100895797889 75427542481857825671848417)
        ·
          refine ⟨56570656861393369253886313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75427542481857825671848417 56570656861393369253886313)
          ·
            refine ⟨42427992646045026940414735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56570656861393369253886313 42427992646045026940414735)
            ·
              refine ⟨63641988969067540410622103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42427992646045026940414735 63641988969067540410622103)
              ·
                refine ⟨95462983453601310615933155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63641988969067540410622103 95462983453601310615933155)
                ·
                  refine ⟨143194475180401965923899733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95462983453601310615933155 143194475180401965923899733)
                  ·
                    refine ⟨419515064005083884542675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 143194475180401965923899733 419515064005083884542675)
                    ·
                      rfl

theorem cell23_2451008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 10].length) (baseStart_2451008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451008 prefixEnd_2451008 := by exact prefixLift 2451008
  have htrace : WordTrace (prefixWord ++ tailWord_2451008) baseStart_2451008 baseEnd_2451008 := by
    simpa [prefixWord, tailWord_2451008, baseEnd_2451008] using wordTrace_append hprefix tailTrace_2451008
  have hstable : (prefixWord ++ tailWord_2451008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451008).length < 2 ^ (prefixWord ++ tailWord_2451008).sum := by decide
  have hdescent : baseEnd_2451008 < baseStart_2451008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451069 : List Nat := [1, 4, 1, 1, 4, 2, 2, 1, 2, 2, 3]
def baseStart_2451069 : Nat := 118140960795 + 2451069 * 2 ^ 59
def prefixEnd_2451069 : Nat := 4983230072969 + 3 ^ 40 * 2451069 * 2
def baseEnd_2451069 : Nat := 1258576514335175914965245

theorem tailTrace_2451069 : CollatzResearch.WordTrace tailWord_2451069 prefixEnd_2451069 1258576514335175914965245 := by
  unfold tailWord_2451069
  simp only [CollatzResearch.WordTrace]
  refine ⟨89397830757203097103124261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59598553838135398068749507 89397830757203097103124261)
  ·
    refine ⟨16762093266975580706835799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89397830757203097103124261 16762093266975580706835799)
    ·
      refine ⟨25143139900463371060253699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16762093266975580706835799 25143139900463371060253699)
      ·
        refine ⟨37714709850695056590380549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25143139900463371060253699 37714709850695056590380549)
        ·
          refine ⟨7071508097005323110696353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37714709850695056590380549 7071508097005323110696353)
          ·
            refine ⟨5303631072753992333022265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7071508097005323110696353 5303631072753992333022265)
            ·
              refine ⟨3977723304565494249766699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5303631072753992333022265 3977723304565494249766699)
              ·
                refine ⟨5966584956848241374650049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3977723304565494249766699 5966584956848241374650049)
                ·
                  refine ⟨4474938717636181030987537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5966584956848241374650049 4474938717636181030987537)
                  ·
                    refine ⟨3356204038227135773240653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4474938717636181030987537 3356204038227135773240653)
                    ·
                      refine ⟨1258576514335175914965245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3356204038227135773240653 1258576514335175914965245)
                      ·
                        rfl

theorem cell23_2451069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_2451069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451069 prefixEnd_2451069 := by exact prefixLift 2451069
  have htrace : WordTrace (prefixWord ++ tailWord_2451069) baseStart_2451069 baseEnd_2451069 := by
    simpa [prefixWord, tailWord_2451069, baseEnd_2451069] using wordTrace_append hprefix tailTrace_2451069
  have hstable : (prefixWord ++ tailWord_2451069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451069).length < 2 ^ (prefixWord ++ tailWord_2451069).sum := by decide
  have hdescent : baseEnd_2451069 < baseStart_2451069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451122 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_2451122 : Nat := 118140960795 + 2451122 * 2 ^ 59
def prefixEnd_2451122 : Nat := 4983230072969 + 3 ^ 40 * 2451122 * 2
def baseEnd_2451122 : Nat := 1258603728809864207602501

theorem tailTrace_2451122 : CollatzResearch.WordTrace tailWord_2451122 prefixEnd_2451122 1258603728809864207602501 := by
  unfold tailWord_2451122
  simp only [CollatzResearch.WordTrace]
  refine ⟨22349940956502771788700905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59599842550674058103202413 22349940956502771788700905)
  ·
    refine ⟨16762455717377078841525679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22349940956502771788700905 16762455717377078841525679)
    ·
      refine ⟨25143683576065618262288519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16762455717377078841525679 25143683576065618262288519)
      ·
        refine ⟨37715525364098427393432779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25143683576065618262288519 37715525364098427393432779)
        ·
          refine ⟨56573288046147641090149169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37715525364098427393432779 56573288046147641090149169)
          ·
            refine ⟨42429966034610730817611877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56573288046147641090149169 42429966034610730817611877)
            ·
              refine ⟨7955618631489512028302227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42429966034610730817611877 7955618631489512028302227)
              ·
                refine ⟨11933427947234268042453341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7955618631489512028302227 11933427947234268042453341)
                ·
                  refine ⟨4475035480212850515920003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11933427947234268042453341 4475035480212850515920003)
                  ·
                    refine ⟨6712553220319275773880005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4475035480212850515920003 6712553220319275773880005)
                    ·
                      refine ⟨1258603728809864207602501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6712553220319275773880005 1258603728809864207602501)
                      ·
                        rfl

theorem cell23_2451122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_2451122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451122 prefixEnd_2451122 := by exact prefixLift 2451122
  have htrace : WordTrace (prefixWord ++ tailWord_2451122) baseStart_2451122 baseEnd_2451122 := by
    simpa [prefixWord, tailWord_2451122, baseEnd_2451122] using wordTrace_append hprefix tailTrace_2451122
  have hstable : (prefixWord ++ tailWord_2451122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451122).length < 2 ^ (prefixWord ++ tailWord_2451122).sum := by decide
  have hdescent : baseEnd_2451122 < baseStart_2451122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451132 : List Nat := [2, 2, 2, 3, 1, 2, 2, 2, 1, 6]
def baseStart_2451132 : Nat := 118140960795 + 2451132 * 2 ^ 59
def prefixEnd_2451132 : Nat := 4983230072969 + 3 ^ 40 * 2451132 * 2
def baseEnd_2451132 : Nat := 419536287872136389492485

theorem tailTrace_2451132 : CollatzResearch.WordTrace tailWord_2451132 prefixEnd_2451132 419536287872136389492485 := by
  unfold tailWord_2451132
  simp only [CollatzResearch.WordTrace]
  refine ⟨44700064277987429431333825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59600085703983239241778433 44700064277987429431333825)
  ·
    refine ⟨33525048208490572073500369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44700064277987429431333825 33525048208490572073500369)
    ·
      refine ⟨25143786156367929055125277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33525048208490572073500369 25143786156367929055125277)
      ·
        refine ⟨9428919808637973395671979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25143786156367929055125277 9428919808637973395671979)
        ·
          refine ⟨14143379712956960093507969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9428919808637973395671979 14143379712956960093507969)
          ·
            refine ⟨10607534784717720070130977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14143379712956960093507969 10607534784717720070130977)
            ·
              refine ⟨7955651088538290052598233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10607534784717720070130977 7955651088538290052598233)
              ·
                refine ⟨5966738316403717539448675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7955651088538290052598233 5966738316403717539448675)
                ·
                  refine ⟨8950107474605576309173013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5966738316403717539448675 8950107474605576309173013)
                  ·
                    refine ⟨419536287872136389492485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8950107474605576309173013 419536287872136389492485)
                    ·
                      rfl

theorem cell23_2451132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_2451132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451132 prefixEnd_2451132 := by exact prefixLift 2451132
  have htrace : WordTrace (prefixWord ++ tailWord_2451132) baseStart_2451132 baseEnd_2451132 := by
    simpa [prefixWord, tailWord_2451132, baseEnd_2451132] using wordTrace_append hprefix tailTrace_2451132
  have hstable : (prefixWord ++ tailWord_2451132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451132).length < 2 ^ (prefixWord ++ tailWord_2451132).sum := by decide
  have hdescent : baseEnd_2451132 < baseStart_2451132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451176 : List Nat := [2, 1, 4, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_2451176 : Nat := 118140960795 + 2451176 * 2 ^ 59
def prefixEnd_2451176 : Nat := 4983230072969 + 3 ^ 40 * 2451176 * 2
def baseEnd_2451176 : Nat := 1258631456765206996327253

theorem tailTrace_2451176 : CollatzResearch.WordTrace tailWord_2451176 prefixEnd_2451176 1258631456765206996327253 := by
  unfold tailWord_2451176
  simp only [CollatzResearch.WordTrace]
  refine ⟨44700866683907727188634691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59601155578543636251512921 44700866683907727188634691)
  ·
    refine ⟨67051300025861590782952037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44700866683907727188634691 67051300025861590782952037)
    ·
      refine ⟨12572118754849048271803507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67051300025861590782952037 12572118754849048271803507)
      ·
        refine ⟨18858178132273572407705261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12572118754849048271803507 18858178132273572407705261)
        ·
          refine ⟨7071816799602589652889473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18858178132273572407705261 7071816799602589652889473)
          ·
            refine ⟨5303862599701942239667105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7071816799602589652889473 5303862599701942239667105)
            ·
              refine ⟨3977896949776456679750329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5303862599701942239667105 3977896949776456679750329)
              ·
                refine ⟨2983422712332342509812747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3977896949776456679750329 2983422712332342509812747)
                ·
                  refine ⟨4475134068498513764719121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2983422712332342509812747 4475134068498513764719121)
                  ·
                    refine ⟨3356350551373885323539341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4475134068498513764719121 3356350551373885323539341)
                    ·
                      refine ⟨1258631456765206996327253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3356350551373885323539341 1258631456765206996327253)
                      ·
                        rfl

theorem cell23_2451176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_2451176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451176 prefixEnd_2451176 := by exact prefixLift 2451176
  have htrace : WordTrace (prefixWord ++ tailWord_2451176) baseStart_2451176 baseEnd_2451176 := by
    simpa [prefixWord, tailWord_2451176, baseEnd_2451176] using wordTrace_append hprefix tailTrace_2451176
  have hstable : (prefixWord ++ tailWord_2451176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451176).length < 2 ^ (prefixWord ++ tailWord_2451176).sum := by decide
  have hdescent : baseEnd_2451176 < baseStart_2451176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451190 : List Nat := [5, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2]
def baseStart_2451190 : Nat := 118140960795 + 2451190 * 2 ^ 59
def prefixEnd_2451190 : Nat := 4983230072969 + 3 ^ 40 * 2451190 * 2
def baseEnd_2451190 : Nat := 1258638645494369941552189

theorem tailTrace_2451190 : CollatzResearch.WordTrace tailWord_2451190 prefixEnd_2451190 1258638645494369941552189 := by
  unfold tailWord_2451190
  simp only [CollatzResearch.WordTrace]
  refine ⟨5587640249360295923017439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59601495993176489845519349 5587640249360295923017439)
  ·
    refine ⟨8381460374040443884526159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5587640249360295923017439 8381460374040443884526159)
    ·
      refine ⟨12572190561060665826789239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8381460374040443884526159 12572190561060665826789239)
      ·
        refine ⟨18858285841590998740183859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12572190561060665826789239 18858285841590998740183859)
        ·
          refine ⟨28287428762386498110275789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18858285841590998740183859 28287428762386498110275789)
          ·
            refine ⟨10607785785894936791353421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28287428762386498110275789 10607785785894936791353421)
            ·
              refine ⟨3977919669710601296757533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10607785785894936791353421 3977919669710601296757533)
              ·
                refine ⟨1491719876141475486284075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3977919669710601296757533 1491719876141475486284075)
                ·
                  refine ⟨2237579814212213229426113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1491719876141475486284075 2237579814212213229426113)
                  ·
                    refine ⟨1678184860659159922069585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2237579814212213229426113 1678184860659159922069585)
                    ·
                      refine ⟨1258638645494369941552189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1678184860659159922069585 1258638645494369941552189)
                      ·
                        rfl

theorem cell23_2451190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_2451190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451190 prefixEnd_2451190 := by exact prefixLift 2451190
  have htrace : WordTrace (prefixWord ++ tailWord_2451190) baseStart_2451190 baseEnd_2451190 := by
    simpa [prefixWord, tailWord_2451190, baseEnd_2451190] using wordTrace_append hprefix tailTrace_2451190
  have hstable : (prefixWord ++ tailWord_2451190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451190).length < 2 ^ (prefixWord ++ tailWord_2451190).sum := by decide
  have hdescent : baseEnd_2451190 < baseStart_2451190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451207 : List Nat := [1, 1, 4, 4, 2, 1, 3, 2, 1, 2, 2]
def baseStart_2451207 : Nat := 118140960795 + 2451207 * 2 ^ 59
def prefixEnd_2451207 : Nat := 4983230072969 + 3 ^ 40 * 2451207 * 2
def baseEnd_2451207 : Nat := 1258647374665496375039611

theorem tailTrace_2451207 : CollatzResearch.WordTrace tailWord_2451207 prefixEnd_2451207 1258647374665496375039611 := by
  unfold tailWord_2451207
  simp only [CollatzResearch.WordTrace]
  refine ⟨89402864030703146671647875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59601909353802097781098583 89402864030703146671647875)
  ·
    refine ⟨134104296046054720007471813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89402864030703146671647875 134104296046054720007471813)
    ·
      refine ⟨25144555508635260001400965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134104296046054720007471813 25144555508635260001400965)
      ·
        refine ⟨4714604157869111250262681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25144555508635260001400965 4714604157869111250262681)
        ·
          refine ⟨3535953118401833437697011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4714604157869111250262681 3535953118401833437697011)
          ·
            refine ⟨5303929677602750156545517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3535953118401833437697011 5303929677602750156545517)
            ·
              refine ⟨1988973629101031308704569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5303929677602750156545517 1988973629101031308704569)
              ·
                refine ⟨1491730221825773481528427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1988973629101031308704569 1491730221825773481528427)
                ·
                  refine ⟨2237595332738660222292641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1491730221825773481528427 2237595332738660222292641)
                  ·
                    refine ⟨1678196499553995166719481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2237595332738660222292641 1678196499553995166719481)
                    ·
                      refine ⟨1258647374665496375039611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1678196499553995166719481 1258647374665496375039611)
                      ·
                        rfl

theorem cell23_2451207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_2451207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451207 prefixEnd_2451207 := by exact prefixLift 2451207
  have htrace : WordTrace (prefixWord ++ tailWord_2451207) baseStart_2451207 baseEnd_2451207 := by
    simpa [prefixWord, tailWord_2451207, baseEnd_2451207] using wordTrace_append hprefix tailTrace_2451207
  have hstable : (prefixWord ++ tailWord_2451207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451207).length < 2 ^ (prefixWord ++ tailWord_2451207).sum := by decide
  have hdescent : baseEnd_2451207 < baseStart_2451207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451223 : List Nat := [1, 1, 3, 4, 2, 1, 4, 1, 2, 1, 3]
def baseStart_2451223 : Nat := 118140960795 + 2451223 * 2 ^ 59
def prefixEnd_2451223 : Nat := 4983230072969 + 3 ^ 40 * 2451223 * 2
def baseEnd_2451223 : Nat := 1258655590355968312439537

theorem tailTrace_2451223 : CollatzResearch.WordTrace tailWord_2451223 prefixEnd_2451223 1258655590355968312439537 := by
  unfold tailWord_2451223
  simp only [CollatzResearch.WordTrace]
  refine ⟨89403447598645181404230323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59602298399096787602820215 89403447598645181404230323)
  ·
    refine ⟨134105171397967772106345485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89403447598645181404230323 134105171397967772106345485)
    ·
      refine ⟨50289439274237914539879557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134105171397967772106345485 50289439274237914539879557)
      ·
        refine ⟨9429269863919608976227417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50289439274237914539879557 9429269863919608976227417)
        ·
          refine ⟨7071952397939706732170563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9429269863919608976227417 7071952397939706732170563)
          ·
            refine ⟨10607928596909560098255845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7071952397939706732170563 10607928596909560098255845)
            ·
              refine ⟨1988986611920542518422971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10607928596909560098255845 1988986611920542518422971)
              ·
                refine ⟨2983479917880813777634457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1988986611920542518422971 2983479917880813777634457)
                ·
                  refine ⟨2237609938410610333225843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2983479917880813777634457 2237609938410610333225843)
                  ·
                    refine ⟨3356414907615915499838765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2237609938410610333225843 3356414907615915499838765)
                    ·
                      refine ⟨1258655590355968312439537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3356414907615915499838765 1258655590355968312439537)
                      ·
                        rfl

theorem cell23_2451223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_2451223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451223 prefixEnd_2451223 := by exact prefixLift 2451223
  have htrace : WordTrace (prefixWord ++ tailWord_2451223) baseStart_2451223 baseEnd_2451223 := by
    simpa [prefixWord, tailWord_2451223, baseEnd_2451223] using wordTrace_append hprefix tailTrace_2451223
  have hstable : (prefixWord ++ tailWord_2451223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451223).length < 2 ^ (prefixWord ++ tailWord_2451223).sum := by decide
  have hdescent : baseEnd_2451223 < baseStart_2451223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451232 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 5]
def baseStart_2451232 : Nat := 118140960795 + 2451232 * 2 ^ 59
def prefixEnd_2451232 : Nat := 4983230072969 + 3 ^ 40 * 2451232 * 2
def baseEnd_2451232 : Nat := 1258660211681858777226995

theorem tailTrace_2451232 : CollatzResearch.WordTrace tailWord_2451232 prefixEnd_2451232 1258660211681858777226995 := by
  unfold tailWord_2451232
  simp only [CollatzResearch.WordTrace]
  refine ⟨44701887927806287970653975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59602517237075050627538633 44701887927806287970653975)
  ·
    refine ⟨67052831891709431955980963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44701887927806287970653975 67052831891709431955980963)
    ·
      refine ⟨100579247837564147933971445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67052831891709431955980963 100579247837564147933971445)
      ·
        refine ⟨9429304484771638868809823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100579247837564147933971445 9429304484771638868809823)
        ·
          refine ⟨14143956727157458303214735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9429304484771638868809823 14143956727157458303214735)
          ·
            refine ⟨21215935090736187454822103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14143956727157458303214735 21215935090736187454822103)
            ·
              refine ⟨31823902636104281182233155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21215935090736187454822103 31823902636104281182233155)
              ·
                refine ⟨47735853954156421773349733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31823902636104281182233155 47735853954156421773349733)
                ·
                  refine ⟨8950472616404329082503075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47735853954156421773349733 8950472616404329082503075)
                  ·
                    refine ⟨13425708924606493623754613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8950472616404329082503075 13425708924606493623754613)
                    ·
                      refine ⟨1258660211681858777226995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13425708924606493623754613 1258660211681858777226995)
                      ·
                        rfl

theorem cell23_2451232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_2451232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451232 prefixEnd_2451232 := by exact prefixLift 2451232
  have htrace : WordTrace (prefixWord ++ tailWord_2451232) baseStart_2451232 baseEnd_2451232 := by
    simpa [prefixWord, tailWord_2451232, baseEnd_2451232] using wordTrace_append hprefix tailTrace_2451232
  have hstable : (prefixWord ++ tailWord_2451232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451232).length < 2 ^ (prefixWord ++ tailWord_2451232).sum := by decide
  have hdescent : baseEnd_2451232 < baseStart_2451232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451233 : List Nat := [1, 2, 3, 2, 1, 5, 1, 2, 1, 3, 2]
def baseStart_2451233 : Nat := 118140960795 + 2451233 * 2 ^ 59
def prefixEnd_2451233 : Nat := 4983230072969 + 3 ^ 40 * 2451233 * 2
def baseEnd_2451233 : Nat := 1258660725162513273314491

theorem tailTrace_2451233 : CollatzResearch.WordTrace tailWord_2451233 prefixEnd_2451233 1258660725162513273314491 := by
  unfold tailWord_2451233
  simp only [CollatzResearch.WordTrace]
  refine ⟨89403812328608953112094353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59602541552405968741396235 89403812328608953112094353)
  ·
    refine ⟨67052859246456714834070765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89403812328608953112094353 67052859246456714834070765)
    ·
      refine ⟨25144822217421268062776537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67052859246456714834070765 25144822217421268062776537)
      ·
        refine ⟨18858616663065951047082403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25144822217421268062776537 18858616663065951047082403)
        ·
          refine ⟨28287924994598926570623605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18858616663065951047082403 28287924994598926570623605)
          ·
            refine ⟨2651992968243649365995963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28287924994598926570623605 2651992968243649365995963)
            ·
              refine ⟨3977989452365474048993945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2651992968243649365995963 3977989452365474048993945)
              ·
                refine ⟨2983492089274105536745459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3977989452365474048993945 2983492089274105536745459)
                ·
                  refine ⟨4475238133911158305118189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2983492089274105536745459 4475238133911158305118189)
                  ·
                    refine ⟨1678214300216684364419321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4475238133911158305118189 1678214300216684364419321)
                    ·
                      refine ⟨1258660725162513273314491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1678214300216684364419321 1258660725162513273314491)
                      ·
                        rfl

theorem cell23_2451233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 3, 2].length) (baseStart_2451233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451233 prefixEnd_2451233 := by exact prefixLift 2451233
  have htrace : WordTrace (prefixWord ++ tailWord_2451233) baseStart_2451233 baseEnd_2451233 := by
    simpa [prefixWord, tailWord_2451233, baseEnd_2451233] using wordTrace_append hprefix tailTrace_2451233
  have hstable : (prefixWord ++ tailWord_2451233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451233).length < 2 ^ (prefixWord ++ tailWord_2451233).sum := by decide
  have hdescent : baseEnd_2451233 < baseStart_2451233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451269 : List Nat := [1, 3, 1, 1, 1, 2, 5, 4, 5]
def baseStart_2451269 : Nat := 118140960795 + 2451269 * 2 ^ 59
def prefixEnd_2451269 : Nat := 4983230072969 + 3 ^ 40 * 2451269 * 2
def baseEnd_2451269 : Nat := 139853245607341681384925

theorem tailTrace_2451269 : CollatzResearch.WordTrace tailWord_2451269 prefixEnd_2451269 139853245607341681384925 := by
  unfold tailWord_2451269
  simp only [CollatzResearch.WordTrace]
  refine ⟨89405125356478531260404861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59603416904319020840269907 89405125356478531260404861)
  ·
    refine ⟨33526922008679449222651823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89405125356478531260404861 33526922008679449222651823)
    ·
      refine ⟨50290383013019173833977735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33526922008679449222651823 50290383013019173833977735)
      ·
        refine ⟨75435574519528760750966603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50290383013019173833977735 75435574519528760750966603)
        ·
          refine ⟨113153361779293141126449905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75435574519528760750966603 113153361779293141126449905)
          ·
            refine ⟨84865021334469855844837429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113153361779293141126449905 84865021334469855844837429)
            ·
              refine ⟨7956095750106548985453509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84865021334469855844837429 7956095750106548985453509)
              ·
                refine ⟨1491767953144977934772533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7956095750106548985453509 1491767953144977934772533)
                ·
                  refine ⟨139853245607341681384925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1491767953144977934772533 139853245607341681384925)
                  ·
                    rfl

theorem cell23_2451269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 5].length) (baseStart_2451269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451269 prefixEnd_2451269 := by exact prefixLift 2451269
  have htrace : WordTrace (prefixWord ++ tailWord_2451269) baseStart_2451269 baseEnd_2451269 := by
    simpa [prefixWord, tailWord_2451269, baseEnd_2451269] using wordTrace_append hprefix tailTrace_2451269
  have hstable : (prefixWord ++ tailWord_2451269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451269).length < 2 ^ (prefixWord ++ tailWord_2451269).sum := by decide
  have hdescent : baseEnd_2451269 < baseStart_2451269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451289 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 2, 5, 2]
def baseStart_2451289 : Nat := 118140960795 + 2451289 * 2 ^ 59
def prefixEnd_2451289 : Nat := 4983230072969 + 3 ^ 40 * 2451289 * 2
def baseEnd_2451289 : Nat := 1258689480079165054214233

theorem tailTrace_2451289 : CollatzResearch.WordTrace tailWord_2451289 prefixEnd_2451289 1258689480079165054214233 := by
  unfold tailWord_2451289
  simp only [CollatzResearch.WordTrace]
  refine ⟨89405854816406074676132921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59603903210937383117421947 89405854816406074676132921)
  ·
    refine ⟨67054391112304556007099691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89405854816406074676132921 67054391112304556007099691)
    ·
      refine ⟨100581586668456834010649537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67054391112304556007099691 100581586668456834010649537)
      ·
        refine ⟨75436190001342625507987153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100581586668456834010649537 75436190001342625507987153)
        ·
          refine ⟨56577142501006969130990365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75436190001342625507987153 56577142501006969130990365)
          ·
            refine ⟨21216428437877613424121387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56577142501006969130990365 21216428437877613424121387)
            ·
              refine ⟨31824642656816420136182081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21216428437877613424121387 31824642656816420136182081)
              ·
                refine ⟨23868481992612315102136561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31824642656816420136182081 23868481992612315102136561)
                ·
                  refine ⟨17901361494459236326602421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23868481992612315102136561 17901361494459236326602421)
                  ·
                    refine ⟨1678252640105553405618977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17901361494459236326602421 1678252640105553405618977)
                    ·
                      refine ⟨1258689480079165054214233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1678252640105553405618977 1258689480079165054214233)
                      ·
                        rfl

theorem cell23_2451289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 5, 2].length) (baseStart_2451289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451289 prefixEnd_2451289 := by exact prefixLift 2451289
  have htrace : WordTrace (prefixWord ++ tailWord_2451289) baseStart_2451289 baseEnd_2451289 := by
    simpa [prefixWord, tailWord_2451289, baseEnd_2451289] using wordTrace_append hprefix tailTrace_2451289
  have hstable : (prefixWord ++ tailWord_2451289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451289).length < 2 ^ (prefixWord ++ tailWord_2451289).sum := by decide
  have hdescent : baseEnd_2451289 < baseStart_2451289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451299 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 1, 7]
def baseStart_2451299 : Nat := 118140960795 + 2451299 * 2 ^ 59
def prefixEnd_2451299 : Nat := 4983230072969 + 3 ^ 40 * 2451299 * 2
def baseEnd_2451299 : Nat := 419564871628570005029729

theorem tailTrace_2451299 : CollatzResearch.WordTrace tailWord_2451299 prefixEnd_2451299 419564871628570005029729 := by
  unfold tailWord_2451299
  simp only [CollatzResearch.WordTrace]
  refine ⟨89406219546369846383996951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59604146364246564255997967 89406219546369846383996951)
  ·
    refine ⟨134109329319554769575995427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89406219546369846383996951 134109329319554769575995427)
    ·
      refine ⟨201163993979332154363993141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134109329319554769575995427 201163993979332154363993141)
      ·
        refine ⟨18859124435562389471624357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 201163993979332154363993141 18859124435562389471624357)
        ·
          refine ⟨3536085831667948025929567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18859124435562389471624357 3536085831667948025929567)
          ·
            refine ⟨5304128747501922038894351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3536085831667948025929567 5304128747501922038894351)
            ·
              refine ⟨7956193121252883058341527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5304128747501922038894351 7956193121252883058341527)
              ·
                refine ⟨11934289681879324587512291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7956193121252883058341527 11934289681879324587512291)
                ·
                  refine ⟨17901434522818986881268437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11934289681879324587512291 17901434522818986881268437)
                  ·
                    refine ⟨419564871628570005029729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17901434522818986881268437 419564871628570005029729)
                    ·
                      rfl

theorem cell23_2451299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 7].length) (baseStart_2451299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451299 prefixEnd_2451299 := by exact prefixLift 2451299
  have htrace : WordTrace (prefixWord ++ tailWord_2451299) baseStart_2451299 baseEnd_2451299 := by
    simpa [prefixWord, tailWord_2451299, baseEnd_2451299] using wordTrace_append hprefix tailTrace_2451299
  have hstable : (prefixWord ++ tailWord_2451299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451299).length < 2 ^ (prefixWord ++ tailWord_2451299).sum := by decide
  have hdescent : baseEnd_2451299 < baseStart_2451299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451322 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5]
def baseStart_2451322 : Nat := 118140960795 + 2451322 * 2 ^ 59
def prefixEnd_2451322 : Nat := 4983230072969 + 3 ^ 40 * 2451322 * 2
def baseEnd_2451322 : Nat := 1258706424940763425101581

theorem tailTrace_2451322 : CollatzResearch.WordTrace tailWord_2451322 prefixEnd_2451322 1258706424940763425101581 := by
  unfold tailWord_2451322
  simp only [CollatzResearch.WordTrace]
  refine ⟨22351764606321630328021055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59604705616857680874722813 22351764606321630328021055)
  ·
    refine ⟨33527646909482445492031583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22351764606321630328021055 33527646909482445492031583)
    ·
      refine ⟨50291470364223668238047375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33527646909482445492031583 50291470364223668238047375)
      ·
        refine ⟨75437205546335502357071063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50291470364223668238047375 75437205546335502357071063)
        ·
          refine ⟨113155808319503253535606595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75437205546335502357071063 113155808319503253535606595)
          ·
            refine ⟨169733712479254880303409893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113155808319503253535606595 169733712479254880303409893)
            ·
              refine ⟨31825071089860290056889355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169733712479254880303409893 31825071089860290056889355)
              ·
                refine ⟨47737606634790435085334033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31825071089860290056889355 47737606634790435085334033)
                ·
                  refine ⟨35803204976092826314000525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47737606634790435085334033 35803204976092826314000525)
                  ·
                    refine ⟨13426201866034809867750197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35803204976092826314000525 13426201866034809867750197)
                    ·
                      refine ⟨1258706424940763425101581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13426201866034809867750197 1258706424940763425101581)
                      ·
                        rfl

theorem cell23_2451322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_2451322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451322 prefixEnd_2451322 := by exact prefixLift 2451322
  have htrace : WordTrace (prefixWord ++ tailWord_2451322) baseStart_2451322 baseEnd_2451322 := by
    simpa [prefixWord, tailWord_2451322, baseEnd_2451322] using wordTrace_append hprefix tailTrace_2451322
  have hstable : (prefixWord ++ tailWord_2451322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451322).length < 2 ^ (prefixWord ++ tailWord_2451322).sum := by decide
  have hdescent : baseEnd_2451322 < baseStart_2451322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451356 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_2451356 : Nat := 118140960795 + 2451356 * 2 ^ 59
def prefixEnd_2451356 : Nat := 4983230072969 + 3 ^ 40 * 2451356 * 2
def baseEnd_2451356 : Nat := 1258723883283016292076425

theorem tailTrace_2451356 : CollatzResearch.WordTrace tailWord_2451356 prefixEnd_2451356 1258723883283016292076425 := by
  unfold tailWord_2451356
  simp only [CollatzResearch.WordTrace]
  refine ⟨44704149253581672559410961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59605532338108896745881281 44704149253581672559410961)
  ·
    refine ⟨33528111940186254419558221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44704149253581672559410961 33528111940186254419558221)
    ·
      refine ⟨12573041977569845407334333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33528111940186254419558221 12573041977569845407334333)
      ·
        refine ⟨4714890741588692027750375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12573041977569845407334333 4714890741588692027750375)
        ·
          refine ⟨7072336112383038041625563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4714890741588692027750375 7072336112383038041625563)
          ·
            refine ⟨10608504168574557062438345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7072336112383038041625563 10608504168574557062438345)
            ·
              refine ⟨7956378126430917796828759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10608504168574557062438345 7956378126430917796828759)
              ·
                refine ⟨11934567189646376695243139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7956378126430917796828759 11934567189646376695243139)
                ·
                  refine ⟨17901850784469565042864709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11934567189646376695243139 17901850784469565042864709)
                  ·
                    refine ⟨3356597022088043445537133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17901850784469565042864709 3356597022088043445537133)
                    ·
                      refine ⟨1258723883283016292076425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3356597022088043445537133 1258723883283016292076425)
                      ·
                        rfl

theorem cell23_2451356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_2451356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451356 prefixEnd_2451356 := by exact prefixLift 2451356
  have htrace : WordTrace (prefixWord ++ tailWord_2451356) baseStart_2451356 baseEnd_2451356 := by
    simpa [prefixWord, tailWord_2451356, baseEnd_2451356] using wordTrace_append hprefix tailTrace_2451356
  have hstable : (prefixWord ++ tailWord_2451356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451356).length < 2 ^ (prefixWord ++ tailWord_2451356).sum := by decide
  have hdescent : baseEnd_2451356 < baseStart_2451356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451386 : List Nat := [3, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3]
def baseStart_2451386 : Nat := 118140960795 + 2451386 * 2 ^ 59
def prefixEnd_2451386 : Nat := 4983230072969 + 3 ^ 40 * 2451386 * 2
def baseEnd_2451386 : Nat := 1258739287702651174701287

theorem tailTrace_2451386 : CollatzResearch.WordTrace tailWord_2451386 prefixEnd_2451386 1258739287702651174701287 := by
  unfold tailWord_2451386
  simp only [CollatzResearch.WordTrace]
  refine ⟨22352348174263665060603503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59606261798036440161609341 22352348174263665060603503)
  ·
    refine ⟨33528522261395497590905255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22352348174263665060603503 33528522261395497590905255)
    ·
      refine ⟨50292783392093246386357883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33528522261395497590905255 50292783392093246386357883)
      ·
        refine ⟨75439175088139869579536825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50292783392093246386357883 75439175088139869579536825)
        ·
          refine ⟨56579381316104902184652619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75439175088139869579536825 56579381316104902184652619)
          ·
            refine ⟨84869071974157353276978929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56579381316104902184652619 84869071974157353276978929)
            ·
              refine ⟨63651803980618014957734197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84869071974157353276978929 63651803980618014957734197)
              ·
                refine ⟨5967356623182938902287581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63651803980618014957734197 5967356623182938902287581)
                ·
                  refine ⟨2237758733693602088357843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5967356623182938902287581 2237758733693602088357843)
                  ·
                    refine ⟨3356638100540403132536765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2237758733693602088357843 3356638100540403132536765)
                    ·
                      refine ⟨1258739287702651174701287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3356638100540403132536765 1258739287702651174701287)
                      ·
                        rfl

theorem cell23_2451386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3].length) (baseStart_2451386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451386 prefixEnd_2451386 := by exact prefixLift 2451386
  have htrace : WordTrace (prefixWord ++ tailWord_2451386) baseStart_2451386 baseEnd_2451386 := by
    simpa [prefixWord, tailWord_2451386, baseEnd_2451386] using wordTrace_append hprefix tailTrace_2451386
  have hstable : (prefixWord ++ tailWord_2451386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451386).length < 2 ^ (prefixWord ++ tailWord_2451386).sum := by decide
  have hdescent : baseEnd_2451386 < baseStart_2451386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451413 : List Nat := [1, 3, 2, 3, 2, 1, 1, 3, 2, 3, 2]
def baseStart_2451413 : Nat := 118140960795 + 2451413 * 2 ^ 59
def prefixEnd_2451413 : Nat := 4983230072969 + 3 ^ 40 * 2451413 * 2
def baseEnd_2451413 : Nat := 1258753151680322569063663

theorem tailTrace_2451413 : CollatzResearch.WordTrace tailWord_2451413 prefixEnd_2451413 1258753151680322569063663 := by
  unfold tailWord_2451413
  simp only [CollatzResearch.WordTrace]
  refine ⟨89410377467956843853646893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59606918311971229235764595 89410377467956843853646893)
  ·
    refine ⟨33528891550483816445117585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89410377467956843853646893 33528891550483816445117585)
    ·
      refine ⟨25146668662862862333838189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33528891550483816445117585 25146668662862862333838189)
      ·
        refine ⟨9430000748573573375189321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25146668662862862333838189 9430000748573573375189321)
        ·
          refine ⟨7072500561430180031391991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9430000748573573375189321 7072500561430180031391991)
          ·
            refine ⟨10608750842145270047087987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7072500561430180031391991 10608750842145270047087987)
            ·
              refine ⟨15913126263217905070631981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10608750842145270047087987 15913126263217905070631981)
              ·
                refine ⟨5967422348706714401486993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15913126263217905070631981 5967422348706714401486993)
                ·
                  refine ⟨4475566761530035801115245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5967422348706714401486993 4475566761530035801115245)
                  ·
                    refine ⟨1678337535573763425418217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4475566761530035801115245 1678337535573763425418217)
                    ·
                      refine ⟨1258753151680322569063663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1678337535573763425418217 1258753151680322569063663)
                      ·
                        rfl

theorem cell23_2451413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_2451413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451413 prefixEnd_2451413 := by exact prefixLift 2451413
  have htrace : WordTrace (prefixWord ++ tailWord_2451413) baseStart_2451413 baseEnd_2451413 := by
    simpa [prefixWord, tailWord_2451413, baseEnd_2451413] using wordTrace_append hprefix tailTrace_2451413
  have hstable : (prefixWord ++ tailWord_2451413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451413).length < 2 ^ (prefixWord ++ tailWord_2451413).sum := by decide
  have hdescent : baseEnd_2451413 < baseStart_2451413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451423 : List Nat := [1, 1, 2, 3, 4, 2, 3, 1, 1, 5]
def baseStart_2451423 : Nat := 118140960795 + 2451423 * 2 ^ 59
def prefixEnd_2451423 : Nat := 4983230072969 + 3 ^ 40 * 2451423 * 2
def baseEnd_2451423 : Nat := 419586095495622509979539

theorem tailTrace_2451423 : CollatzResearch.WordTrace tailWord_2451423 prefixEnd_2451423 419586095495622509979539 := by
  unfold tailWord_2451423
  simp only [CollatzResearch.WordTrace]
  refine ⟨89410742197920615561510923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59607161465280410374340615 89410742197920615561510923)
  ·
    refine ⟨134116113296880923342266385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89410742197920615561510923 134116113296880923342266385)
    ·
      refine ⟨100587084972660692506699789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134116113296880923342266385 100587084972660692506699789)
      ·
        refine ⟨37720156864747759690012421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100587084972660692506699789 37720156864747759690012421)
        ·
          refine ⟨7072529412140204941877329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37720156864747759690012421 7072529412140204941877329)
          ·
            refine ⟨5304397059105153706407997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7072529412140204941877329 5304397059105153706407997)
            ·
              refine ⟨1989148897164432639902999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5304397059105153706407997 1989148897164432639902999)
              ·
                refine ⟨2983723345746648959854499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989148897164432639902999 2983723345746648959854499)
                ·
                  refine ⟨4475585018619973439781749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2983723345746648959854499 4475585018619973439781749)
                  ·
                    refine ⟨419586095495622509979539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4475585018619973439781749 419586095495622509979539)
                    ·
                      rfl

theorem cell23_2451423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 1, 5].length) (baseStart_2451423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451423 prefixEnd_2451423 := by exact prefixLift 2451423
  have htrace : WordTrace (prefixWord ++ tailWord_2451423) baseStart_2451423 baseEnd_2451423 := by
    simpa [prefixWord, tailWord_2451423, baseEnd_2451423] using wordTrace_append hprefix tailTrace_2451423
  have hstable : (prefixWord ++ tailWord_2451423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451423).length < 2 ^ (prefixWord ++ tailWord_2451423).sum := by decide
  have hdescent : baseEnd_2451423 < baseStart_2451423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451439 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 4]
def baseStart_2451439 : Nat := 118140960795 + 2451439 * 2 ^ 59
def prefixEnd_2451439 : Nat := 4983230072969 + 3 ^ 40 * 2451439 * 2
def baseEnd_2451439 : Nat := 1258766502177339467338543

theorem tailTrace_2451439 : CollatzResearch.WordTrace tailWord_2451439 prefixEnd_2451439 1258766502177339467338543 := by
  unfold tailWord_2451439
  simp only [CollatzResearch.WordTrace]
  refine ⟨89411325765862650294093371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59607550510575100196062247 89411325765862650294093371)
  ·
    refine ⟨134116988648793975441140057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89411325765862650294093371 134116988648793975441140057)
    ·
      refine ⟨100587741486595481580855043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134116988648793975441140057 100587741486595481580855043)
      ·
        refine ⟨150881612229893222371282565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100587741486595481580855043 150881612229893222371282565)
        ·
          refine ⟨28290302293104979194615481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150881612229893222371282565 28290302293104979194615481)
          ·
            refine ⟨21217726719828734395961611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28290302293104979194615481 21217726719828734395961611)
            ·
              refine ⟨31826590079743101593942417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21217726719828734395961611 31826590079743101593942417)
              ·
                refine ⟨23869942559807326195456813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31826590079743101593942417 23869942559807326195456813)
                ·
                  refine ⟨8951228459927747323296305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23869942559807326195456813 8951228459927747323296305)
                  ·
                    refine ⟨6713421344945810492472229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8951228459927747323296305 6713421344945810492472229)
                    ·
                      refine ⟨1258766502177339467338543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6713421344945810492472229 1258766502177339467338543)
                      ·
                        rfl

theorem cell23_2451439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_2451439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451439 prefixEnd_2451439 := by exact prefixLift 2451439
  have htrace : WordTrace (prefixWord ++ tailWord_2451439) baseStart_2451439 baseEnd_2451439 := by
    simpa [prefixWord, tailWord_2451439, baseEnd_2451439] using wordTrace_append hprefix tailTrace_2451439
  have hstable : (prefixWord ++ tailWord_2451439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451439).length < 2 ^ (prefixWord ++ tailWord_2451439).sum := by decide
  have hdescent : baseEnd_2451439 < baseStart_2451439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451449 : List Nat := [1, 2, 1, 3, 1, 4, 3, 8]
def baseStart_2451449 : Nat := 118140960795 + 2451449 * 2 ^ 59
def prefixEnd_2451449 : Nat := 4983230072969 + 3 ^ 40 * 2451449 * 2
def baseEnd_2451449 : Nat := 46621171740143867711611

theorem tailTrace_2451449 : CollatzResearch.WordTrace tailWord_2451449 prefixEnd_2451449 46621171740143867711611 := by
  unfold tailWord_2451449
  simp only [CollatzResearch.WordTrace]
  refine ⟨89411690495826422001957401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59607793663884281334638267 89411690495826422001957401)
  ·
    refine ⟨67058767871869816501468051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89411690495826422001957401 67058767871869816501468051)
    ·
      refine ⟨100588151807804724752202077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67058767871869816501468051 100588151807804724752202077)
      ·
        refine ⟨37720556927926771782075779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100588151807804724752202077 37720556927926771782075779)
        ·
          refine ⟨56580835391890157673113669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37720556927926771782075779 56580835391890157673113669)
          ·
            refine ⟨10608906635979404563708813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56580835391890157673113669 10608906635979404563708813)
            ·
              refine ⟨3978339988492276711390805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10608906635979404563708813 3978339988492276711390805)
              ·
                refine ⟨46621171740143867711611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3978339988492276711390805 46621171740143867711611)
                ·
                  rfl

theorem cell23_2451449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 8].length) (baseStart_2451449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451449 prefixEnd_2451449 := by exact prefixLift 2451449
  have htrace : WordTrace (prefixWord ++ tailWord_2451449) baseStart_2451449 baseEnd_2451449 := by
    simpa [prefixWord, tailWord_2451449, baseEnd_2451449] using wordTrace_append hprefix tailTrace_2451449
  have hstable : (prefixWord ++ tailWord_2451449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451449).length < 2 ^ (prefixWord ++ tailWord_2451449).sum := by decide
  have hdescent : baseEnd_2451449 < baseStart_2451449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451477 : List Nat := [1, 3, 2, 1, 6, 1, 2, 1, 1, 1, 4]
def baseStart_2451477 : Nat := 118140960795 + 2451477 * 2 ^ 59
def prefixEnd_2451477 : Nat := 4983230072969 + 3 ^ 40 * 2451477 * 2
def baseEnd_2451477 : Nat := 1258786014442210318663369

theorem tailTrace_2451477 : CollatzResearch.WordTrace tailWord_2451477 prefixEnd_2451477 1258786014442210318663369 := by
  unfold tailWord_2451477
  simp only [CollatzResearch.WordTrace]
  refine ⟨89412711739724982783976685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59608474493149988522651123 89412711739724982783976685)
  ·
    refine ⟨33529766902396868543991257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89412711739724982783976685 33529766902396868543991257)
    ·
      refine ⟨25147325176797651407993443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33529766902396868543991257 25147325176797651407993443)
      ·
        refine ⟨37720987765196477111990165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25147325176797651407993443 37720987765196477111990165)
        ·
          refine ⟨1768171301493584864624539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37720987765196477111990165 1768171301493584864624539)
          ·
            refine ⟨2652256952240377296936809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1768171301493584864624539 2652256952240377296936809)
            ·
              refine ⟨1989192714180282972702607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2652256952240377296936809 1989192714180282972702607)
              ·
                refine ⟨2983789071270424459053911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989192714180282972702607 2983789071270424459053911)
                ·
                  refine ⟨4475683606905636688580867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2983789071270424459053911 4475683606905636688580867)
                  ·
                    refine ⟨6713525410358455032871301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4475683606905636688580867 6713525410358455032871301)
                    ·
                      refine ⟨1258786014442210318663369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6713525410358455032871301 1258786014442210318663369)
                      ·
                        rfl

theorem cell23_2451477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 1, 1, 4].length) (baseStart_2451477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451477 prefixEnd_2451477 := by exact prefixLift 2451477
  have htrace : WordTrace (prefixWord ++ tailWord_2451477) baseStart_2451477 baseEnd_2451477 := by
    simpa [prefixWord, tailWord_2451477, baseEnd_2451477] using wordTrace_append hprefix tailTrace_2451477
  have hstable : (prefixWord ++ tailWord_2451477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451477).length < 2 ^ (prefixWord ++ tailWord_2451477).sum := by decide
  have hdescent : baseEnd_2451477 < baseStart_2451477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451493 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 4, 1, 3]
def baseStart_2451493 : Nat := 118140960795 + 2451493 * 2 ^ 59
def prefixEnd_2451493 : Nat := 4983230072969 + 3 ^ 40 * 2451493 * 2
def baseEnd_2451493 : Nat := 1258794230132682256063295

theorem tailTrace_2451493 : CollatzResearch.WordTrace tailWord_2451493 prefixEnd_2451493 1258794230132682256063295 := by
  unfold tailWord_2451493
  simp only [CollatzResearch.WordTrace]
  refine ⟨89413295307667017516559133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59608863538444678344372755 89413295307667017516559133)
  ·
    refine ⟨33529985740375131568709675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89413295307667017516559133 33529985740375131568709675)
    ·
      refine ⟨50294978610562697353064513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33529985740375131568709675 50294978610562697353064513)
      ·
        refine ⟨37721233957922023014798385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50294978610562697353064513 37721233957922023014798385)
        ·
          refine ⟨28290925468441517261098789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37721233957922023014798385 28290925468441517261098789)
          ·
            refine ⟨5304548525332784486456023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28290925468441517261098789 5304548525332784486456023)
            ·
              refine ⟨7956822787999176729684035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5304548525332784486456023 7956822787999176729684035)
              ·
                refine ⟨11935234181998765094526053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7956822787999176729684035 11935234181998765094526053)
                ·
                  refine ⟨2237856409124768455223635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11935234181998765094526053 2237856409124768455223635)
                  ·
                    refine ⟨3356784613687152682835453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2237856409124768455223635 3356784613687152682835453)
                    ·
                      refine ⟨1258794230132682256063295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3356784613687152682835453 1258794230132682256063295)
                      ·
                        rfl

theorem cell23_2451493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 4, 1, 3].length) (baseStart_2451493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451493 prefixEnd_2451493 := by exact prefixLift 2451493
  have htrace : WordTrace (prefixWord ++ tailWord_2451493) baseStart_2451493 baseEnd_2451493 := by
    simpa [prefixWord, tailWord_2451493, baseEnd_2451493] using wordTrace_append hprefix tailTrace_2451493
  have hstable : (prefixWord ++ tailWord_2451493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451493).length < 2 ^ (prefixWord ++ tailWord_2451493).sum := by decide
  have hdescent : baseEnd_2451493 < baseStart_2451493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451499 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 4]
def baseStart_2451499 : Nat := 118140960795 + 2451499 * 2 ^ 59
def prefixEnd_2451499 : Nat := 4983230072969 + 3 ^ 40 * 2451499 * 2
def baseEnd_2451499 : Nat := 1258797311016609232588267

theorem tailTrace_2451499 : CollatzResearch.WordTrace tailWord_2451499 prefixEnd_2451499 1258797311016609232588267 := by
  unfold tailWord_2451499
  simp only [CollatzResearch.WordTrace]
  refine ⟨89413514145645280541277551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59609009430430187027518367 89413514145645280541277551)
  ·
    refine ⟨134120271218467920811916327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89413514145645280541277551 134120271218467920811916327)
    ·
      refine ⟨201180406827701881217874491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134120271218467920811916327 201180406827701881217874491)
      ·
        refine ⟨301770610241552821826811737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201180406827701881217874491 301770610241552821826811737)
        ·
          refine ⟨226327957681164616370108803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301770610241552821826811737 226327957681164616370108803)
          ·
            refine ⟨339491936521746924555163205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226327957681164616370108803 339491936521746924555163205)
            ·
              refine ⟨63654738097827548354093101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 339491936521746924555163205 63654738097827548354093101)
              ·
                refine ⟨23870526786685330632784913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63654738097827548354093101 23870526786685330632784913)
                ·
                  refine ⟨17902895090013997974588685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23870526786685330632784913 17902895090013997974588685)
                  ·
                    refine ⟨6713585658755249240470757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17902895090013997974588685 6713585658755249240470757)
                    ·
                      refine ⟨1258797311016609232588267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6713585658755249240470757 1258797311016609232588267)
                      ·
                        rfl

theorem cell23_2451499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 4].length) (baseStart_2451499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451499 prefixEnd_2451499 := by exact prefixLift 2451499
  have htrace : WordTrace (prefixWord ++ tailWord_2451499) baseStart_2451499 baseEnd_2451499 := by
    simpa [prefixWord, tailWord_2451499, baseEnd_2451499] using wordTrace_append hprefix tailTrace_2451499
  have hstable : (prefixWord ++ tailWord_2451499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451499).length < 2 ^ (prefixWord ++ tailWord_2451499).sum := by decide
  have hdescent : baseEnd_2451499 < baseStart_2451499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451520 : List Nat := [2, 1, 1, 2, 2, 5, 2, 2, 1, 3, 2]
def baseStart_2451520 : Nat := 118140960795 + 2451520 * 2 ^ 59
def prefixEnd_2451520 : Nat := 4983230072969 + 3 ^ 40 * 2451520 * 2
def baseEnd_2451520 : Nat := 1258808094110353650425671

theorem tailTrace_2451520 : CollatzResearch.WordTrace tailWord_2451520 prefixEnd_2451520 1258808094110353650425671 := by
  unfold tailWord_2451520
  simp only [CollatzResearch.WordTrace]
  refine ⟨44707140039284600563896007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59609520052379467418528009 44707140039284600563896007)
  ·
    refine ⟨67060710058926900845844011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44707140039284600563896007 67060710058926900845844011)
    ·
      refine ⟨100591065088390351268766017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67060710058926900845844011 100591065088390351268766017)
      ·
        refine ⟨75443298816292763451574513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100591065088390351268766017 75443298816292763451574513)
        ·
          refine ⟨56582474112219572588680885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75443298816292763451574513 56582474112219572588680885)
          ·
            refine ⟨5304606948020584930188833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56582474112219572588680885 5304606948020584930188833)
            ·
              refine ⟨3978455211015438697641625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5304606948020584930188833 3978455211015438697641625)
              ·
                refine ⟨2983841408261579023231219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3978455211015438697641625 2983841408261579023231219)
                ·
                  refine ⟨4475762112392368534846829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2983841408261579023231219 4475762112392368534846829)
                  ·
                    refine ⟨1678410792147138200567561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4475762112392368534846829 1678410792147138200567561)
                    ·
                      refine ⟨1258808094110353650425671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1678410792147138200567561 1258808094110353650425671)
                      ·
                        rfl

theorem cell23_2451520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 1, 3, 2].length) (baseStart_2451520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451520 prefixEnd_2451520 := by exact prefixLift 2451520
  have htrace : WordTrace (prefixWord ++ tailWord_2451520) baseStart_2451520 baseEnd_2451520 := by
    simpa [prefixWord, tailWord_2451520, baseEnd_2451520] using wordTrace_append hprefix tailTrace_2451520
  have hstable : (prefixWord ++ tailWord_2451520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451520).length < 2 ^ (prefixWord ++ tailWord_2451520).sum := by decide
  have hdescent : baseEnd_2451520 < baseStart_2451520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451556 : List Nat := [2, 3, 1, 1, 2, 1, 5, 1, 7]
def baseStart_2451556 : Nat := 118140960795 + 2451556 * 2 ^ 59
def prefixEnd_2451556 : Nat := 4983230072969 + 3 ^ 40 * 2451556 * 2
def baseEnd_2451556 : Nat := 139869619934879501063945

theorem tailTrace_2451556 : CollatzResearch.WordTrace tailWord_2451556 prefixEnd_2451556 139869619934879501063945 := by
  unfold tailWord_2451556
  simp only [CollatzResearch.WordTrace]
  refine ⟨44707796553219389638051261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59610395404292519517401681 44707796553219389638051261)
  ·
    refine ⟨16765423707457271114269223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44707796553219389638051261 16765423707457271114269223)
    ·
      refine ⟨25148135561185906671403835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16765423707457271114269223 25148135561185906671403835)
      ·
        refine ⟨37722203341778860007105753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25148135561185906671403835 37722203341778860007105753)
        ·
          refine ⟨28291652506334145005329315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37722203341778860007105753 28291652506334145005329315)
          ·
            refine ⟨42437478759501217507993973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28291652506334145005329315 42437478759501217507993973)
            ·
              refine ⟨3978513633703239141374435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42437478759501217507993973 3978513633703239141374435)
              ·
                refine ⟨5967770450554858712061653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3978513633703239141374435 5967770450554858712061653)
                ·
                  refine ⟨139869619934879501063945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5967770450554858712061653 139869619934879501063945)
                  ·
                    rfl

theorem cell23_2451556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_2451556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451556 prefixEnd_2451556 := by exact prefixLift 2451556
  have htrace : WordTrace (prefixWord ++ tailWord_2451556) baseStart_2451556 baseEnd_2451556 := by
    simpa [prefixWord, tailWord_2451556, baseEnd_2451556] using wordTrace_append hprefix tailTrace_2451556
  have hstable : (prefixWord ++ tailWord_2451556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451556).length < 2 ^ (prefixWord ++ tailWord_2451556).sum := by decide
  have hdescent : baseEnd_2451556 < baseStart_2451556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451567 : List Nat := [1, 1, 2, 1, 3, 4, 4, 1, 2, 2, 2]
def baseStart_2451567 : Nat := 118140960795 + 2451567 * 2 ^ 59
def prefixEnd_2451567 : Nat := 4983230072969 + 3 ^ 40 * 2451567 * 2
def baseEnd_2451567 : Nat := 1258832227701114966537955

theorem tailTrace_2451567 : CollatzResearch.WordTrace tailWord_2451567 prefixEnd_2451567 1258832227701114966537955 := by
  unfold tailWord_2451567
  simp only [CollatzResearch.WordTrace]
  refine ⟨89415994309398928154752955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59610662872932618769835303 89415994309398928154752955)
  ·
    refine ⟨134123991464098392232129433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89415994309398928154752955 134123991464098392232129433)
    ·
      refine ⟨100592993598073794174097075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134123991464098392232129433 100592993598073794174097075)
      ·
        refine ⟨150889490397110691261145613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100592993598073794174097075 150889490397110691261145613)
        ·
          refine ⟨56583558898916509222929605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150889490397110691261145613 56583558898916509222929605)
          ·
            refine ⟨10609417293546845479299301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56583558898916509222929605 10609417293546845479299301)
            ·
              refine ⟨1989265742540033527368619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10609417293546845479299301 1989265742540033527368619)
              ·
                refine ⟨2983898613810050291052929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989265742540033527368619 2983898613810050291052929)
                ·
                  refine ⟨2237923960357537718289697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2983898613810050291052929 2237923960357537718289697)
                  ·
                    refine ⟨1678442970268153288717273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2237923960357537718289697 1678442970268153288717273)
                    ·
                      refine ⟨1258832227701114966537955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1678442970268153288717273 1258832227701114966537955)
                      ·
                        rfl

theorem cell23_2451567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 4, 1, 2, 2, 2].length) (baseStart_2451567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451567 prefixEnd_2451567 := by exact prefixLift 2451567
  have htrace : WordTrace (prefixWord ++ tailWord_2451567) baseStart_2451567 baseEnd_2451567 := by
    simpa [prefixWord, tailWord_2451567, baseEnd_2451567] using wordTrace_append hprefix tailTrace_2451567
  have hstable : (prefixWord ++ tailWord_2451567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451567).length < 2 ^ (prefixWord ++ tailWord_2451567).sum := by decide
  have hdescent : baseEnd_2451567 < baseStart_2451567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451607 : List Nat := [1, 1, 3, 3, 4, 2, 2, 2, 5]
def baseStart_2451607 : Nat := 118140960795 + 2451607 * 2 ^ 59
def prefixEnd_2451607 : Nat := 4983230072969 + 3 ^ 40 * 2451607 * 2
def baseEnd_2451607 : Nat := 139872529658588312226419

theorem tailTrace_2451607 : CollatzResearch.WordTrace tailWord_2451607 prefixEnd_2451607 139872529658588312226419 := by
  unfold tailWord_2451607
  simp only [CollatzResearch.WordTrace]
  refine ⟨89417453229254014986209075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59611635486169343324139383 89417453229254014986209075)
  ·
    refine ⟨134126179843881022479313613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89417453229254014986209075 134126179843881022479313613)
    ·
      refine ⟨50297317441455383429742605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134126179843881022479313613 50297317441455383429742605)
      ·
        refine ⟨18861494040545768786153477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50297317441455383429742605 18861494040545768786153477)
        ·
          refine ⟨3536530132602331647403777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18861494040545768786153477 3536530132602331647403777)
          ·
            refine ⟨2652397599451748735552833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3536530132602331647403777 2652397599451748735552833)
            ·
              refine ⟨1989298199588811551664625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2652397599451748735552833 1989298199588811551664625)
              ·
                refine ⟨1491973649691608663748469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1989298199588811551664625 1491973649691608663748469)
                ·
                  refine ⟨139872529658588312226419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1491973649691608663748469 139872529658588312226419)
                  ·
                    rfl

theorem cell23_2451607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 5].length) (baseStart_2451607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451607 prefixEnd_2451607 := by exact prefixLift 2451607
  have htrace : WordTrace (prefixWord ++ tailWord_2451607) baseStart_2451607 baseEnd_2451607 := by
    simpa [prefixWord, tailWord_2451607, baseEnd_2451607] using wordTrace_append hprefix tailTrace_2451607
  have hstable : (prefixWord ++ tailWord_2451607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451607).length < 2 ^ (prefixWord ++ tailWord_2451607).sum := by decide
  have hdescent : baseEnd_2451607 < baseStart_2451607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451637 : List Nat := [1, 3, 3, 4, 1, 2, 1, 1, 2, 5]
def baseStart_2451637 : Nat := 118140960795 + 2451637 * 2 ^ 59
def prefixEnd_2451637 : Nat := 4983230072969 + 3 ^ 40 * 2451637 * 2
def baseEnd_2451637 : Nat := 419622723782309897554211

theorem tailTrace_2451637 : CollatzResearch.WordTrace tailWord_2451637 prefixEnd_2451637 419622723782309897554211 := by
  unfold tailWord_2451637
  simp only [CollatzResearch.WordTrace]
  refine ⟨89418547419145330109801165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59612364946096886739867443 89418547419145330109801165)
  ·
    refine ⟨33531955282179498791175437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89418547419145330109801165 33531955282179498791175437)
    ·
      refine ⟨12574483230817312046690789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33531955282179498791175437 12574483230817312046690789)
      ·
        refine ⟨2357715605778246008754523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12574483230817312046690789 2357715605778246008754523)
        ·
          refine ⟨3536573408667369013131785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2357715605778246008754523 3536573408667369013131785)
          ·
            refine ⟨2652430056500526759848839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3536573408667369013131785 2652430056500526759848839)
            ·
              refine ⟨3978645084750790139773259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2652430056500526759848839 3978645084750790139773259)
              ·
                refine ⟨5967967627126185209659889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3978645084750790139773259 5967967627126185209659889)
                ·
                  refine ⟨4475975720344638907244917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5967967627126185209659889 4475975720344638907244917)
                  ·
                    refine ⟨419622723782309897554211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4475975720344638907244917 419622723782309897554211)
                    ·
                      rfl

theorem cell23_2451637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_2451637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451637 prefixEnd_2451637 := by exact prefixLift 2451637
  have htrace : WordTrace (prefixWord ++ tailWord_2451637) baseStart_2451637 baseEnd_2451637 := by
    simpa [prefixWord, tailWord_2451637, baseEnd_2451637] using wordTrace_append hprefix tailTrace_2451637
  have hstable : (prefixWord ++ tailWord_2451637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451637).length < 2 ^ (prefixWord ++ tailWord_2451637).sum := by decide
  have hdescent : baseEnd_2451637 < baseStart_2451637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451690 : List Nat := [3, 1, 3, 1, 1, 2, 1, 4, 3, 1, 3]
def baseStart_2451690 : Nat := 118140960795 + 2451690 * 2 ^ 59
def prefixEnd_2451690 : Nat := 4983230072969 + 3 ^ 40 * 2451690 * 2
def baseEnd_2451690 : Nat := 1258895385821617985299889

theorem tailTrace_2451690 : CollatzResearch.WordTrace tailWord_2451690 prefixEnd_2451690 1258895385821617985299889 := by
  unfold tailWord_2451690
  simp only [CollatzResearch.WordTrace]
  refine ⟨22355120121988330040370131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59613653658635546774320349 22355120121988330040370131)
  ·
    refine ⟨33532680182982495060555197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22355120121988330040370131 33532680182982495060555197)
    ·
      refine ⟨12574755068618435647708199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33532680182982495060555197 12574755068618435647708199)
      ·
        refine ⟨18862132602927653471562299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12574755068618435647708199 18862132602927653471562299)
        ·
          refine ⟨28293198904391480207343449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18862132602927653471562299 28293198904391480207343449)
          ·
            refine ⟨21219899178293610155507587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28293198904391480207343449 21219899178293610155507587)
            ·
              refine ⟨31829848767440415233261381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21219899178293610155507587 31829848767440415233261381)
              ·
                refine ⟨5968096643895077856236509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31829848767440415233261381 5968096643895077856236509)
                ·
                  refine ⟨2238036241460654196088691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5968096643895077856236509 2238036241460654196088691)
                  ·
                    refine ⟨3357054362190981294133037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2238036241460654196088691 3357054362190981294133037)
                    ·
                      refine ⟨1258895385821617985299889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3357054362190981294133037 1258895385821617985299889)
                      ·
                        rfl

theorem cell23_2451690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_2451690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451690 prefixEnd_2451690 := by exact prefixLift 2451690
  have htrace : WordTrace (prefixWord ++ tailWord_2451690) baseStart_2451690 baseEnd_2451690 := by
    simpa [prefixWord, tailWord_2451690, baseEnd_2451690] using wordTrace_append hprefix tailTrace_2451690
  have hstable : (prefixWord ++ tailWord_2451690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451690).length < 2 ^ (prefixWord ++ tailWord_2451690).sum := by decide
  have hdescent : baseEnd_2451690 < baseStart_2451690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451696 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 4]
def baseStart_2451696 : Nat := 118140960795 + 2451696 * 2 ^ 59
def prefixEnd_2451696 : Nat := 4983230072969 + 3 ^ 40 * 2451696 * 2
def baseEnd_2451696 : Nat := 1258898466705544961824861

theorem tailTrace_2451696 : CollatzResearch.WordTrace tailWord_2451696 prefixEnd_2451696 1258898466705544961824861 := by
  unfold tailWord_2451696
  simp only [CollatzResearch.WordTrace]
  refine ⟨44710349662965791593099471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59613799550621055457465961 44710349662965791593099471)
  ·
    refine ⟨67065524494448687389649207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44710349662965791593099471 67065524494448687389649207)
    ·
      refine ⟨100598286741673031084473811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67065524494448687389649207 100598286741673031084473811)
      ·
        refine ⟨150897430112509546626710717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100598286741673031084473811 150897430112509546626710717)
        ·
          refine ⟨56586536292191079985016519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150897430112509546626710717 56586536292191079985016519)
          ·
            refine ⟨84879804438286619977524779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56586536292191079985016519 84879804438286619977524779)
            ·
              refine ⟨127319706657429929966287169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84879804438286619977524779 127319706657429929966287169)
              ·
                refine ⟨95489779993072447474715377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127319706657429929966287169 95489779993072447474715377)
                ·
                  refine ⟨71617334994804335606036533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95489779993072447474715377 71617334994804335606036533)
                  ·
                    refine ⟨6714125155762906463065925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71617334994804335606036533 6714125155762906463065925)
                    ·
                      refine ⟨1258898466705544961824861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6714125155762906463065925 1258898466705544961824861)
                      ·
                        rfl

theorem cell23_2451696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_2451696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451696 prefixEnd_2451696 := by exact prefixLift 2451696
  have htrace : WordTrace (prefixWord ++ tailWord_2451696) baseStart_2451696 baseEnd_2451696 := by
    simpa [prefixWord, tailWord_2451696, baseEnd_2451696] using wordTrace_append hprefix tailTrace_2451696
  have hstable : (prefixWord ++ tailWord_2451696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451696).length < 2 ^ (prefixWord ++ tailWord_2451696).sum := by decide
  have hdescent : baseEnd_2451696 < baseStart_2451696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451710 : List Nat := [4, 2, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_2451710 : Nat := 118140960795 + 2451710 * 2 ^ 59
def prefixEnd_2451710 : Nat := 4983230072969 + 3 ^ 40 * 2451710 * 2
def baseEnd_2451710 : Nat := 419635218478235969016599

theorem tailTrace_2451710 : CollatzResearch.WordTrace tailWord_2451710 prefixEnd_2451710 419635218478235969016599 := by
  unfold tailWord_2451710
  simp only [CollatzResearch.WordTrace]
  refine ⟨11177651243485107947151073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59614139965253909051472389 11177651243485107947151073)
  ·
    refine ⟨8383238432613830960363305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11177651243485107947151073 8383238432613830960363305)
    ·
      refine ⟨6287428824460373220272479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8383238432613830960363305 6287428824460373220272479)
      ·
        refine ⟨9431143236690559830408719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6287428824460373220272479 9431143236690559830408719)
        ·
          refine ⟨14146714855035839745613079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9431143236690559830408719 14146714855035839745613079)
          ·
            refine ⟨21220072282553759618419619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14146714855035839745613079 21220072282553759618419619)
            ·
              refine ⟨31830108423830639427629429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21220072282553759618419619 31830108423830639427629429)
              ·
                refine ⟨2984072664734122446340259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31830108423830639427629429 2984072664734122446340259)
                ·
                  refine ⟨4476108997101183669510389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2984072664734122446340259 4476108997101183669510389)
                  ·
                    refine ⟨419635218478235969016599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4476108997101183669510389 419635218478235969016599)
                    ·
                      rfl

theorem cell23_2451710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_2451710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451710 prefixEnd_2451710 := by exact prefixLift 2451710
  have htrace : WordTrace (prefixWord ++ tailWord_2451710) baseStart_2451710 baseEnd_2451710 := by
    simpa [prefixWord, tailWord_2451710, baseEnd_2451710] using wordTrace_append hprefix tailTrace_2451710
  have hstable : (prefixWord ++ tailWord_2451710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451710).length < 2 ^ (prefixWord ++ tailWord_2451710).sum := by decide
  have hdescent : baseEnd_2451710 < baseStart_2451710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451723 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 4, 4]
def baseStart_2451723 : Nat := 118140960795 + 2451723 * 2 ^ 59
def prefixEnd_2451723 : Nat := 4983230072969 + 3 ^ 40 * 2451723 * 2
def baseEnd_2451723 : Nat := 419637443561072118729079

theorem tailTrace_2451723 : CollatzResearch.WordTrace tailWord_2451723 prefixEnd_2451723 419637443561072118729079 := by
  unfold tailWord_2451723
  simp only [CollatzResearch.WordTrace]
  refine ⟨89421684096833766797431823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59614456064555844531621215 89421684096833766797431823)
  ·
    refine ⟨134132526145250650196147735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89421684096833766797431823 134132526145250650196147735)
    ·
      refine ⟨201198789217875975294221603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134132526145250650196147735 201198789217875975294221603)
      ·
        refine ⟨301798183826813962941332405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201198789217875975294221603 301798183826813962941332405)
        ·
          refine ⟨28293579733763809025749913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 301798183826813962941332405 28293579733763809025749913)
          ·
            refine ⟨21220184800322856769312435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28293579733763809025749913 21220184800322856769312435)
            ·
              refine ⟨31830277200484285153968653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21220184800322856769312435 31830277200484285153968653)
              ·
                refine ⟨11936353950181606932738245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31830277200484285153968653 11936353950181606932738245)
                ·
                  refine ⟨2238066365659051299888421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11936353950181606932738245 2238066365659051299888421)
                  ·
                    refine ⟨419637443561072118729079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2238066365659051299888421 419637443561072118729079)
                    ·
                      rfl

theorem cell23_2451723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 4].length) (baseStart_2451723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451723 prefixEnd_2451723 := by exact prefixLift 2451723
  have htrace : WordTrace (prefixWord ++ tailWord_2451723) baseStart_2451723 baseEnd_2451723 := by
    simpa [prefixWord, tailWord_2451723, baseEnd_2451723] using wordTrace_append hprefix tailTrace_2451723
  have hstable : (prefixWord ++ tailWord_2451723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451723).length < 2 ^ (prefixWord ++ tailWord_2451723).sum := by decide
  have hdescent : baseEnd_2451723 < baseStart_2451723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451724 : List Nat := [2, 2, 1, 2, 2, 2, 5, 2, 1, 1, 3]
def baseStart_2451724 : Nat := 118140960795 + 2451724 * 2 ^ 59
def prefixEnd_2451724 : Nat := 4983230072969 + 3 ^ 40 * 2451724 * 2
def baseEnd_2451724 : Nat := 1258912844163870852274733

theorem tailTrace_2451724 : CollatzResearch.WordTrace tailWord_2451724 prefixEnd_2451724 1258912844163870852274733 := by
  unfold tailWord_2451724
  simp only [CollatzResearch.WordTrace]
  refine ⟨44710860284915071984109113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59614480379886762645478817 44710860284915071984109113)
  ·
    refine ⟨33533145213686303988081835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44710860284915071984109113 33533145213686303988081835)
    ·
      refine ⟨50299717820529455982122753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33533145213686303988081835 50299717820529455982122753)
      ·
        refine ⟨37724788365397091986592065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50299717820529455982122753 37724788365397091986592065)
        ·
          refine ⟨28293591274047818989944049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37724788365397091986592065 28293591274047818989944049)
          ·
            refine ⟨21220193455535864242458037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28293591274047818989944049 21220193455535864242458037)
            ·
              refine ⟨1989393136456487272730441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21220193455535864242458037 1989393136456487272730441)
              ·
                refine ⟨1492044852342365454547831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1989393136456487272730441 1492044852342365454547831)
                ·
                  refine ⟨2238067278513548181821747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492044852342365454547831 2238067278513548181821747)
                  ·
                    refine ⟨3357100917770322272732621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2238067278513548181821747 3357100917770322272732621)
                    ·
                      refine ⟨1258912844163870852274733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3357100917770322272732621 1258912844163870852274733)
                      ·
                        rfl

theorem cell23_2451724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 1, 1, 3].length) (baseStart_2451724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451724 prefixEnd_2451724 := by exact prefixLift 2451724
  have htrace : WordTrace (prefixWord ++ tailWord_2451724) baseStart_2451724 baseEnd_2451724 := by
    simpa [prefixWord, tailWord_2451724, baseEnd_2451724] using wordTrace_append hprefix tailTrace_2451724
  have hstable : (prefixWord ++ tailWord_2451724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451724).length < 2 ^ (prefixWord ++ tailWord_2451724).sum := by decide
  have hdescent : baseEnd_2451724 < baseStart_2451724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451733 : List Nat := [1, 3, 2, 1, 2, 1, 4, 2, 1, 1, 5]
def baseStart_2451733 : Nat := 118140960795 + 2451733 * 2 ^ 59
def prefixEnd_2451733 : Nat := 4983230072969 + 3 ^ 40 * 2451733 * 2
def baseEnd_2451733 : Nat := 1258917465489761317062191

theorem tailTrace_2451733 : CollatzResearch.WordTrace tailWord_2451733 prefixEnd_2451733 1258917465489761317062191 := by
  unfold tailWord_2451733
  simp only [CollatzResearch.WordTrace]
  refine ⟨89422048826797538505295853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59614699217865025670197235 89422048826797538505295853)
  ·
    refine ⟨33533268310049076939485945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89422048826797538505295853 33533268310049076939485945)
    ·
      refine ⟨25149951232536807704614459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33533268310049076939485945 25149951232536807704614459)
      ·
        refine ⟨37724926848805211556921689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25149951232536807704614459 37724926848805211556921689)
        ·
          refine ⟨28293695136603908667691267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37724926848805211556921689 28293695136603908667691267)
          ·
            refine ⟨42440542704905863001536901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28293695136603908667691267 42440542704905863001536901)
            ·
              refine ⟨7957601757169849312788169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42440542704905863001536901 7957601757169849312788169)
              ·
                refine ⟨5968201317877386984591127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7957601757169849312788169 5968201317877386984591127)
                ·
                  refine ⟨8952301976816080476886691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5968201317877386984591127 8952301976816080476886691)
                  ·
                    refine ⟨13428452965224120715330037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8952301976816080476886691 13428452965224120715330037)
                    ·
                      refine ⟨1258917465489761317062191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13428452965224120715330037 1258917465489761317062191)
                      ·
                        rfl

theorem cell23_2451733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_2451733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451733 prefixEnd_2451733 := by exact prefixLift 2451733
  have htrace : WordTrace (prefixWord ++ tailWord_2451733) baseStart_2451733 baseEnd_2451733 := by
    simpa [prefixWord, tailWord_2451733, baseEnd_2451733] using wordTrace_append hprefix tailTrace_2451733
  have hstable : (prefixWord ++ tailWord_2451733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451733).length < 2 ^ (prefixWord ++ tailWord_2451733).sum := by decide
  have hdescent : baseEnd_2451733 < baseStart_2451733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451743 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 6]
def baseStart_2451743 : Nat := 118140960795 + 2451743 * 2 ^ 59
def prefixEnd_2451743 : Nat := 4983230072969 + 3 ^ 40 * 2451743 * 2
def baseEnd_2451743 : Nat := 1258922600296306277937145

theorem tailTrace_2451743 : CollatzResearch.WordTrace tailWord_2451743 prefixEnd_2451743 1258922600296306277937145 := by
  unfold tailWord_2451743
  simp only [CollatzResearch.WordTrace]
  refine ⟨89422413556761310213159883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59614942371174206808773255 89422413556761310213159883)
  ·
    refine ⟨134133620335141965319739825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89422413556761310213159883 134133620335141965319739825)
    ·
      refine ⟨100600215251356473989804869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134133620335141965319739825 100600215251356473989804869)
      ·
        refine ⟨18862540359629338873088413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100600215251356473989804869 18862540359629338873088413)
        ·
          refine ⟨7073452634861002077408155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18862540359629338873088413 7073452634861002077408155)
          ·
            refine ⟨10610178952291503116112233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7073452634861002077408155 10610178952291503116112233)
            ·
              refine ⟨7957634214218627337084175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10610178952291503116112233 7957634214218627337084175)
              ·
                refine ⟨11936451321327941005626263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7957634214218627337084175 11936451321327941005626263)
                ·
                  refine ⟨17904676981991911508439395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11936451321327941005626263 17904676981991911508439395)
                  ·
                    refine ⟨26857015472987867262659093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17904676981991911508439395 26857015472987867262659093)
                    ·
                      refine ⟨1258922600296306277937145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26857015472987867262659093 1258922600296306277937145)
                      ·
                        rfl

theorem cell23_2451743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_2451743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451743 prefixEnd_2451743 := by exact prefixLift 2451743
  have htrace : WordTrace (prefixWord ++ tailWord_2451743) baseStart_2451743 baseEnd_2451743 := by
    simpa [prefixWord, tailWord_2451743, baseEnd_2451743] using wordTrace_append hprefix tailTrace_2451743
  have hstable : (prefixWord ++ tailWord_2451743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451743).length < 2 ^ (prefixWord ++ tailWord_2451743).sum := by decide
  have hdescent : baseEnd_2451743 < baseStart_2451743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451757 : List Nat := [1, 5, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_2451757 : Nat := 118140960795 + 2451757 * 2 ^ 59
def prefixEnd_2451757 : Nat := 4983230072969 + 3 ^ 40 * 2451757 * 2
def baseEnd_2451757 : Nat := 419643263008489741054027

theorem tailTrace_2451757 : CollatzResearch.WordTrace tailWord_2451757 prefixEnd_2451757 419643263008489741054027 := by
  unfold tailWord_2451757
  simp only [CollatzResearch.WordTrace]
  refine ⟨89422924178710590604169525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59615282785807060402779683 89422924178710590604169525)
  ·
    refine ⟨8383399141754117869140893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89422924178710590604169525 8383399141754117869140893)
    ·
      refine ⟨3143774678157794200927835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8383399141754117869140893 3143774678157794200927835)
      ·
        refine ⟨4715662017236691301391753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3143774678157794200927835 4715662017236691301391753)
        ·
          refine ⟨3536746512927518476043815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4715662017236691301391753 3536746512927518476043815)
          ·
            refine ⟨5305119769391277714065723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3536746512927518476043815 5305119769391277714065723)
            ·
              refine ⟨7957679654086916571098585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5305119769391277714065723 7957679654086916571098585)
              ·
                refine ⟨5968259740565187428323939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7957679654086916571098585 5968259740565187428323939)
                ·
                  refine ⟨8952389610847781142485909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5968259740565187428323939 8952389610847781142485909)
                  ·
                    refine ⟨419643263008489741054027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8952389610847781142485909 419643263008489741054027)
                    ·
                      rfl

theorem cell23_2451757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_2451757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451757 prefixEnd_2451757 := by exact prefixLift 2451757
  have htrace : WordTrace (prefixWord ++ tailWord_2451757) baseStart_2451757 baseEnd_2451757 := by
    simpa [prefixWord, tailWord_2451757, baseEnd_2451757] using wordTrace_append hprefix tailTrace_2451757
  have hstable : (prefixWord ++ tailWord_2451757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451757).length < 2 ^ (prefixWord ++ tailWord_2451757).sum := by decide
  have hdescent : baseEnd_2451757 < baseStart_2451757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451764 : List Nat := [2, 5, 1, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_2451764 : Nat := 118140960795 + 2451764 * 2 ^ 59
def prefixEnd_2451764 : Nat := 4983230072969 + 3 ^ 40 * 2451764 * 2
def baseEnd_2451764 : Nat := 1258933383390050695774549

theorem tailTrace_2451764 : CollatzResearch.WordTrace tailWord_2451764 prefixEnd_2451764 1258933383390050695774549 := by
  unfold tailWord_2451764
  simp only [CollatzResearch.WordTrace]
  refine ⟨44711589744842615399837173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59615452993123487199782897 44711589744842615399837173)
  ·
    refine ⟨4191711538578995193734735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44711589744842615399837173 4191711538578995193734735)
    ·
      refine ⟨6287567307868492790602103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4191711538578995193734735 6287567307868492790602103)
      ·
        refine ⟨9431350961802739185903155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6287567307868492790602103 9431350961802739185903155)
        ·
          refine ⟨14147026442704108778854733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9431350961802739185903155 14147026442704108778854733)
          ·
            refine ⟨5305134916014040792070525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14147026442704108778854733 5305134916014040792070525)
            ·
              refine ⟨1989425593505265297026447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5305134916014040792070525 1989425593505265297026447)
              ·
                refine ⟨2984138390257897945539671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989425593505265297026447 2984138390257897945539671)
                ·
                  refine ⟨4476207585386846918309507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2984138390257897945539671 4476207585386846918309507)
                  ·
                    refine ⟨6714311378080270377464261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4476207585386846918309507 6714311378080270377464261)
                    ·
                      refine ⟨1258933383390050695774549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6714311378080270377464261 1258933383390050695774549)
                      ·
                        rfl

theorem cell23_2451764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_2451764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451764 prefixEnd_2451764 := by exact prefixLift 2451764
  have htrace : WordTrace (prefixWord ++ tailWord_2451764) baseStart_2451764 baseEnd_2451764 := by
    simpa [prefixWord, tailWord_2451764, baseEnd_2451764] using wordTrace_append hprefix tailTrace_2451764
  have hstable : (prefixWord ++ tailWord_2451764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451764).length < 2 ^ (prefixWord ++ tailWord_2451764).sum := by decide
  have hdescent : baseEnd_2451764 < baseStart_2451764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451797 : List Nat := [1, 3, 2, 2, 4, 1, 2, 1, 1, 3, 3]
def baseStart_2451797 : Nat := 118140960795 + 2451797 * 2 ^ 59
def prefixEnd_2451797 : Nat := 4983230072969 + 3 ^ 40 * 2451797 * 2
def baseEnd_2451797 : Nat := 1258950328251649066661897

theorem tailTrace_2451797 : CollatzResearch.WordTrace tailWord_2451797 prefixEnd_2451797 1258950328251649066661897 := by
  unfold tailWord_2451797
  simp only [CollatzResearch.WordTrace]
  refine ⟨89424383098565677435625645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59616255399043784957083763 89424383098565677435625645)
  ·
    refine ⟨33534143661962129038359617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89424383098565677435625645 33534143661962129038359617)
    ·
      refine ⟨25150607746471596778769713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33534143661962129038359617 25150607746471596778769713)
      ·
        refine ⟨18862955809853697584077285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25150607746471596778769713 18862955809853697584077285)
        ·
          refine ⟨3536804214347568297014491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18862955809853697584077285 3536804214347568297014491)
          ·
            refine ⟨5305206321521352445521737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3536804214347568297014491 5305206321521352445521737)
            ·
              refine ⟨3978904741141014334141303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5305206321521352445521737 3978904741141014334141303)
              ·
                refine ⟨5968357111711521501211955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3978904741141014334141303 5968357111711521501211955)
                ·
                  refine ⟨8952535667567282251817933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5968357111711521501211955 8952535667567282251817933)
                  ·
                    refine ⟨3357200875337730844431725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8952535667567282251817933 3357200875337730844431725)
                    ·
                      refine ⟨1258950328251649066661897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3357200875337730844431725 1258950328251649066661897)
                      ·
                        rfl

theorem cell23_2451797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_2451797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451797 prefixEnd_2451797 := by exact prefixLift 2451797
  have htrace : WordTrace (prefixWord ++ tailWord_2451797) baseStart_2451797 baseEnd_2451797 := by
    simpa [prefixWord, tailWord_2451797, baseEnd_2451797] using wordTrace_append hprefix tailTrace_2451797
  have hstable : (prefixWord ++ tailWord_2451797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451797).length < 2 ^ (prefixWord ++ tailWord_2451797).sum := by decide
  have hdescent : baseEnd_2451797 < baseStart_2451797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451823 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 3]
def baseStart_2451823 : Nat := 118140960795 + 2451823 * 2 ^ 59
def prefixEnd_2451823 : Nat := 4983230072969 + 3 ^ 40 * 2451823 * 2
def baseEnd_2451823 : Nat := 1258963678748665964936777

theorem tailTrace_2451823 : CollatzResearch.WordTrace tailWord_2451823 prefixEnd_2451823 1258963678748665964936777 := by
  unfold tailWord_2451823
  simp only [CollatzResearch.WordTrace]
  refine ⟨89425331396471483876072123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59616887597647655917381415 89425331396471483876072123)
  ·
    refine ⟨134137997094707225814108185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89425331396471483876072123 134137997094707225814108185)
    ·
      refine ⟨100603497821030419360581139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134137997094707225814108185 100603497821030419360581139)
      ·
        refine ⟨150905246731545629040871709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100603497821030419360581139 150905246731545629040871709)
        ·
          refine ⟨56589467524329610890326891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150905246731545629040871709 56589467524329610890326891)
          ·
            refine ⟨84884201286494416335490337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56589467524329610890326891 84884201286494416335490337)
            ·
              refine ⟨63663150964870812251617753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84884201286494416335490337 63663150964870812251617753)
              ·
                refine ⟨47747363223653109188713315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63663150964870812251617753 47747363223653109188713315)
                ·
                  refine ⟨71621044835479663783069973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47747363223653109188713315 71621044835479663783069973)
                  ·
                    refine ⟨3357236476663109239831405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71621044835479663783069973 3357236476663109239831405)
                    ·
                      refine ⟨1258963678748665964936777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3357236476663109239831405 1258963678748665964936777)
                      ·
                        rfl

theorem cell23_2451823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 3].length) (baseStart_2451823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451823 prefixEnd_2451823 := by exact prefixLift 2451823
  have htrace : WordTrace (prefixWord ++ tailWord_2451823) baseStart_2451823 baseEnd_2451823 := by
    simpa [prefixWord, tailWord_2451823, baseEnd_2451823] using wordTrace_append hprefix tailTrace_2451823
  have hstable : (prefixWord ++ tailWord_2451823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451823).length < 2 ^ (prefixWord ++ tailWord_2451823).sum := by decide
  have hdescent : baseEnd_2451823 < baseStart_2451823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451824 : List Nat := [2, 1, 1, 1, 4, 3, 4, 1, 1, 3, 2]
def baseStart_2451824 : Nat := 118140960795 + 2451824 * 2 ^ 59
def prefixEnd_2451824 : Nat := 4983230072969 + 3 ^ 40 * 2451824 * 2
def baseEnd_2451824 : Nat := 1258964192229320461024273

theorem tailTrace_2451824 : CollatzResearch.WordTrace tailWord_2451824 prefixEnd_2451824 1258964192229320461024273 := by
  unfold tailWord_2451824
  simp only [CollatzResearch.WordTrace]
  refine ⟨44712683934733930523429263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59616911912978574031239017 44712683934733930523429263)
  ·
    refine ⟨67069025902100895785143895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44712683934733930523429263 67069025902100895785143895)
    ·
      refine ⟨100603538853151343677715843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67069025902100895785143895 100603538853151343677715843)
      ·
        refine ⟨150905308279727015516573765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100603538853151343677715843 150905308279727015516573765)
        ·
          refine ⟨28294745302448815409357581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150905308279727015516573765 28294745302448815409357581)
          ·
            refine ⟨10610529488418305778509093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28294745302448815409357581 10610529488418305778509093)
            ·
              refine ⟨1989474279078432333470455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10610529488418305778509093 1989474279078432333470455)
              ·
                refine ⟨2984211418617648500205683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989474279078432333470455 2984211418617648500205683)
                ·
                  refine ⟨4476317127926472750308525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2984211418617648500205683 4476317127926472750308525)
                  ·
                    refine ⟨1678618922972427281365697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4476317127926472750308525 1678618922972427281365697)
                    ·
                      refine ⟨1258964192229320461024273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1678618922972427281365697 1258964192229320461024273)
                      ·
                        rfl

theorem cell23_2451824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 1, 3, 2].length) (baseStart_2451824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451824 prefixEnd_2451824 := by exact prefixLift 2451824
  have htrace : WordTrace (prefixWord ++ tailWord_2451824) baseStart_2451824 baseEnd_2451824 := by
    simpa [prefixWord, tailWord_2451824, baseEnd_2451824] using wordTrace_append hprefix tailTrace_2451824
  have hstable : (prefixWord ++ tailWord_2451824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451824).length < 2 ^ (prefixWord ++ tailWord_2451824).sum := by decide
  have hdescent : baseEnd_2451824 < baseStart_2451824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451854 : List Nat := [4, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2]
def baseStart_2451854 : Nat := 118140960795 + 2451854 * 2 ^ 59
def prefixEnd_2451854 : Nat := 4983230072969 + 3 ^ 40 * 2451854 * 2
def baseEnd_2451854 : Nat := 1258979596648955343649135

theorem tailTrace_2451854 : CollatzResearch.WordTrace tailWord_2451854 prefixEnd_2451854 1258979596648955343649135 := by
  unfold tailWord_2451854
  simp only [CollatzResearch.WordTrace]
  refine ⟨11178307757419897021306327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59617641372906117446967077 11178307757419897021306327)
  ·
    refine ⟨16767461636129845531959491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11178307757419897021306327 16767461636129845531959491)
    ·
      refine ⟨25151192454194768297939237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16767461636129845531959491 25151192454194768297939237)
      ·
        refine ⟨4715848585161519055863607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25151192454194768297939237 4715848585161519055863607)
        ·
          refine ⟨7073772877742278583795411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4715848585161519055863607 7073772877742278583795411)
          ·
            refine ⟨10610659316613417875693117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7073772877742278583795411 10610659316613417875693117)
            ·
              refine ⟨3978997243730031703384919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10610659316613417875693117 3978997243730031703384919)
              ·
                refine ⟨5968495865595047555077379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3978997243730031703384919 5968495865595047555077379)
                ·
                  refine ⟨8952743798392571332616069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5968495865595047555077379 8952743798392571332616069)
                  ·
                    refine ⟨1678639462198607124865513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8952743798392571332616069 1678639462198607124865513)
                    ·
                      refine ⟨1258979596648955343649135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1678639462198607124865513 1258979596648955343649135)
                      ·
                        rfl

theorem cell23_2451854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_2451854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451854 prefixEnd_2451854 := by exact prefixLift 2451854
  have htrace : WordTrace (prefixWord ++ tailWord_2451854) baseStart_2451854 baseEnd_2451854 := by
    simpa [prefixWord, tailWord_2451854, baseEnd_2451854] using wordTrace_append hprefix tailTrace_2451854
  have hstable : (prefixWord ++ tailWord_2451854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451854).length < 2 ^ (prefixWord ++ tailWord_2451854).sum := by decide
  have hdescent : baseEnd_2451854 < baseStart_2451854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451890 : List Nat := [3, 2, 1, 1, 1, 1, 5, 2, 2, 5]
def baseStart_2451890 : Nat := 118140960795 + 2451890 * 2 ^ 59
def prefixEnd_2451890 : Nat := 4983230072969 + 3 ^ 40 * 2451890 * 2
def baseEnd_2451890 : Nat := 419666027317505734266323

theorem tailTrace_2451890 : CollatzResearch.WordTrace tailWord_2451890 prefixEnd_2451890 419666027317505734266323 := by
  unfold tailWord_2451890
  simp only [CollatzResearch.WordTrace]
  refine ⟨22356943771807188579690281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59618516724819169545840749 22356943771807188579690281)
  ·
    refine ⟨16767707828855391434767711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22356943771807188579690281 16767707828855391434767711)
    ·
      refine ⟨25151561743283087152151567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16767707828855391434767711 25151561743283087152151567)
      ·
        refine ⟨37727342614924630728227351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25151561743283087152151567 37727342614924630728227351)
        ·
          refine ⟨56591013922386946092341027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37727342614924630728227351 56591013922386946092341027)
          ·
            refine ⟨84886520883580419138511541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56591013922386946092341027 84886520883580419138511541)
            ·
              refine ⟨7958111332835664294235457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84886520883580419138511541 7958111332835664294235457)
              ·
                refine ⟨5968583499626748220676593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7958111332835664294235457 5968583499626748220676593)
                ·
                  refine ⟨4476437624720061165507445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5968583499626748220676593 4476437624720061165507445)
                  ·
                    refine ⟨419666027317505734266323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4476437624720061165507445 419666027317505734266323)
                    ·
                      rfl

theorem cell23_2451890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_2451890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451890 prefixEnd_2451890 := by exact prefixLift 2451890
  have htrace : WordTrace (prefixWord ++ tailWord_2451890) baseStart_2451890 baseEnd_2451890 := by
    simpa [prefixWord, tailWord_2451890, baseEnd_2451890] using wordTrace_append hprefix tailTrace_2451890
  have hstable : (prefixWord ++ tailWord_2451890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451890).length < 2 ^ (prefixWord ++ tailWord_2451890).sum := by decide
  have hdescent : baseEnd_2451890 < baseStart_2451890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451900 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_2451900 : Nat := 118140960795 + 2451900 * 2 ^ 59
def prefixEnd_2451900 : Nat := 4983230072969 + 3 ^ 40 * 2451900 * 2
def baseEnd_2451900 : Nat := 1259003216759062163673923

theorem tailTrace_2451900 : CollatzResearch.WordTrace tailWord_2451900 prefixEnd_2451900 1259003216759062163673923 := by
  unfold tailWord_2451900
  simp only [CollatzResearch.WordTrace]
  refine ⟨44714069908596263013312577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59618759878128350684416769 44714069908596263013312577)
  ·
    refine ⟨33535552431447197259984433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44714069908596263013312577 33535552431447197259984433)
    ·
      refine ⟨25151664323585397944988325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33535552431447197259984433 25151664323585397944988325)
      ·
        refine ⟨4715937060672262114685311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25151664323585397944988325 4715937060672262114685311)
        ·
          refine ⟨7073905591008393172027967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4715937060672262114685311 7073905591008393172027967)
          ·
            refine ⟨10610858386512589758041951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7073905591008393172027967 10610858386512589758041951)
            ·
              refine ⟨15916287579768884637062927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10610858386512589758041951 15916287579768884637062927)
              ·
                refine ⟨23874431369653326955594391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15916287579768884637062927 23874431369653326955594391)
                ·
                  refine ⟨35811647054479990433391587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23874431369653326955594391 35811647054479990433391587)
                  ·
                    refine ⟨53717470581719985650087381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35811647054479990433391587 53717470581719985650087381)
                    ·
                      refine ⟨1259003216759062163673923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53717470581719985650087381 1259003216759062163673923)
                      ·
                        rfl

theorem cell23_2451900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_2451900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451900 prefixEnd_2451900 := by exact prefixLift 2451900
  have htrace : WordTrace (prefixWord ++ tailWord_2451900) baseStart_2451900 baseEnd_2451900 := by
    simpa [prefixWord, tailWord_2451900, baseEnd_2451900] using wordTrace_append hprefix tailTrace_2451900
  have hstable : (prefixWord ++ tailWord_2451900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451900).length < 2 ^ (prefixWord ++ tailWord_2451900).sum := by decide
  have hdescent : baseEnd_2451900 < baseStart_2451900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451905 : List Nat := [1, 2, 7, 1, 1, 1, 1, 3, 2, 2, 2]
def baseStart_2451905 : Nat := 118140960795 + 2451905 * 2 ^ 59
def prefixEnd_2451905 : Nat := 4983230072969 + 3 ^ 40 * 2451905 * 2
def baseEnd_2451905 : Nat := 1259005784162334644111401

theorem tailTrace_2451905 : CollatzResearch.WordTrace tailWord_2451905 prefixEnd_2451905 1259005784162334644111401 := by
  unfold tailWord_2451905
  simp only [CollatzResearch.WordTrace]
  refine ⟨89428322182174411880557169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59618881454782941253704779 89428322182174411880557169)
  ·
    refine ⟨67071241636630808910417877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89428322182174411880557169 67071241636630808910417877)
    ·
      refine ⟨1571982225858534583837919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 67071241636630808910417877 1571982225858534583837919)
      ·
        refine ⟨2357973338787801875756879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1571982225858534583837919 2357973338787801875756879)
        ·
          refine ⟨3536960008181702813635319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2357973338787801875756879 3536960008181702813635319)
          ·
            refine ⟨5305440012272554220452979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3536960008181702813635319 5305440012272554220452979)
            ·
              refine ⟨7958160018408831330679469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5305440012272554220452979 7958160018408831330679469)
              ·
                refine ⟨2984310006903311749004801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7958160018408831330679469 2984310006903311749004801)
                ·
                  refine ⟨2238232505177483811753601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2984310006903311749004801 2238232505177483811753601)
                  ·
                    refine ⟨1678674378883112858815201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2238232505177483811753601 1678674378883112858815201)
                    ·
                      refine ⟨1259005784162334644111401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1678674378883112858815201 1259005784162334644111401)
                      ·
                        rfl

theorem cell23_2451905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_2451905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451905 prefixEnd_2451905 := by exact prefixLift 2451905
  have htrace : WordTrace (prefixWord ++ tailWord_2451905) baseStart_2451905 baseEnd_2451905 := by
    simpa [prefixWord, tailWord_2451905, baseEnd_2451905] using wordTrace_append hprefix tailTrace_2451905
  have hstable : (prefixWord ++ tailWord_2451905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451905).length < 2 ^ (prefixWord ++ tailWord_2451905).sum := by decide
  have hdescent : baseEnd_2451905 < baseStart_2451905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451963 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 1, 11]
def baseStart_2451963 : Nat := 118140960795 + 2451963 * 2 ^ 59
def prefixEnd_2451963 : Nat := 4983230072969 + 3 ^ 40 * 2451963 * 2
def baseEnd_2451963 : Nat := 419678522013431805728711

theorem tailTrace_2451963 : CollatzResearch.WordTrace tailWord_2451963 prefixEnd_2451963 419678522013431805728711 := by
  unfold tailWord_2451963
  simp only [CollatzResearch.WordTrace]
  refine ⟨89430437615964287786168543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59620291743976191857445695 89430437615964287786168543)
  ·
    refine ⟨134145656423946431679252815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89430437615964287786168543 134145656423946431679252815)
    ·
      refine ⟨201218484635919647518879223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134145656423946431679252815 201218484635919647518879223)
      ·
        refine ⟨301827726953879471278318835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201218484635919647518879223 301827726953879471278318835)
        ·
          refine ⟨452741590430819206917478253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301827726953879471278318835 452741590430819206917478253)
          ·
            refine ⟨169778096411557202594054345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 452741590430819206917478253 169778096411557202594054345)
            ·
              refine ⟨127333572308667901945540759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169778096411557202594054345 127333572308667901945540759)
              ·
                refine ⟨191000358463001852918311139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127333572308667901945540759 191000358463001852918311139)
                ·
                  refine ⟨286500537694502779377466709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191000358463001852918311139 286500537694502779377466709)
                  ·
                    refine ⟨419678522013431805728711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 286500537694502779377466709 419678522013431805728711)
                    ·
                      rfl

theorem cell23_2451963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 11].length) (baseStart_2451963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451963 prefixEnd_2451963 := by exact prefixLift 2451963
  have htrace : WordTrace (prefixWord ++ tailWord_2451963) baseStart_2451963 baseEnd_2451963 := by
    simpa [prefixWord, tailWord_2451963, baseEnd_2451963] using wordTrace_append hprefix tailTrace_2451963
  have hstable : (prefixWord ++ tailWord_2451963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451963).length < 2 ^ (prefixWord ++ tailWord_2451963).sum := by decide
  have hdescent : baseEnd_2451963 < baseStart_2451963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451981 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_2451981 : Nat := 118140960795 + 2451981 * 2 ^ 59
def prefixEnd_2451981 : Nat := 4983230072969 + 3 ^ 40 * 2451981 * 2
def baseEnd_2451981 : Nat := 1259044808692076346761051

theorem tailTrace_2451981 : CollatzResearch.WordTrace tailWord_2451981 prefixEnd_2451981 1259044808692076346761051 := by
  unfold tailWord_2451981
  simp only [CollatzResearch.WordTrace]
  refine ⟨89431094129899076860323797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59620729419932717906882531 89431094129899076860323797)
  ·
    refine ⟨2096041268669509613913839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 89431094129899076860323797 2096041268669509613913839)
    ·
      refine ⟨3144061903004264420870759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2096041268669509613913839 3144061903004264420870759)
      ·
        refine ⟨4716092854506396631306139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3144061903004264420870759 4716092854506396631306139)
        ·
          refine ⟨7074139281759594946959209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4716092854506396631306139 7074139281759594946959209)
          ·
            refine ⟨5305604461319696210219407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7074139281759594946959209 5305604461319696210219407)
            ·
              refine ⟨7958406691979544315329111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5305604461319696210219407 7958406691979544315329111)
              ·
                refine ⟨11937610037969316472993667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7958406691979544315329111 11937610037969316472993667)
                ·
                  refine ⟨17906415056953974709490501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11937610037969316472993667 17906415056953974709490501)
                  ·
                    refine ⟨3357452823178870258029469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17906415056953974709490501 3357452823178870258029469)
                    ·
                      refine ⟨1259044808692076346761051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3357452823178870258029469 1259044808692076346761051)
                      ·
                        rfl

theorem cell23_2451981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_2451981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451981 prefixEnd_2451981 := by exact prefixLift 2451981
  have htrace : WordTrace (prefixWord ++ tailWord_2451981) baseStart_2451981 baseEnd_2451981 := by
    simpa [prefixWord, tailWord_2451981, baseEnd_2451981] using wordTrace_append hprefix tailTrace_2451981
  have hstable : (prefixWord ++ tailWord_2451981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451981).length < 2 ^ (prefixWord ++ tailWord_2451981).sum := by decide
  have hdescent : baseEnd_2451981 < baseStart_2451981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451987 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 1, 5, 2]
def baseStart_2451987 : Nat := 118140960795 + 2451987 * 2 ^ 59
def prefixEnd_2451987 : Nat := 4983230072969 + 3 ^ 40 * 2451987 * 2
def baseEnd_2451987 : Nat := 1259047889576003323286023

theorem tailTrace_2451987 : CollatzResearch.WordTrace tailWord_2451987 prefixEnd_2451987 1259047889576003323286023 := by
  unfold tailWord_2451987
  simp only [CollatzResearch.WordTrace]
  refine ⟨89431312967877339885042215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59620875311918226590028143 89431312967877339885042215)
  ·
    refine ⟨134146969451816009827563323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89431312967877339885042215 134146969451816009827563323)
    ·
      refine ⟨201220454177724014741344985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134146969451816009827563323 201220454177724014741344985)
      ·
        refine ⟨150915340633293011056008739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201220454177724014741344985 150915340633293011056008739)
        ·
          refine ⟨226373010949939516584013109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150915340633293011056008739 226373010949939516584013109)
          ·
            refine ⟨21222469776556829679751229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 226373010949939516584013109 21222469776556829679751229)
            ·
              refine ⟨7958426166208811129906711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21222469776556829679751229 7958426166208811129906711)
              ·
                refine ⟨11937639249313216694860067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7958426166208811129906711 11937639249313216694860067)
                ·
                  refine ⟨17906458873969825042290101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11937639249313216694860067 17906458873969825042290101)
                  ·
                    refine ⟨1678730519434671097714697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17906458873969825042290101 1678730519434671097714697)
                    ·
                      refine ⟨1259047889576003323286023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1678730519434671097714697 1259047889576003323286023)
                      ·
                        rfl

theorem cell23_2451987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 5, 2].length) (baseStart_2451987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451987 prefixEnd_2451987 := by exact prefixLift 2451987
  have htrace : WordTrace (prefixWord ++ tailWord_2451987) baseStart_2451987 baseEnd_2451987 := by
    simpa [prefixWord, tailWord_2451987, baseEnd_2451987] using wordTrace_append hprefix tailTrace_2451987
  have hstable : (prefixWord ++ tailWord_2451987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451987).length < 2 ^ (prefixWord ++ tailWord_2451987).sum := by decide
  have hdescent : baseEnd_2451987 < baseStart_2451987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2451988 : List Nat := [2, 4, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_2451988 : Nat := 118140960795 + 2451988 * 2 ^ 59
def prefixEnd_2451988 : Nat := 4983230072969 + 3 ^ 40 * 2451988 * 2
def baseEnd_2451988 : Nat := 419682801018885939791173

theorem tailTrace_2451988 : CollatzResearch.WordTrace tailWord_2451988 prefixEnd_2451988 419682801018885939791173 := by
  unfold tailWord_2451988
  simp only [CollatzResearch.WordTrace]
  refine ⟨44715674720436858527914309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59620899627249144703885745 44715674720436858527914309)
  ·
    refine ⟨8384189010081910973983933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44715674720436858527914309 8384189010081910973983933)
    ·
      refine ⟨3144070878780716615243975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8384189010081910973983933 3144070878780716615243975)
      ·
        refine ⟨4716106318171074922865963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3144070878780716615243975 4716106318171074922865963)
        ·
          refine ⟨7074159477256612384298945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4716106318171074922865963 7074159477256612384298945)
          ·
            refine ⟨5305619607942459288224209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7074159477256612384298945 5305619607942459288224209)
            ·
              refine ⟨3979214705956844466168157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5305619607942459288224209 3979214705956844466168157)
              ·
                refine ⟨1492205514733816674813059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3979214705956844466168157 1492205514733816674813059)
                ·
                  refine ⟨2238308272100725012219589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492205514733816674813059 2238308272100725012219589)
                  ·
                    refine ⟨419682801018885939791173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2238308272100725012219589 419682801018885939791173)
                    ·
                      rfl

theorem cell23_2451988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_2451988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2451988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2451988 prefixEnd_2451988 := by exact prefixLift 2451988
  have htrace : WordTrace (prefixWord ++ tailWord_2451988) baseStart_2451988 baseEnd_2451988 := by
    simpa [prefixWord, tailWord_2451988, baseEnd_2451988] using wordTrace_append hprefix tailTrace_2451988
  have hstable : (prefixWord ++ tailWord_2451988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2451988).length < 2 ^ (prefixWord ++ tailWord_2451988).sum := by decide
  have hdescent : baseEnd_2451988 < baseStart_2451988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2451988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452045 : List Nat := [1, 6, 1, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_2452045 : Nat := 118140960795 + 2452045 * 2 ^ 59
def prefixEnd_2452045 : Nat := 4983230072969 + 3 ^ 40 * 2452045 * 2
def baseEnd_2452045 : Nat := 1259077671453964096360757

theorem tailTrace_2452045 : CollatzResearch.WordTrace tailWord_2452045 prefixEnd_2452045 1259077671453964096360757 := by
  unfold tailWord_2452045
  simp only [CollatzResearch.WordTrace]
  refine ⟨89433428401667215790653589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59622285601111477193769059 89433428401667215790653589)
  ·
    refine ⟨4192191956328150740186887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 89433428401667215790653589 4192191956328150740186887)
    ·
      refine ⟨6288287934492226110280331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4192191956328150740186887 6288287934492226110280331)
      ·
        refine ⟨9432431901738339165420497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6288287934492226110280331 9432431901738339165420497)
        ·
          refine ⟨7074323926303754374065373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9432431901738339165420497 7074323926303754374065373)
          ·
            refine ⟨2652871472363907890274515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7074323926303754374065373 2652871472363907890274515)
            ·
              refine ⟨3979307208545861835411773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2652871472363907890274515 3979307208545861835411773)
              ·
                refine ⟨1492240203204698188279415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3979307208545861835411773 1492240203204698188279415)
                ·
                  refine ⟨2238360304807047282419123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492240203204698188279415 2238360304807047282419123)
                  ·
                    refine ⟨3357540457210570923628685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2238360304807047282419123 3357540457210570923628685)
                    ·
                      refine ⟨1259077671453964096360757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3357540457210570923628685 1259077671453964096360757)
                      ·
                        rfl

theorem cell23_2452045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_2452045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452045 prefixEnd_2452045 := by exact prefixLift 2452045
  have htrace : WordTrace (prefixWord ++ tailWord_2452045) baseStart_2452045 baseEnd_2452045 := by
    simpa [prefixWord, tailWord_2452045, baseEnd_2452045] using wordTrace_append hprefix tailTrace_2452045
  have hstable : (prefixWord ++ tailWord_2452045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452045).length < 2 ^ (prefixWord ++ tailWord_2452045).sum := by decide
  have hdescent : baseEnd_2452045 < baseStart_2452045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452062 : List Nat := [4, 4, 1, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_2452062 : Nat := 118140960795 + 2452062 * 2 ^ 59
def prefixEnd_2452062 : Nat := 4983230072969 + 3 ^ 40 * 2452062 * 2
def baseEnd_2452062 : Nat := 1259086400625090529848179

theorem tailTrace_2452062 : CollatzResearch.WordTrace tailWord_2452062 prefixEnd_2452062 1259086400625090529848179 := by
  unfold tailWord_2452062
  simp only [CollatzResearch.WordTrace]
  refine ⟨11179256055325703461752805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59622698961737085129348293 11179256055325703461752805)
  ·
    refine ⟨2096110510373569399078651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11179256055325703461752805 2096110510373569399078651)
    ·
      refine ⟨3144165765560354098617977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2096110510373569399078651 3144165765560354098617977)
      ·
        refine ⟨2358124324170265573963483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3144165765560354098617977 2358124324170265573963483)
        ·
          refine ⟨3537186486255398360945225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2358124324170265573963483 3537186486255398360945225)
          ·
            refine ⟨2652889864691548770708919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3537186486255398360945225 2652889864691548770708919)
            ·
              refine ⟨3979334797037323156063379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2652889864691548770708919 3979334797037323156063379)
              ·
                refine ⟨5969002195555984734095069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3979334797037323156063379 5969002195555984734095069)
                ·
                  refine ⟨2238375823333494275285651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5969002195555984734095069 2238375823333494275285651)
                  ·
                    refine ⟨3357563735000241412928477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2238375823333494275285651 3357563735000241412928477)
                    ·
                      refine ⟨1259086400625090529848179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3357563735000241412928477 1259086400625090529848179)
                      ·
                        rfl

theorem cell23_2452062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_2452062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452062 prefixEnd_2452062 := by exact prefixLift 2452062
  have htrace : WordTrace (prefixWord ++ tailWord_2452062) baseStart_2452062 baseEnd_2452062 := by
    simpa [prefixWord, tailWord_2452062, baseEnd_2452062] using wordTrace_append hprefix tailTrace_2452062
  have hstable : (prefixWord ++ tailWord_2452062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452062).length < 2 ^ (prefixWord ++ tailWord_2452062).sum := by decide
  have hdescent : baseEnd_2452062 < baseStart_2452062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452078 : List Nat := [4, 1, 2, 2, 2, 3, 2, 1, 2, 4]
def baseStart_2452078 : Nat := 118140960795 + 2452078 * 2 ^ 59
def prefixEnd_2452078 : Nat := 4983230072969 + 3 ^ 40 * 2452078 * 2
def baseEnd_2452078 : Nat := 419698205438520822416035

theorem tailTrace_2452078 : CollatzResearch.WordTrace tailWord_2452078 prefixEnd_2452078 419698205438520822416035 := by
  unfold tailWord_2452078
  simp only [CollatzResearch.WordTrace]
  refine ⟨11179329001318457803325611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59623088007031774951069925 11179329001318457803325611)
  ·
    refine ⟨16768993501977686704988417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11179329001318457803325611 16768993501977686704988417)
    ·
      refine ⟨12576745126483265028741313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16768993501977686704988417 12576745126483265028741313)
      ·
        refine ⟨9432558844862448771555985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12576745126483265028741313 9432558844862448771555985)
        ·
          refine ⟨7074419133646836578666989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9432558844862448771555985 7074419133646836578666989)
          ·
            refine ⟨2652907175117563717000121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7074419133646836578666989 2652907175117563717000121)
            ·
              refine ⟨1989680381338172787750091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2652907175117563717000121 1989680381338172787750091)
              ·
                refine ⟨2984520572007259181625137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989680381338172787750091 2984520572007259181625137)
                ·
                  refine ⟨2238390429005444386218853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2984520572007259181625137 2238390429005444386218853)
                  ·
                    refine ⟨419698205438520822416035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2238390429005444386218853 419698205438520822416035)
                    ·
                      rfl

theorem cell23_2452078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_2452078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452078 prefixEnd_2452078 := by exact prefixLift 2452078
  have htrace : WordTrace (prefixWord ++ tailWord_2452078) baseStart_2452078 baseEnd_2452078 := by
    simpa [prefixWord, tailWord_2452078, baseEnd_2452078] using wordTrace_append hprefix tailTrace_2452078
  have hstable : (prefixWord ++ tailWord_2452078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452078).length < 2 ^ (prefixWord ++ tailWord_2452078).sum := by decide
  have hdescent : baseEnd_2452078 < baseStart_2452078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452141 : List Nat := [1, 5, 2, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_2452141 : Nat := 118140960795 + 2452141 * 2 ^ 59
def prefixEnd_2452141 : Nat := 4983230072969 + 3 ^ 40 * 2452141 * 2
def baseEnd_2452141 : Nat := 1259126965596795720760315

theorem tailTrace_2452141 : CollatzResearch.WordTrace tailWord_2452141 prefixEnd_2452141 1259126965596795720760315 := by
  unfold tailWord_2452141
  simp only [CollatzResearch.WordTrace]
  refine ⟨89436929809319424186148277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59624619872879616124098851 89436929809319424186148277)
  ·
    refine ⟨8384712169623696017451401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89436929809319424186148277 8384712169623696017451401)
    ·
      refine ⟨6288534127217772013088551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8384712169623696017451401 6288534127217772013088551)
      ·
        refine ⟨9432801190826658019632827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6288534127217772013088551 9432801190826658019632827)
        ·
          refine ⟨14149201786239987029449241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9432801190826658019632827 14149201786239987029449241)
          ·
            refine ⟨10611901339679990272086931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14149201786239987029449241 10611901339679990272086931)
            ·
              refine ⟨15917852009519985408130397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10611901339679990272086931 15917852009519985408130397)
              ·
                refine ⟨5969194503569994528048899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15917852009519985408130397 5969194503569994528048899)
                ·
                  refine ⟨8953791755354991792073349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5969194503569994528048899 8953791755354991792073349)
                  ·
                    refine ⟨1678835954129060961013753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8953791755354991792073349 1678835954129060961013753)
                    ·
                      refine ⟨1259126965596795720760315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1678835954129060961013753 1259126965596795720760315)
                      ·
                        rfl

theorem cell23_2452141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_2452141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452141 prefixEnd_2452141 := by exact prefixLift 2452141
  have htrace : WordTrace (prefixWord ++ tailWord_2452141) baseStart_2452141 baseEnd_2452141 := by
    simpa [prefixWord, tailWord_2452141, baseEnd_2452141] using wordTrace_append hprefix tailTrace_2452141
  have hstable : (prefixWord ++ tailWord_2452141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452141).length < 2 ^ (prefixWord ++ tailWord_2452141).sum := by decide
  have hdescent : baseEnd_2452141 < baseStart_2452141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452147 : List Nat := [1, 1, 1, 2, 3, 5, 1, 2, 7]
def baseStart_2452147 : Nat := 118140960795 + 2452147 * 2 ^ 59
def prefixEnd_2452147 : Nat := 4983230072969 + 3 ^ 40 * 2452147 * 2
def baseEnd_2452147 : Nat := 139903338497858077476143

theorem tailTrace_2452147 : CollatzResearch.WordTrace tailWord_2452147 prefixEnd_2452147 139903338497858077476143 := by
  unfold tailWord_2452147
  simp only [CollatzResearch.WordTrace]
  refine ⟨89437148647297687210866695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59624765764865124807244463 89437148647297687210866695)
  ·
    refine ⟨134155722970946530816300043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89437148647297687210866695 134155722970946530816300043)
    ·
      refine ⟨201233584456419796224450065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134155722970946530816300043 201233584456419796224450065)
      ·
        refine ⟨150925188342314847168337549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201233584456419796224450065 150925188342314847168337549)
        ·
          refine ⟨56596945628368067688126581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150925188342314847168337549 56596945628368067688126581)
          ·
            refine ⟨5305963652659506345761867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56596945628368067688126581 5305963652659506345761867)
            ·
              refine ⟨7958945478989259518642801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5305963652659506345761867 7958945478989259518642801)
              ·
                refine ⟨5969209109241944638982101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7958945478989259518642801 5969209109241944638982101)
                ·
                  refine ⟨139903338497858077476143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5969209109241944638982101 139903338497858077476143)
                  ·
                    rfl

theorem cell23_2452147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 7].length) (baseStart_2452147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452147 prefixEnd_2452147 := by exact prefixLift 2452147
  have htrace : WordTrace (prefixWord ++ tailWord_2452147) baseStart_2452147 baseEnd_2452147 := by
    simpa [prefixWord, tailWord_2452147, baseEnd_2452147] using wordTrace_append hprefix tailTrace_2452147
  have hstable : (prefixWord ++ tailWord_2452147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452147).length < 2 ^ (prefixWord ++ tailWord_2452147).sum := by decide
  have hdescent : baseEnd_2452147 < baseStart_2452147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452174 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3]
def baseStart_2452174 : Nat := 118140960795 + 2452174 * 2 ^ 59
def prefixEnd_2452174 : Nat := 4983230072969 + 3 ^ 40 * 2452174 * 2
def baseEnd_2452174 : Nat := 1259143910458394091647663

theorem tailTrace_2452174 : CollatzResearch.WordTrace tailWord_2452174 prefixEnd_2452174 1259143910458394091647663 := by
  unfold tailWord_2452174
  simp only [CollatzResearch.WordTrace]
  refine ⟨11179766677274983852762447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59625422278799913881399717 11179766677274983852762447)
  ·
    refine ⟨16769650015912475779143671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11179766677274983852762447 16769650015912475779143671)
    ·
      refine ⟨25154475023868713668715507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16769650015912475779143671 25154475023868713668715507)
      ·
        refine ⟨37731712535803070503073261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25154475023868713668715507 37731712535803070503073261)
        ·
          refine ⟨14149392200926151438652473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37731712535803070503073261 14149392200926151438652473)
          ·
            refine ⟨10612044150694613578989355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14149392200926151438652473 10612044150694613578989355)
            ·
              refine ⟨15918066226041920368484033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10612044150694613578989355 15918066226041920368484033)
              ·
                refine ⟨11938549669531440276363025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15918066226041920368484033 11938549669531440276363025)
                ·
                  refine ⟨8953912252148580207272269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11938549669531440276363025 8953912252148580207272269)
                  ·
                    refine ⟨3357717094555717577727101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8953912252148580207272269 3357717094555717577727101)
                    ·
                      refine ⟨1259143910458394091647663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3357717094555717577727101 1259143910458394091647663)
                      ·
                        rfl

theorem cell23_2452174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_2452174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452174 prefixEnd_2452174 := by exact prefixLift 2452174
  have htrace : WordTrace (prefixWord ++ tailWord_2452174) baseStart_2452174 baseEnd_2452174 := by
    simpa [prefixWord, tailWord_2452174, baseEnd_2452174] using wordTrace_append hprefix tailTrace_2452174
  have hstable : (prefixWord ++ tailWord_2452174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452174).length < 2 ^ (prefixWord ++ tailWord_2452174).sum := by decide
  have hdescent : baseEnd_2452174 < baseStart_2452174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452177 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 4, 5]
def baseStart_2452177 : Nat := 118140960795 + 2452177 * 2 ^ 59
def prefixEnd_2452177 : Nat := 4983230072969 + 3 ^ 40 * 2452177 * 2
def baseEnd_2452177 : Nat := 419715150300119193303383

theorem tailTrace_2452177 : CollatzResearch.WordTrace tailWord_2452177 prefixEnd_2452177 419715150300119193303383 := by
  unfold tailWord_2452177
  simp only [CollatzResearch.WordTrace]
  refine ⟨89438242837189002334458785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59625495224792668222972523 89438242837189002334458785)
  ·
    refine ⟨67078682127891751750844089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89438242837189002334458785 67078682127891751750844089)
    ·
      refine ⟨50309011595918813813133067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67078682127891751750844089 50309011595918813813133067)
      ·
        refine ⟨75463517393878220719699601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50309011595918813813133067 75463517393878220719699601)
        ·
          refine ⟨56597638045408665539774701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75463517393878220719699601 56597638045408665539774701)
          ·
            refine ⟨21224114267028249577415513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56597638045408665539774701 21224114267028249577415513)
            ·
              refine ⟨15918085700271187183061635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21224114267028249577415513 15918085700271187183061635)
              ·
                refine ⟨23877128550406780774592453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15918085700271187183061635 23877128550406780774592453)
                ·
                  refine ⟨4476961603201271395236085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23877128550406780774592453 4476961603201271395236085)
                  ·
                    refine ⟨419715150300119193303383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4476961603201271395236085 419715150300119193303383)
                    ·
                      rfl

theorem cell23_2452177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 5].length) (baseStart_2452177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452177 prefixEnd_2452177 := by exact prefixLift 2452177
  have htrace : WordTrace (prefixWord ++ tailWord_2452177) baseStart_2452177 baseEnd_2452177 := by
    simpa [prefixWord, tailWord_2452177, baseEnd_2452177] using wordTrace_append hprefix tailTrace_2452177
  have hstable : (prefixWord ++ tailWord_2452177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452177).length < 2 ^ (prefixWord ++ tailWord_2452177).sum := by decide
  have hdescent : baseEnd_2452177 < baseStart_2452177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452181 : List Nat := [1, 3, 2, 5, 1, 1, 2, 1, 7]
def baseStart_2452181 : Nat := 118140960795 + 2452181 * 2 ^ 59
def prefixEnd_2452181 : Nat := 4983230072969 + 3 ^ 40 * 2452181 * 2
def baseEnd_2452181 : Nat := 139905278313663951584459

theorem tailTrace_2452181 : CollatzResearch.WordTrace tailWord_2452181 prefixEnd_2452181 139905278313663951584459 := by
  unfold tailWord_2452181
  simp only [CollatzResearch.WordTrace]
  refine ⟨89438388729174511017604397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59625592486116340678402931 89438388729174511017604397)
  ·
    refine ⟨33539395773440441631601649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89438388729174511017604397 33539395773440441631601649)
    ·
      refine ⟨25154546830080331223701237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33539395773440441631601649 25154546830080331223701237)
      ·
        refine ⟨2358238765320031052221991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25154546830080331223701237 2358238765320031052221991)
        ·
          refine ⟨3537358147980046578332987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2358238765320031052221991 3537358147980046578332987)
          ·
            refine ⟨5306037221970069867499481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3537358147980046578332987 5306037221970069867499481)
            ·
              refine ⟨3979527916477552400624611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5306037221970069867499481 3979527916477552400624611)
              ·
                refine ⟨5969291874716328600936917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3979527916477552400624611 5969291874716328600936917)
                ·
                  refine ⟨139905278313663951584459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5969291874716328600936917 139905278313663951584459)
                  ·
                    rfl

theorem cell23_2452181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 7].length) (baseStart_2452181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452181 prefixEnd_2452181 := by exact prefixLift 2452181
  have htrace : WordTrace (prefixWord ++ tailWord_2452181) baseStart_2452181 baseEnd_2452181 := by
    simpa [prefixWord, tailWord_2452181, baseEnd_2452181] using wordTrace_append hprefix tailTrace_2452181
  have hstable : (prefixWord ++ tailWord_2452181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452181).length < 2 ^ (prefixWord ++ tailWord_2452181).sum := by decide
  have hdescent : baseEnd_2452181 < baseStart_2452181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452214 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4]
def baseStart_2452214 : Nat := 118140960795 + 2452214 * 2 ^ 59
def prefixEnd_2452214 : Nat := 4983230072969 + 3 ^ 40 * 2452214 * 2
def baseEnd_2452214 : Nat := 1259164449684573935147479

theorem tailTrace_2452214 : CollatzResearch.WordTrace tailWord_2452214 prefixEnd_2452214 1259164449684573935147479 := by
  unfold tailWord_2452214
  simp only [CollatzResearch.WordTrace]
  refine ⟨5589974521128434853347231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 59626394892036638435703797 5589974521128434853347231)
  ·
    refine ⟨8384961781692652280020847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5589974521128434853347231 8384961781692652280020847)
    ·
      refine ⟨12577442672538978420031271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8384961781692652280020847 12577442672538978420031271)
      ·
        refine ⟨18866164008808467630046907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12577442672538978420031271 18866164008808467630046907)
        ·
          refine ⟨28299246013212701445070361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18866164008808467630046907 28299246013212701445070361)
          ·
            refine ⟨21224434509909526083802771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28299246013212701445070361 21224434509909526083802771)
            ·
              refine ⟨31836651764864289125704157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21224434509909526083802771 31836651764864289125704157)
              ·
                refine ⟨11938744411824108422139059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31836651764864289125704157 11938744411824108422139059)
                ·
                  refine ⟨17908116617736162633208589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11938744411824108422139059 17908116617736162633208589)
                  ·
                    refine ⟨6715543731651060987453221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17908116617736162633208589 6715543731651060987453221)
                    ·
                      refine ⟨1259164449684573935147479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6715543731651060987453221 1259164449684573935147479)
                      ·
                        rfl

theorem cell23_2452214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_2452214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452214 prefixEnd_2452214 := by exact prefixLift 2452214
  have htrace : WordTrace (prefixWord ++ tailWord_2452214) baseStart_2452214 baseEnd_2452214 := by
    simpa [prefixWord, tailWord_2452214, baseEnd_2452214] using wordTrace_append hprefix tailTrace_2452214
  have hstable : (prefixWord ++ tailWord_2452214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452214).length < 2 ^ (prefixWord ++ tailWord_2452214).sum := by decide
  have hdescent : baseEnd_2452214 < baseStart_2452214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452231 : List Nat := [1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_2452231 : Nat := 118140960795 + 2452231 * 2 ^ 59
def prefixEnd_2452231 : Nat := 4983230072969 + 3 ^ 40 * 2452231 * 2
def baseEnd_2452231 : Nat := 1259173178855700368634901

theorem tailTrace_2452231 : CollatzResearch.WordTrace tailWord_2452231 prefixEnd_2452231 1259173178855700368634901 := by
  unfold tailWord_2452231
  simp only [CollatzResearch.WordTrace]
  refine ⟨89440212378993369556924547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59626808252662246371283031 89440212378993369556924547)
  ·
    refine ⟨134160318568490054335386821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89440212378993369556924547 134160318568490054335386821)
    ·
      refine ⟨25155059731591885187885029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134160318568490054335386821 25155059731591885187885029)
      ·
        refine ⟨4716573699673478472728443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25155059731591885187885029 4716573699673478472728443)
        ·
          refine ⟨7074860549510217709092665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4716573699673478472728443 7074860549510217709092665)
          ·
            refine ⟨5306145412132663281819499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7074860549510217709092665 5306145412132663281819499)
            ·
              refine ⟨7959218118198994922729249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5306145412132663281819499 7959218118198994922729249)
              ·
                refine ⟨5969413588649246192046937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7959218118198994922729249 5969413588649246192046937)
                ·
                  refine ⟨4477060191486934644035203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5969413588649246192046937 4477060191486934644035203)
                  ·
                    refine ⟨6715590287230401966052805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4477060191486934644035203 6715590287230401966052805)
                    ·
                      refine ⟨1259173178855700368634901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6715590287230401966052805 1259173178855700368634901)
                      ·
                        rfl

theorem cell23_2452231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_2452231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452231 prefixEnd_2452231 := by exact prefixLift 2452231
  have htrace : WordTrace (prefixWord ++ tailWord_2452231) baseStart_2452231 baseEnd_2452231 := by
    simpa [prefixWord, tailWord_2452231, baseEnd_2452231] using wordTrace_append hprefix tailTrace_2452231
  have hstable : (prefixWord ++ tailWord_2452231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452231).length < 2 ^ (prefixWord ++ tailWord_2452231).sum := by decide
  have hdescent : baseEnd_2452231 < baseStart_2452231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452241 : List Nat := [1, 2, 2, 1, 1, 3, 2, 6, 1, 4]
def baseStart_2452241 : Nat := 118140960795 + 2452241 * 2 ^ 59
def prefixEnd_2452241 : Nat := 4983230072969 + 3 ^ 40 * 2452241 * 2
def baseEnd_2452241 : Nat := 419726104554081776503285

theorem tailTrace_2452241 : CollatzResearch.WordTrace tailWord_2452241 prefixEnd_2452241 419726104554081776503285 := by
  unfold tailWord_2452241
  simp only [CollatzResearch.WordTrace]
  refine ⟨89440577108957141264788577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59627051405971427509859051 89440577108957141264788577)
  ·
    refine ⟨67080432831717855948591433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89440577108957141264788577 67080432831717855948591433)
    ·
      refine ⟨50310324623788391961443575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67080432831717855948591433 50310324623788391961443575)
      ·
        refine ⟨75465486935682587942165363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50310324623788391961443575 75465486935682587942165363)
        ·
          refine ⟨113198230403523881913248045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75465486935682587942165363 113198230403523881913248045)
          ·
            refine ⟨42449336401321455717468017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113198230403523881913248045 42449336401321455717468017)
            ·
              refine ⟨31837002300991091788101013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42449336401321455717468017 31837002300991091788101013)
              ·
                refine ⟨1492359482858957427567235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31837002300991091788101013 1492359482858957427567235)
                ·
                  refine ⟨2238539224288436141350853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492359482858957427567235 2238539224288436141350853)
                  ·
                    refine ⟨419726104554081776503285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2238539224288436141350853 419726104554081776503285)
                    ·
                      rfl

theorem cell23_2452241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 1, 4].length) (baseStart_2452241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452241 prefixEnd_2452241 := by exact prefixLift 2452241
  have htrace : WordTrace (prefixWord ++ tailWord_2452241) baseStart_2452241 baseEnd_2452241 := by
    simpa [prefixWord, tailWord_2452241, baseEnd_2452241] using wordTrace_append hprefix tailTrace_2452241
  have hstable : (prefixWord ++ tailWord_2452241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452241).length < 2 ^ (prefixWord ++ tailWord_2452241).sum := by decide
  have hdescent : baseEnd_2452241 < baseStart_2452241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452291 : List Nat := [1, 1, 1, 3, 1, 4, 1, 4, 2, 3, 2]
def baseStart_2452291 : Nat := 118140960795 + 2452291 * 2 ^ 59
def prefixEnd_2452291 : Nat := 4983230072969 + 3 ^ 40 * 2452291 * 2
def baseEnd_2452291 : Nat := 1259203987694970133884625

theorem tailTrace_2452291 : CollatzResearch.WordTrace tailWord_2452291 prefixEnd_2452291 1259203987694970133884625 := by
  unfold tailWord_2452291
  simp only [CollatzResearch.WordTrace]
  refine ⟨89442400758775999804108727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59628267172517333202739151 89442400758775999804108727)
  ·
    refine ⟨134163601138163999706163091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89442400758775999804108727 134163601138163999706163091)
    ·
      refine ⟨201245401707245999559244637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134163601138163999706163091 201245401707245999559244637)
      ·
        refine ⟨75467025640217249834716739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201245401707245999559244637 75467025640217249834716739)
        ·
          refine ⟨113200538460325874752075109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75467025640217249834716739 113200538460325874752075109)
          ·
            refine ⟨21225100961311101516014083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113200538460325874752075109 21225100961311101516014083)
            ·
              refine ⟨31837651441966652274021125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21225100961311101516014083 31837651441966652274021125)
              ·
                refine ⟨5969559645368747301378961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31837651441966652274021125 5969559645368747301378961)
                ·
                  refine ⟨4477169734026560476034221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5969559645368747301378961 4477169734026560476034221)
                  ·
                    refine ⟨1678938650259960178512833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4477169734026560476034221 1678938650259960178512833)
                    ·
                      refine ⟨1259203987694970133884625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1678938650259960178512833 1259203987694970133884625)
                      ·
                        rfl

theorem cell23_2452291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 3, 2].length) (baseStart_2452291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452291 prefixEnd_2452291 := by exact prefixLift 2452291
  have htrace : WordTrace (prefixWord ++ tailWord_2452291) baseStart_2452291 baseEnd_2452291 := by
    simpa [prefixWord, tailWord_2452291, baseEnd_2452291] using wordTrace_append hprefix tailTrace_2452291
  have hstable : (prefixWord ++ tailWord_2452291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452291).length < 2 ^ (prefixWord ++ tailWord_2452291).sum := by decide
  have hdescent : baseEnd_2452291 < baseStart_2452291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452292 : List Nat := [2, 3, 4, 2, 1, 1, 1, 4, 1, 4]
def baseStart_2452292 : Nat := 118140960795 + 2452292 * 2 ^ 59
def prefixEnd_2452292 : Nat := 4983230072969 + 3 ^ 40 * 2452292 * 2
def baseEnd_2452292 : Nat := 419734833725208209990707

theorem tailTrace_2452292 : CollatzResearch.WordTrace tailWord_2452292 prefixEnd_2452292 419734833725208209990707 := by
  unfold tailWord_2452292
  simp only [CollatzResearch.WordTrace]
  refine ⟨44721218615886188487447565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59628291487848251316596753 44721218615886188487447565)
  ·
    refine ⟨16770456980957320682792837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44721218615886188487447565 16770456980957320682792837)
    ·
      refine ⟨3144460683929497628023657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16770456980957320682792837 3144460683929497628023657)
      ·
        refine ⟨2358345512947123221017743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3144460683929497628023657 2358345512947123221017743)
        ·
          refine ⟨3537518269420684831526615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2358345512947123221017743 3537518269420684831526615)
          ·
            refine ⟨5306277404131027247289923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3537518269420684831526615 5306277404131027247289923)
            ·
              refine ⟨7959416106196540870934885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5306277404131027247289923 7959416106196540870934885)
              ·
                refine ⟨1492390519911851413300291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7959416106196540870934885 1492390519911851413300291)
                ·
                  refine ⟨2238585779867777119950437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492390519911851413300291 2238585779867777119950437)
                  ·
                    refine ⟨419734833725208209990707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2238585779867777119950437 419734833725208209990707)
                    ·
                      rfl

theorem cell23_2452292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_2452292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452292 prefixEnd_2452292 := by exact prefixLift 2452292
  have htrace : WordTrace (prefixWord ++ tailWord_2452292) baseStart_2452292 baseEnd_2452292 := by
    simpa [prefixWord, tailWord_2452292, baseEnd_2452292] using wordTrace_append hprefix tailTrace_2452292
  have hstable : (prefixWord ++ tailWord_2452292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452292).length < 2 ^ (prefixWord ++ tailWord_2452292).sum := by decide
  have hdescent : baseEnd_2452292 < baseStart_2452292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452304 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 4]
def baseStart_2452304 : Nat := 118140960795 + 2452304 * 2 ^ 59
def prefixEnd_2452304 : Nat := 4983230072969 + 3 ^ 40 * 2452304 * 2
def baseEnd_2452304 : Nat := 1259210662943478583022065

theorem tailTrace_2452304 : CollatzResearch.WordTrace tailWord_2452304 prefixEnd_2452304 1259210662943478583022065 := by
  unfold tailWord_2452304
  simp only [CollatzResearch.WordTrace]
  refine ⟨44721437453864451512165983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59628583271819268682887977 44721437453864451512165983)
  ·
    refine ⟨67082156180796677268248975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44721437453864451512165983 67082156180796677268248975)
    ·
      refine ⟨100623234271195015902373463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67082156180796677268248975 100623234271195015902373463)
      ·
        refine ⟨150934851406792523853560195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100623234271195015902373463 150934851406792523853560195)
        ·
          refine ⟨226402277110188785780340293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150934851406792523853560195 226402277110188785780340293)
          ·
            refine ⟨42450426958160397333813805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 226402277110188785780340293 42450426958160397333813805)
            ·
              refine ⟨15918910109310149000180177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42450426958160397333813805 15918910109310149000180177)
              ·
                refine ⟨11939182581982611750135133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15918910109310149000180177 11939182581982611750135133)
                ·
                  refine ⟨4477193468243479406300675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11939182581982611750135133 4477193468243479406300675)
                  ·
                    refine ⟨6715790202365219109451013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4477193468243479406300675 6715790202365219109451013)
                    ·
                      refine ⟨1259210662943478583022065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6715790202365219109451013 1259210662943478583022065)
                      ·
                        rfl

theorem cell23_2452304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 4].length) (baseStart_2452304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452304 prefixEnd_2452304 := by exact prefixLift 2452304
  have htrace : WordTrace (prefixWord ++ tailWord_2452304) baseStart_2452304 baseEnd_2452304 := by
    simpa [prefixWord, tailWord_2452304, baseEnd_2452304] using wordTrace_append hprefix tailTrace_2452304
  have hstable : (prefixWord ++ tailWord_2452304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452304).length < 2 ^ (prefixWord ++ tailWord_2452304).sum := by decide
  have hdescent : baseEnd_2452304 < baseStart_2452304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452314 : List Nat := [3, 1, 1, 2, 1, 4, 1, 3, 1, 6]
def baseStart_2452314 : Nat := 118140960795 + 2452314 * 2 ^ 59
def prefixEnd_2452314 : Nat := 4983230072969 + 3 ^ 40 * 2452314 * 2
def baseEnd_2452314 : Nat := 419738599250007847965673

theorem tailTrace_2452314 : CollatzResearch.WordTrace tailWord_2452314 prefixEnd_2452314 419738599250007847965673 := by
  unfold tailWord_2452314
  simp only [CollatzResearch.WordTrace]
  refine ⟨22360809909423168683048999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59628826425128449821463997 22360809909423168683048999)
  ·
    refine ⟨33541214864134753024573499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22360809909423168683048999 33541214864134753024573499)
    ·
      refine ⟨50311822296202129536860249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33541214864134753024573499 50311822296202129536860249)
      ·
        refine ⟨37733866722151597152645187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50311822296202129536860249 37733866722151597152645187)
        ·
          refine ⟨56600800083227395728967781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37733866722151597152645187 56600800083227395728967781)
          ·
            refine ⟨10612650015605136699181459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56600800083227395728967781 10612650015605136699181459)
            ·
              refine ⟨15918975023407705048772189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10612650015605136699181459 15918975023407705048772189)
              ·
                refine ⟨5969615633777889393289571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15918975023407705048772189 5969615633777889393289571)
                ·
                  refine ⟨8954423450666834089934357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5969615633777889393289571 8954423450666834089934357)
                  ·
                    refine ⟨419738599250007847965673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8954423450666834089934357 419738599250007847965673)
                    ·
                      rfl

theorem cell23_2452314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_2452314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452314 prefixEnd_2452314 := by exact prefixLift 2452314
  have htrace : WordTrace (prefixWord ++ tailWord_2452314) baseStart_2452314 baseEnd_2452314 := by
    simpa [prefixWord, tailWord_2452314, baseEnd_2452314] using wordTrace_append hprefix tailTrace_2452314
  have hstable : (prefixWord ++ tailWord_2452314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452314).length < 2 ^ (prefixWord ++ tailWord_2452314).sum := by decide
  have hdescent : baseEnd_2452314 < baseStart_2452314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452338 : List Nat := [3, 2, 1, 2, 1, 1, 6, 1, 1, 1, 4]
def baseStart_2452338 : Nat := 118140960795 + 2452338 * 2 ^ 59
def prefixEnd_2452338 : Nat := 4983230072969 + 3 ^ 40 * 2452338 * 2
def baseEnd_2452338 : Nat := 1259228121285731449996909

theorem tailTrace_2452338 : CollatzResearch.WordTrace tailWord_2452338 prefixEnd_2452338 1259228121285731449996909 := by
  unfold tailWord_2452338
  simp only [CollatzResearch.WordTrace]
  refine ⟨22361028747401431707767417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59629409993070484554046445 22361028747401431707767417)
  ·
    refine ⟨16770771560551073780825563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22361028747401431707767417 16770771560551073780825563)
    ·
      refine ⟨25156157340826610671238345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16770771560551073780825563 25156157340826610671238345)
      ·
        refine ⟨18867118005619958003428759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25156157340826610671238345 18867118005619958003428759)
        ·
          refine ⟨28300677008429937005143139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18867118005619958003428759 28300677008429937005143139)
          ·
            refine ⟨42451015512644905507714709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28300677008429937005143139 42451015512644905507714709)
            ·
              refine ⟨1989891352155229945674127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42451015512644905507714709 1989891352155229945674127)
              ·
                refine ⟨2984837028232844918511191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989891352155229945674127 2984837028232844918511191)
                ·
                  refine ⟨4477255542349267377766787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2984837028232844918511191 4477255542349267377766787)
                  ·
                    refine ⟨6715883313523901066650181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4477255542349267377766787 6715883313523901066650181)
                    ·
                      refine ⟨1259228121285731449996909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6715883313523901066650181 1259228121285731449996909)
                      ·
                        rfl

theorem cell23_2452338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_2452338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452338 prefixEnd_2452338 := by exact prefixLift 2452338
  have htrace : WordTrace (prefixWord ++ tailWord_2452338) baseStart_2452338 baseEnd_2452338 := by
    simpa [prefixWord, tailWord_2452338, baseEnd_2452338] using wordTrace_append hprefix tailTrace_2452338
  have hstable : (prefixWord ++ tailWord_2452338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452338).length < 2 ^ (prefixWord ++ tailWord_2452338).sum := by decide
  have hdescent : baseEnd_2452338 < baseStart_2452338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452355 : List Nat := [1, 1, 1, 3, 4, 1, 1, 6, 1, 2, 2]
def baseStart_2452355 : Nat := 118140960795 + 2452355 * 2 ^ 59
def prefixEnd_2452355 : Nat := 4983230072969 + 3 ^ 40 * 2452355 * 2
def baseEnd_2452355 : Nat := 1259236850456857883484331

theorem tailTrace_2452355 : CollatzResearch.WordTrace tailWord_2452355 prefixEnd_2452355 1259236850456857883484331 := by
  unfold tailWord_2452355
  simp only [CollatzResearch.WordTrace]
  refine ⟨89444735030544138734438519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59629823353696092489625679 89444735030544138734438519)
  ·
    refine ⟨134167102545816208101657779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89444735030544138734438519 134167102545816208101657779)
    ·
      refine ⟨201250653818724312152486669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134167102545816208101657779 201250653818724312152486669)
      ·
        refine ⟨75468995182021617057182501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201250653818724312152486669 75468995182021617057182501)
        ·
          refine ⟨14150436596629053198221719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75468995182021617057182501 14150436596629053198221719)
          ·
            refine ⟨21225654894943579797332579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14150436596629053198221719 21225654894943579797332579)
            ·
              refine ⟨31838482342415369695998869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21225654894943579797332579 31838482342415369695998869)
              ·
                refine ⟨1492428859800720454499947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31838482342415369695998869 1492428859800720454499947)
                ·
                  refine ⟨2238643289701080681749921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492428859800720454499947 2238643289701080681749921)
                  ·
                    refine ⟨1678982467275810511312441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2238643289701080681749921 1678982467275810511312441)
                    ·
                      refine ⟨1259236850456857883484331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1678982467275810511312441 1259236850456857883484331)
                      ·
                        rfl

theorem cell23_2452355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6, 1, 2, 2].length) (baseStart_2452355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452355 prefixEnd_2452355 := by exact prefixLift 2452355
  have htrace : WordTrace (prefixWord ++ tailWord_2452355) baseStart_2452355 baseEnd_2452355 := by
    simpa [prefixWord, tailWord_2452355, baseEnd_2452355] using wordTrace_append hprefix tailTrace_2452355
  have hstable : (prefixWord ++ tailWord_2452355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452355).length < 2 ^ (prefixWord ++ tailWord_2452355).sum := by decide
  have hdescent : baseEnd_2452355 < baseStart_2452355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452378 : List Nat := [3, 1, 1, 4, 3, 2, 2, 7]
def baseStart_2452378 : Nat := 118140960795 + 2452378 * 2 ^ 59
def prefixEnd_2452378 : Nat := 4983230072969 + 3 ^ 40 * 2452378 * 2
def baseEnd_2452378 : Nat := 46638839278218936796175

theorem tailTrace_2452378 : CollatzResearch.WordTrace tailWord_2452378 prefixEnd_2452378 46638839278218936796175 := by
  unfold tailWord_2452378
  simp only [CollatzResearch.WordTrace]
  refine ⟨22361393477365203415631447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59630382606307209108350525 22361393477365203415631447)
  ·
    refine ⟨33542090216047805123447171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22361393477365203415631447 33542090216047805123447171)
    ·
      refine ⟨50313135324071707685170757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33542090216047805123447171 50313135324071707685170757)
      ·
        refine ⟨9433712873263445190969517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50313135324071707685170757 9433712873263445190969517)
        ·
          refine ⟨3537642327473791946613569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9433712873263445190969517 3537642327473791946613569)
          ·
            refine ⟨2653231745605343959960177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3537642327473791946613569 2653231745605343959960177)
            ·
              refine ⟨1989923809204007969970133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2653231745605343959960177 1989923809204007969970133)
              ·
                refine ⟨46638839278218936796175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1989923809204007969970133 46638839278218936796175)
                ·
                  rfl

theorem cell23_2452378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 7].length) (baseStart_2452378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452378 prefixEnd_2452378 := by exact prefixLift 2452378
  have htrace : WordTrace (prefixWord ++ tailWord_2452378) baseStart_2452378 baseEnd_2452378 := by
    simpa [prefixWord, tailWord_2452378, baseEnd_2452378] using wordTrace_append hprefix tailTrace_2452378
  have hstable : (prefixWord ++ tailWord_2452378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452378).length < 2 ^ (prefixWord ++ tailWord_2452378).sum := by decide
  have hdescent : baseEnd_2452378 < baseStart_2452378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452384 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 5]
def baseStart_2452384 : Nat := 118140960795 + 2452384 * 2 ^ 59
def prefixEnd_2452384 : Nat := 4983230072969 + 3 ^ 40 * 2452384 * 2
def baseEnd_2452384 : Nat := 1259251741395838270021697

theorem tailTrace_2452384 : CollatzResearch.WordTrace tailWord_2452384 prefixEnd_2452384 1259251741395838270021697 := by
  unfold tailWord_2452384
  simp only [CollatzResearch.WordTrace]
  refine ⟨44722896373719538343622103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59630528498292717791496137 44722896373719538343622103)
  ·
    refine ⟨67084344560579307515433155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44722896373719538343622103 67084344560579307515433155)
    ·
      refine ⟨100626516840868961273149733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67084344560579307515433155 100626516840868961273149733)
      ·
        refine ⟨18867471907662930238715575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100626516840868961273149733 18867471907662930238715575)
        ·
          refine ⟨28301207861494395358073363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18867471907662930238715575 28301207861494395358073363)
          ·
            refine ⟨42451811792241593037110045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28301207861494395358073363 42451811792241593037110045)
            ·
              refine ⟨15919429422090597388916267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42451811792241593037110045 15919429422090597388916267)
              ·
                refine ⟨23879144133135896083374401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15919429422090597388916267 23879144133135896083374401)
                ·
                  refine ⟨17909358099851922062530801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23879144133135896083374401 17909358099851922062530801)
                  ·
                    refine ⟨13432018574888941546898101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17909358099851922062530801 13432018574888941546898101)
                    ·
                      refine ⟨1259251741395838270021697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13432018574888941546898101 1259251741395838270021697)
                      ·
                        rfl

theorem cell23_2452384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_2452384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452384 prefixEnd_2452384 := by exact prefixLift 2452384
  have htrace : WordTrace (prefixWord ++ tailWord_2452384) baseStart_2452384 baseEnd_2452384 := by
    simpa [prefixWord, tailWord_2452384, baseEnd_2452384] using wordTrace_append hprefix tailTrace_2452384
  have hstable : (prefixWord ++ tailWord_2452384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452384).length < 2 ^ (prefixWord ++ tailWord_2452384).sum := by decide
  have hdescent : baseEnd_2452384 < baseStart_2452384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452428 : List Nat := [2, 2, 1, 4, 1, 1, 2, 3, 1, 4, 2]
def baseStart_2452428 : Nat := 118140960795 + 2452428 * 2 ^ 59
def prefixEnd_2452428 : Nat := 4983230072969 + 3 ^ 40 * 2452428 * 2
def baseEnd_2452428 : Nat := 1259274334544636097871495

theorem tailTrace_2452428 : CollatzResearch.WordTrace tailWord_2452428 prefixEnd_2452428 1259274334544636097871495 := by
  unfold tailWord_2452428
  simp only [CollatzResearch.WordTrace]
  refine ⟨44723698779639836100922969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59631598372853114801230625 44723698779639836100922969)
  ·
    refine ⟨33542774084729877075692227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44723698779639836100922969 33542774084729877075692227)
    ·
      refine ⟨50314161127094815613538341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33542774084729877075692227 50314161127094815613538341)
      ·
        refine ⟨9433905211330277927538439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50314161127094815613538341 9433905211330277927538439)
        ·
          refine ⟨14150857816995416891307659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9433905211330277927538439 14150857816995416891307659)
          ·
            refine ⟨21226286725493125336961489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14150857816995416891307659 21226286725493125336961489)
            ·
              refine ⟨15919715044119844002721117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21226286725493125336961489 15919715044119844002721117)
              ·
                refine ⟨5969893141544941501020419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15919715044119844002721117 5969893141544941501020419)
                ·
                  refine ⟨8954839712317412251530629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5969893141544941501020419 8954839712317412251530629)
                  ·
                    refine ⟨1679032446059514797161993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8954839712317412251530629 1679032446059514797161993)
                    ·
                      refine ⟨1259274334544636097871495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1679032446059514797161993 1259274334544636097871495)
                      ·
                        rfl

theorem cell23_2452428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_2452428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452428 prefixEnd_2452428 := by exact prefixLift 2452428
  have htrace : WordTrace (prefixWord ++ tailWord_2452428) baseStart_2452428 baseEnd_2452428 := by
    simpa [prefixWord, tailWord_2452428, baseEnd_2452428] using wordTrace_append hprefix tailTrace_2452428
  have hstable : (prefixWord ++ tailWord_2452428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452428).length < 2 ^ (prefixWord ++ tailWord_2452428).sum := by decide
  have hdescent : baseEnd_2452428 < baseStart_2452428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452445 : List Nat := [1, 4, 3, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_2452445 : Nat := 118140960795 + 2452445 * 2 ^ 59
def prefixEnd_2452445 : Nat := 4983230072969 + 3 ^ 40 * 2452445 * 2
def baseEnd_2452445 : Nat := 1259283063715762531358917

theorem tailTrace_2452445 : CollatzResearch.WordTrace tailWord_2452445 prefixEnd_2452445 1259283063715762531358917 := by
  unfold tailWord_2452445
  simp only [CollatzResearch.WordTrace]
  refine ⟨89448017600218084105214789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59632011733478722736809859 89448017600218084105214789)
  ·
    refine ⟨16771503300040890769727773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89448017600218084105214789 16771503300040890769727773)
    ·
      refine ⟨6289313737515334038647915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16771503300040890769727773 6289313737515334038647915)
      ·
        refine ⟨9433970606273001057971873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6289313737515334038647915 9433970606273001057971873)
        ·
          refine ⟨7075477954704750793478905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9433970606273001057971873 7075477954704750793478905)
          ·
            refine ⟨5306608466028563095109179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7075477954704750793478905 5306608466028563095109179)
            ·
              refine ⟨7959912699042844642663769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5306608466028563095109179 7959912699042844642663769)
              ·
                refine ⟨5969934524282133481997827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7959912699042844642663769 5969934524282133481997827)
                ·
                  refine ⟨8954901786423200222996741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5969934524282133481997827 8954901786423200222996741)
                  ·
                    refine ⟨1679044084954350041811889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8954901786423200222996741 1679044084954350041811889)
                    ·
                      refine ⟨1259283063715762531358917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1679044084954350041811889 1259283063715762531358917)
                      ·
                        rfl

theorem cell23_2452445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_2452445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452445 prefixEnd_2452445 := by exact prefixLift 2452445
  have htrace : WordTrace (prefixWord ++ tailWord_2452445) baseStart_2452445 baseEnd_2452445 := by
    simpa [prefixWord, tailWord_2452445, baseEnd_2452445] using wordTrace_append hprefix tailTrace_2452445
  have hstable : (prefixWord ++ tailWord_2452445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452445).length < 2 ^ (prefixWord ++ tailWord_2452445).sum := by decide
  have hdescent : baseEnd_2452445 < baseStart_2452445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452464 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 3, 7]
def baseStart_2452464 : Nat := 118140960795 + 2452464 * 2 ^ 59
def prefixEnd_2452464 : Nat := 4983230072969 + 3 ^ 40 * 2452464 * 2
def baseEnd_2452464 : Nat := 419764273282732652340443

theorem tailTrace_2452464 : CollatzResearch.WordTrace tailWord_2452464 prefixEnd_2452464 419764273282732652340443 := by
  unfold tailWord_2452464
  simp only [CollatzResearch.WordTrace]
  refine ⟨44724355293574625175078223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59632473724766166900104297 44724355293574625175078223)
  ·
    refine ⟨67086532940361937762617335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44724355293574625175078223 67086532940361937762617335)
    ·
      refine ⟨100629799410542906643926003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67086532940361937762617335 100629799410542906643926003)
      ·
        refine ⟨150944699115814359965889005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100629799410542906643926003 150944699115814359965889005)
        ·
          refine ⟨56604262168430384987208377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150944699115814359965889005 56604262168430384987208377)
          ·
            refine ⟨42453196626322788740406283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56604262168430384987208377 42453196626322788740406283)
            ·
              refine ⟨63679794939484183110609425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42453196626322788740406283 63679794939484183110609425)
              ·
                refine ⟨47759846204613137332957069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63679794939484183110609425 47759846204613137332957069)
                ·
                  refine ⟨17909942326729926499858901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47759846204613137332957069 17909942326729926499858901)
                  ·
                    refine ⟨419764273282732652340443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17909942326729926499858901 419764273282732652340443)
                    ·
                      rfl

theorem cell23_2452464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 3, 7].length) (baseStart_2452464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452464 prefixEnd_2452464 := by exact prefixLift 2452464
  have htrace : WordTrace (prefixWord ++ tailWord_2452464) baseStart_2452464 baseEnd_2452464 := by
    simpa [prefixWord, tailWord_2452464, baseEnd_2452464] using wordTrace_append hprefix tailTrace_2452464
  have hstable : (prefixWord ++ tailWord_2452464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452464).length < 2 ^ (prefixWord ++ tailWord_2452464).sum := by decide
  have hdescent : baseEnd_2452464 < baseStart_2452464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452528 : List Nat := [2, 1, 1, 1, 2, 4, 4, 1, 3, 4]
def baseStart_2452528 : Nat := 118140960795 + 2452528 * 2 ^ 59
def prefixEnd_2452528 : Nat := 4983230072969 + 3 ^ 40 * 2452528 * 2
def baseEnd_2452528 : Nat := 419775227536695235540345

theorem tailTrace_2452528 : CollatzResearch.WordTrace tailWord_2452528 prefixEnd_2452528 419775227536695235540345 := by
  unfold tailWord_2452528
  simp only [CollatzResearch.WordTrace]
  refine ⟨44725522429458694640243119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59634029905944926186990825 44725522429458694640243119)
  ·
    refine ⟨67088283644188041960364679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44725522429458694640243119 67088283644188041960364679)
    ·
      refine ⟨100632425466282062940547019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67088283644188041960364679 100632425466282062940547019)
      ·
        refine ⟨150948638199423094410820529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100632425466282062940547019 150948638199423094410820529)
        ·
          refine ⟨113211478649567320808115397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150948638199423094410820529 113211478649567320808115397)
          ·
            refine ⟨21227152246793872651521637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113211478649567320808115397 21227152246793872651521637)
            ·
              refine ⟨3980091046273851122160307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21227152246793872651521637 3980091046273851122160307)
              ·
                refine ⟨5970136569410776683240461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3980091046273851122160307 5970136569410776683240461)
                ·
                  refine ⟨2238801213529041256215173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5970136569410776683240461 2238801213529041256215173)
                  ·
                    refine ⟨419775227536695235540345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2238801213529041256215173 419775227536695235540345)
                    ·
                      rfl

theorem cell23_2452528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 3, 4].length) (baseStart_2452528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452528 prefixEnd_2452528 := by exact prefixLift 2452528
  have htrace : WordTrace (prefixWord ++ tailWord_2452528) baseStart_2452528 baseEnd_2452528 := by
    simpa [prefixWord, tailWord_2452528, baseEnd_2452528] using wordTrace_append hprefix tailTrace_2452528
  have hstable : (prefixWord ++ tailWord_2452528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452528).length < 2 ^ (prefixWord ++ tailWord_2452528).sum := by decide
  have hdescent : baseEnd_2452528 < baseStart_2452528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452562 : List Nat := [3, 2, 2, 1, 3, 1, 3, 3, 1, 4]
def baseStart_2452562 : Nat := 118140960795 + 2452562 * 2 ^ 59
def prefixEnd_2452562 : Nat := 4983230072969 + 3 ^ 40 * 2452562 * 2
def baseEnd_2452562 : Nat := 419781046984112857865293

theorem tailTrace_2452562 : CollatzResearch.WordTrace tailWord_2452562 prefixEnd_2452562 419781046984112857865293 := by
  unfold tailWord_2452562
  simp only [CollatzResearch.WordTrace]
  refine ⟨22363071235198553271805985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 59634856627196142058149293 22363071235198553271805985)
  ·
    refine ⟨16772303426398914953854489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22363071235198553271805985 16772303426398914953854489)
    ·
      refine ⟨12579227569799186215390867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16772303426398914953854489 12579227569799186215390867)
      ·
        refine ⟨18868841354698779323086301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12579227569799186215390867 18868841354698779323086301)
        ·
          refine ⟨7075815508012042246157363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18868841354698779323086301 7075815508012042246157363)
          ·
            refine ⟨10613723262018063369236045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7075815508012042246157363 10613723262018063369236045)
            ·
              refine ⟨3980146223256773763463517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10613723262018063369236045 3980146223256773763463517)
              ·
                refine ⟨1492554833721290161298819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3980146223256773763463517 1492554833721290161298819)
                ·
                  refine ⟨2238832250581935241948229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1492554833721290161298819 2238832250581935241948229)
                  ·
                    refine ⟨419781046984112857865293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2238832250581935241948229 419781046984112857865293)
                    ·
                      rfl

theorem cell23_2452562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_2452562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452562 prefixEnd_2452562 := by exact prefixLift 2452562
  have htrace : WordTrace (prefixWord ++ tailWord_2452562) baseStart_2452562 baseEnd_2452562 := by
    simpa [prefixWord, tailWord_2452562, baseEnd_2452562] using wordTrace_append hprefix tailTrace_2452562
  have hstable : (prefixWord ++ tailWord_2452562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452562).length < 2 ^ (prefixWord ++ tailWord_2452562).sum := by decide
  have hdescent : baseEnd_2452562 < baseStart_2452562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452585 : List Nat := [1, 2, 1, 1, 1, 6, 3, 1, 3, 1, 3]
def baseStart_2452585 : Nat := 118140960795 + 2452585 * 2 ^ 59
def prefixEnd_2452585 : Nat := 4983230072969 + 3 ^ 40 * 2452585 * 2
def baseEnd_2452585 : Nat := 1259354951007391983608273

theorem tailTrace_2452585 : CollatzResearch.WordTrace tailWord_2452585 prefixEnd_2452585 1259354951007391983608273 := by
  unfold tailWord_2452585
  simp only [CollatzResearch.WordTrace]
  refine ⟨89453123819710888015311209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 59635415879807258676874139 89453123819710888015311209)
  ·
    refine ⟨67089842864783166011483407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89453123819710888015311209 67089842864783166011483407)
    ·
      refine ⟨100634764297174749017225111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67089842864783166011483407 100634764297174749017225111)
      ·
        refine ⟨150952146445762123525837667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100634764297174749017225111 150952146445762123525837667)
        ·
          refine ⟨226428219668643185288756501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150952146445762123525837667 226428219668643185288756501)
          ·
            refine ⟨10613822796967649310410461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 226428219668643185288756501 10613822796967649310410461)
            ·
              refine ⟨3980183548862868491403923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10613822796967649310410461 3980183548862868491403923)
              ·
                refine ⟨5970275323294302737105885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3980183548862868491403923 5970275323294302737105885)
                ·
                  refine ⟨2238853246235363526414707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5970275323294302737105885 2238853246235363526414707)
                  ·
                    refine ⟨3358279869353045289622061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2238853246235363526414707 3358279869353045289622061)
                    ·
                      refine ⟨1259354951007391983608273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3358279869353045289622061 1259354951007391983608273)
                      ·
                        rfl

theorem cell23_2452585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 1, 3].length) (baseStart_2452585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452585 prefixEnd_2452585 := by exact prefixLift 2452585
  have htrace : WordTrace (prefixWord ++ tailWord_2452585) baseStart_2452585 baseEnd_2452585 := by
    simpa [prefixWord, tailWord_2452585, baseEnd_2452585] using wordTrace_append hprefix tailTrace_2452585
  have hstable : (prefixWord ++ tailWord_2452585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452585).length < 2 ^ (prefixWord ++ tailWord_2452585).sum := by decide
  have hdescent : baseEnd_2452585 < baseStart_2452585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452606 : List Nat := [4, 2, 4, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_2452606 : Nat := 118140960795 + 2452606 * 2 ^ 59
def prefixEnd_2452606 : Nat := 4983230072969 + 3 ^ 40 * 2452606 * 2
def baseEnd_2452606 : Nat := 1259365734101136401445677

theorem tailTrace_2452606 : CollatzResearch.WordTrace tailWord_2452606 prefixEnd_2452606 1259365734101136401445677 := by
  unfold tailWord_2452606
  simp only [CollatzResearch.WordTrace]
  refine ⟨11181736219079351075228209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 59635926501756539067883781 11181736219079351075228209)
  ·
    refine ⟨8386302164309513306421157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11181736219079351075228209 8386302164309513306421157)
    ·
      refine ⟨1572431655808033744953967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8386302164309513306421157 1572431655808033744953967)
      ·
        refine ⟨2358647483712050617430951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1572431655808033744953967 2358647483712050617430951)
        ·
          refine ⟨3537971225568075926146427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2358647483712050617430951 3537971225568075926146427)
          ·
            refine ⟨5306956838352113889219641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3537971225568075926146427 5306956838352113889219641)
            ·
              refine ⟨3980217628764085416914731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5306956838352113889219641 3980217628764085416914731)
              ·
                refine ⟨5970326443146128125372097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3980217628764085416914731 5970326443146128125372097)
                ·
                  refine ⟨4477744832359596094029073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5970326443146128125372097 4477744832359596094029073)
                  ·
                    refine ⟨3358308624269697070521805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4477744832359596094029073 3358308624269697070521805)
                    ·
                      refine ⟨1259365734101136401445677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3358308624269697070521805 1259365734101136401445677)
                      ·
                        rfl

theorem cell23_2452606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_2452606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452606 prefixEnd_2452606 := by exact prefixLift 2452606
  have htrace : WordTrace (prefixWord ++ tailWord_2452606) baseStart_2452606 baseEnd_2452606 := by
    simpa [prefixWord, tailWord_2452606, baseEnd_2452606] using wordTrace_append hprefix tailTrace_2452606
  have hstable : (prefixWord ++ tailWord_2452606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452606).length < 2 ^ (prefixWord ++ tailWord_2452606).sum := by decide
  have hdescent : baseEnd_2452606 < baseStart_2452606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2452608 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 2, 6, 2]
def baseStart_2452608 : Nat := 118140960795 + 2452608 * 2 ^ 59
def prefixEnd_2452608 : Nat := 4983230072969 + 3 ^ 40 * 2452608 * 2
def baseEnd_2452608 : Nat := 1259366761062445393620667

theorem tailTrace_2452608 : CollatzResearch.WordTrace tailWord_2452608 prefixEnd_2452608 1259366761062445393620667 := by
  unfold tailWord_2452608
  simp only [CollatzResearch.WordTrace]
  refine ⟨44726981349313781471699239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 59635975132418375295598985 44726981349313781471699239)
  ·
    refine ⟨67090472023970672207548859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44726981349313781471699239 67090472023970672207548859)
    ·
      refine ⟨100635708035956008311323289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67090472023970672207548859 100635708035956008311323289)
      ·
        refine ⟨75476781026967006233492467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100635708035956008311323289 75476781026967006233492467)
        ·
          refine ⟨113215171540450509350238701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75476781026967006233492467 113215171540450509350238701)
          ·
            refine ⟨42455689327668941006339513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113215171540450509350238701 42455689327668941006339513)
            ·
              refine ⟨31841766995751705754754635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42455689327668941006339513 31841766995751705754754635)
              ·
                refine ⟨47762650493627558632131953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31841766995751705754754635 47762650493627558632131953)
                ·
                  refine ⟨35821987870220668974098965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47762650493627558632131953 35821987870220668974098965)
                  ·
                    refine ⟨1679155681416593858160889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35821987870220668974098965 1679155681416593858160889)
                    ·
                      refine ⟨1259366761062445393620667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1679155681416593858160889 1259366761062445393620667)
                      ·
                        rfl

theorem cell23_2452608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 2, 6, 2].length) (baseStart_2452608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2452608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2452608 prefixEnd_2452608 := by exact prefixLift 2452608
  have htrace : WordTrace (prefixWord ++ tailWord_2452608) baseStart_2452608 baseEnd_2452608 := by
    simpa [prefixWord, tailWord_2452608, baseEnd_2452608] using wordTrace_append hprefix tailTrace_2452608
  have hstable : (prefixWord ++ tailWord_2452608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2452608).length < 2 ^ (prefixWord ++ tailWord_2452608).sum := by decide
  have hdescent : baseEnd_2452608 < baseStart_2452608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2452608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
