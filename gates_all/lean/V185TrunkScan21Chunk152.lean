import V185TrunkScan21Chunk151

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1853831 : List Nat := [1, 1, 4, 2, 2, 1, 4, 1, 5]
def baseStart_1853831 : Nat := 118140960795 + 1853831 * 2 ^ 59
def prefixEnd_1853831 : Nat := 4983230072969 + 3 ^ 40 * 1853831 * 2
def baseEnd_1853831 : Nat := 423069491202329605060841

theorem tailTrace_1853831 : CollatzResearch.WordTrace tailWord_1853831 prefixEnd_1853831 423069491202329605060841 := by
  unfold tailWord_1853831
  simp only [CollatzResearch.WordTrace]
  refine ⟨67614771346894370973369347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45076514231262913982246231 67614771346894370973369347)
  ·
    refine ⟨101422157020341556460054021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67614771346894370973369347 101422157020341556460054021)
    ·
      refine ⟨19016654441314041836260129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101422157020341556460054021 19016654441314041836260129)
      ·
        refine ⟨14262490830985531377195097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19016654441314041836260129 14262490830985531377195097)
        ·
          refine ⟨10696868123239148532896323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14262490830985531377195097 10696868123239148532896323)
          ·
            refine ⟨16045302184858722799344485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10696868123239148532896323 16045302184858722799344485)
            ·
              refine ⟨3008494159661010524877091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16045302184858722799344485 3008494159661010524877091)
              ·
                refine ⟨4512741239491515787315637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3008494159661010524877091 4512741239491515787315637)
                ·
                  refine ⟨423069491202329605060841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4512741239491515787315637 423069491202329605060841)
                  ·
                    rfl

theorem cell21_1853831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 5].length) (baseStart_1853831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853831 prefixEnd_1853831 := by exact prefixLift 1853831
  have htrace : WordTrace (prefixWord ++ tailWord_1853831) baseStart_1853831 baseEnd_1853831 := by
    simpa [prefixWord, tailWord_1853831, baseEnd_1853831] using wordTrace_append hprefix tailTrace_1853831
  have hstable : (prefixWord ++ tailWord_1853831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853831).length < 2 ^ (prefixWord ++ tailWord_1853831).sum := by decide
  have hdescent : baseEnd_1853831 < baseStart_1853831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1853958 : List Nat := [6, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_1853958 : Nat := 118140960795 + 1853958 * 2 ^ 59
def prefixEnd_1853958 : Nat := 4983230072969 + 3 ^ 40 * 1853958 * 2
def baseEnd_1853958 : Nat := 423098474332605606443915

theorem tailTrace_1853958 : CollatzResearch.WordTrace tailWord_1853958 prefixEnd_1853958 423098474332605606443915 := by
  unfold tailWord_1853958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2113106356794820989476329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45079602278289514442161685 2113106356794820989476329)
  ·
    refine ⟨1584829767596115742107247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2113106356794820989476329 1584829767596115742107247)
    ·
      refine ⟨2377244651394173613160871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1584829767596115742107247 2377244651394173613160871)
      ·
        refine ⟨3565866977091260419741307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2377244651394173613160871 3565866977091260419741307)
        ·
          refine ⟨5348800465636890629611961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3565866977091260419741307 5348800465636890629611961)
          ·
            refine ⟨4011600349227667972208971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5348800465636890629611961 4011600349227667972208971)
            ·
              refine ⟨6017400523841501958313457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4011600349227667972208971 6017400523841501958313457)
              ·
                refine ⟨4513050392881126468735093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6017400523841501958313457 4513050392881126468735093)
                ·
                  refine ⟨423098474332605606443915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4513050392881126468735093 423098474332605606443915)
                  ·
                    rfl

theorem cell21_1853958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_1853958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1853958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1853958 prefixEnd_1853958 := by exact prefixLift 1853958
  have htrace : WordTrace (prefixWord ++ tailWord_1853958) baseStart_1853958 baseEnd_1853958 := by
    simpa [prefixWord, tailWord_1853958, baseEnd_1853958] using wordTrace_append hprefix tailTrace_1853958
  have hstable : (prefixWord ++ tailWord_1853958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1853958).length < 2 ^ (prefixWord ++ tailWord_1853958).sum := by decide
  have hdescent : baseEnd_1853958 < baseStart_1853958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1853958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854020 : List Nat := [2, 3, 5, 1, 1, 2, 2, 5]
def baseStart_1854020 : Nat := 118140960795 + 1854020 * 2 ^ 59
def prefixEnd_1854020 : Nat := 4983230072969 + 3 ^ 40 * 1854020 * 2
def baseEnd_1854020 : Nat := 141037541192435758803485

theorem tailTrace_1854020 : CollatzResearch.WordTrace tailWord_1854020 prefixEnd_1854020 141037541192435758803485 := by
  unfold tailWord_1854020
  simp only [CollatzResearch.WordTrace]
  refine ⟨33810832371604828125999757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45081109828806437501333009 33810832371604828125999757)
  ·
    refine ⟨12679062139351810547249909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33810832371604828125999757 12679062139351810547249909)
    ·
      refine ⟨1188662075564232238804679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12679062139351810547249909 1188662075564232238804679)
      ·
        refine ⟨1782993113346348358207019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188662075564232238804679 1782993113346348358207019)
        ·
          refine ⟨2674489670019522537310529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1782993113346348358207019 2674489670019522537310529)
          ·
            refine ⟨2005867252514641902982897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2674489670019522537310529 2005867252514641902982897)
            ·
              refine ⟨1504400439385981427237173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2005867252514641902982897 1504400439385981427237173)
              ·
                refine ⟨141037541192435758803485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1504400439385981427237173 141037541192435758803485)
                ·
                  rfl

theorem cell21_1854020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 5].length) (baseStart_1854020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1854020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1854020 prefixEnd_1854020 := by exact prefixLift 1854020
  have htrace : WordTrace (prefixWord ++ tailWord_1854020) baseStart_1854020 baseEnd_1854020 := by
    simpa [prefixWord, tailWord_1854020, baseEnd_1854020] using wordTrace_append hprefix tailTrace_1854020
  have hstable : (prefixWord ++ tailWord_1854020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854020).length < 2 ^ (prefixWord ++ tailWord_1854020).sum := by decide
  have hdescent : baseEnd_1854020 < baseStart_1854020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854087 : List Nat := [1, 1, 4, 2, 1, 2, 1, 9]
def baseStart_1854087 : Nat := 118140960795 + 1854087 * 2 ^ 59
def prefixEnd_1854087 : Nat := 4983230072969 + 3 ^ 40 * 1854087 * 2
def baseEnd_1854087 : Nat := 141042637963376682931217

theorem tailTrace_1854087 : CollatzResearch.WordTrace tailWord_1854087 prefixEnd_1854087 141042637963376682931217 := by
  unfold tailWord_1854087
  simp only [CollatzResearch.WordTrace]
  refine ⟨67624108433966926694688515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45082738955977951129792343 67624108433966926694688515)
  ·
    refine ⟨101436162650950390042032773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67624108433966926694688515 101436162650950390042032773)
    ·
      refine ⟨19019280497053198132881145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101436162650950390042032773 19019280497053198132881145)
      ·
        refine ⟨14264460372789898599660859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19019280497053198132881145 14264460372789898599660859)
        ·
          refine ⟨21396690559184847899491289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14264460372789898599660859 21396690559184847899491289)
          ·
            refine ⟨16047517919388635924618467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21396690559184847899491289 16047517919388635924618467)
            ·
              refine ⟨24071276879082953886927701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16047517919388635924618467 24071276879082953886927701)
              ·
                refine ⟨141042637963376682931217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24071276879082953886927701 141042637963376682931217)
                ·
                  rfl

theorem cell21_1854087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 9].length) (baseStart_1854087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1854087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1854087 prefixEnd_1854087 := by exact prefixLift 1854087
  have htrace : WordTrace (prefixWord ++ tailWord_1854087) baseStart_1854087 baseEnd_1854087 := by
    simpa [prefixWord, tailWord_1854087, baseEnd_1854087] using wordTrace_append hprefix tailTrace_1854087
  have hstable : (prefixWord ++ tailWord_1854087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854087).length < 2 ^ (prefixWord ++ tailWord_1854087).sum := by decide
  have hdescent : baseEnd_1854087 < baseStart_1854087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854135 : List Nat := [1, 1, 3, 1, 6, 1, 1, 2, 5]
def baseStart_1854135 : Nat := 118140960795 + 1854135 * 2 ^ 59
def prefixEnd_1854135 : Nat := 4983230072969 + 3 ^ 40 * 1854135 * 2
def baseEnd_1854135 : Nat := 423138868144092631993553

theorem tailTrace_1854135 : CollatzResearch.WordTrace tailWord_1854135 prefixEnd_1854135 423138868144092631993553 := by
  unfold tailWord_1854135
  simp only [CollatzResearch.WordTrace]
  refine ⟨67625859137793030892435859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45083906091862020594957239 67625859137793030892435859)
  ·
    refine ⟨101438788706689546338653789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67625859137793030892435859 101438788706689546338653789)
    ·
      refine ⟨38039545765008579876995171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101438788706689546338653789 38039545765008579876995171)
      ·
        refine ⟨57059318647512869815492757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38039545765008579876995171 57059318647512869815492757)
        ·
          refine ⟨2674655561602165772601223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57059318647512869815492757 2674655561602165772601223)
          ·
            refine ⟨4011983342403248658901835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2674655561602165772601223 4011983342403248658901835)
            ·
              refine ⟨6017975013604872988352753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4011983342403248658901835 6017975013604872988352753)
              ·
                refine ⟨4513481260203654741264565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6017975013604872988352753 4513481260203654741264565)
                ·
                  refine ⟨423138868144092631993553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4513481260203654741264565 423138868144092631993553)
                  ·
                    rfl

theorem cell21_1854135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 5].length) (baseStart_1854135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1854135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1854135 prefixEnd_1854135 := by exact prefixLift 1854135
  have htrace : WordTrace (prefixWord ++ tailWord_1854135) baseStart_1854135 baseEnd_1854135 := by
    simpa [prefixWord, tailWord_1854135, baseEnd_1854135] using wordTrace_append hprefix tailTrace_1854135
  have hstable : (prefixWord ++ tailWord_1854135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854135).length < 2 ^ (prefixWord ++ tailWord_1854135).sum := by decide
  have hdescent : baseEnd_1854135 < baseStart_1854135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854152 : List Nat := [2, 1, 3, 1, 2, 4, 2, 3, 3]
def baseStart_1854152 : Nat := 118140960795 + 1854152 * 2 ^ 59
def prefixEnd_1854152 : Nat := 4983230072969 + 3 ^ 40 * 1854152 * 2
def baseEnd_1854152 : Nat := 423142747775704380210185

theorem tailTrace_1854152 : CollatzResearch.WordTrace tailWord_1854152 prefixEnd_1854152 423142747775704380210185 := by
  unfold tailWord_1854152
  simp only [CollatzResearch.WordTrace]
  refine ⟨33813239589365721397902355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45084319452487628530536473 33813239589365721397902355)
  ·
    refine ⟨50719859384048582096853533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33813239589365721397902355 50719859384048582096853533)
    ·
      refine ⟨19019947269018218286320075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50719859384048582096853533 19019947269018218286320075)
      ·
        refine ⟨28529920903527327429480113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19019947269018218286320075 28529920903527327429480113)
        ·
          refine ⟨21397440677645495572110085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28529920903527327429480113 21397440677645495572110085)
          ·
            refine ⟨4012020127058530419770641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21397440677645495572110085 4012020127058530419770641)
            ·
              refine ⟨3009015095293897814827981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4012020127058530419770641 3009015095293897814827981)
              ·
                refine ⟨1128380660735211680560493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3009015095293897814827981 1128380660735211680560493)
                ·
                  refine ⟨423142747775704380210185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1128380660735211680560493 423142747775704380210185)
                  ·
                    rfl

theorem cell21_1854152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 3].length) (baseStart_1854152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1854152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1854152 prefixEnd_1854152 := by exact prefixLift 1854152
  have htrace : WordTrace (prefixWord ++ tailWord_1854152) baseStart_1854152 baseEnd_1854152 := by
    simpa [prefixWord, tailWord_1854152, baseEnd_1854152] using wordTrace_append hprefix tailTrace_1854152
  have hstable : (prefixWord ++ tailWord_1854152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854152).length < 2 ^ (prefixWord ++ tailWord_1854152).sum := by decide
  have hdescent : baseEnd_1854152 < baseStart_1854152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854239 : List Nat := [1, 1, 2, 4, 2, 2, 1, 8]
def baseStart_1854239 : Nat := 118140960795 + 1854239 * 2 ^ 59
def prefixEnd_1854239 : Nat := 4983230072969 + 3 ^ 40 * 1854239 * 2
def baseEnd_1854239 : Nat := 141054200787003854086669

theorem tailTrace_1854239 : CollatzResearch.WordTrace tailWord_1854239 prefixEnd_1854239 141054200787003854086669 := by
  unfold tailWord_1854239
  simp only [CollatzResearch.WordTrace]
  refine ⟨67629652329416256654221771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45086434886277504436147847 67629652329416256654221771)
  ·
    refine ⟨101444478494124384981332657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67629652329416256654221771 101444478494124384981332657)
    ·
      refine ⟨76083358870593288735999493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101444478494124384981332657 76083358870593288735999493)
      ·
        refine ⟨14265629788236241637999905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76083358870593288735999493 14265629788236241637999905)
        ·
          refine ⟨10699222341177181228499929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14265629788236241637999905 10699222341177181228499929)
          ·
            refine ⟨8024416755882885921374947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10699222341177181228499929 8024416755882885921374947)
            ·
              refine ⟨12036625133824328882062421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8024416755882885921374947 12036625133824328882062421)
              ·
                refine ⟨141054200787003854086669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12036625133824328882062421 141054200787003854086669)
                ·
                  rfl

theorem cell21_1854239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 8].length) (baseStart_1854239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1854239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1854239 prefixEnd_1854239 := by exact prefixLift 1854239
  have htrace : WordTrace (prefixWord ++ tailWord_1854239) baseStart_1854239 baseEnd_1854239 := by
    simpa [prefixWord, tailWord_1854239, baseEnd_1854239] using wordTrace_append hprefix tailTrace_1854239
  have hstable : (prefixWord ++ tailWord_1854239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854239).length < 2 ^ (prefixWord ++ tailWord_1854239).sum := by decide
  have hdescent : baseEnd_1854239 < baseStart_1854239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854242 : List Nat := [3, 3, 1, 1, 2, 3, 1, 3, 4]
def baseStart_1854242 : Nat := 118140960795 + 1854242 * 2 ^ 59
def prefixEnd_1854242 : Nat := 4983230072969 + 3 ^ 40 * 1854242 * 2
def baseEnd_1854242 : Nat := 423163287001884223710001

theorem tailTrace_1854242 : CollatzResearch.WordTrace tailWord_1854242 prefixEnd_1854242 423163287001884223710001 := by
  unfold tailWord_1854242
  simp only [CollatzResearch.WordTrace]
  refine ⟨16907440437101347041645245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45086507832270258777720653 16907440437101347041645245)
  ·
    refine ⟨6340290163913005140616967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16907440437101347041645245 6340290163913005140616967)
    ·
      refine ⟨9510435245869507710925451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6340290163913005140616967 9510435245869507710925451)
      ·
        refine ⟨14265652868804261566388177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9510435245869507710925451 14265652868804261566388177)
        ·
          refine ⟨10699239651603196174791133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14265652868804261566388177 10699239651603196174791133)
          ·
            refine ⟨4012214869351198565546675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10699239651603196174791133 4012214869351198565546675)
            ·
              refine ⟨6018322304026797848320013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012214869351198565546675 6018322304026797848320013)
              ·
                refine ⟨2256870864010049193120005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6018322304026797848320013 2256870864010049193120005)
                ·
                  refine ⟨423163287001884223710001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2256870864010049193120005 423163287001884223710001)
                  ·
                    rfl

theorem cell21_1854242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_1854242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1854242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1854242 prefixEnd_1854242 := by exact prefixLift 1854242
  have htrace : WordTrace (prefixWord ++ tailWord_1854242) baseStart_1854242 baseEnd_1854242 := by
    simpa [prefixWord, tailWord_1854242, baseEnd_1854242] using wordTrace_append hprefix tailTrace_1854242
  have hstable : (prefixWord ++ tailWord_1854242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854242).length < 2 ^ (prefixWord ++ tailWord_1854242).sum := by decide
  have hdescent : baseEnd_1854242 < baseStart_1854242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854273 : List Nat := [1, 2, 5, 3, 2, 8]
def baseStart_1854273 : Nat := 118140960795 + 1854273 * 2 ^ 59
def prefixEnd_1854273 : Nat := 4983230072969 + 3 ^ 40 * 1854273 * 2
def baseEnd_1854273 : Nat := 15672976356453150321973

theorem tailTrace_1854273 : CollatzResearch.WordTrace tailWord_1854273 prefixEnd_1854273 15672976356453150321973 := by
  unfold tailWord_1854273
  simp only [CollatzResearch.WordTrace]
  refine ⟨67630892411293080460959473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45087261607528720307306315 67630892411293080460959473)
  ·
    refine ⟨50723169308469810345719605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67630892411293080460959473 50723169308469810345719605)
    ·
      refine ⟨4755297122669044719911213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50723169308469810345719605 4755297122669044719911213)
      ·
        refine ⟨1783236421000891769966705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4755297122669044719911213 1783236421000891769966705)
        ·
          refine ⟨1337427315750668827475029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1783236421000891769966705 1337427315750668827475029)
          ·
            refine ⟨15672976356453150321973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1337427315750668827475029 15672976356453150321973)
            ·
              rfl

theorem cell21_1854273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 8].length) (baseStart_1854273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1854273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1854273 prefixEnd_1854273 := by exact prefixLift 1854273
  have htrace : WordTrace (prefixWord ++ tailWord_1854273) baseStart_1854273 baseEnd_1854273 := by
    simpa [prefixWord, tailWord_1854273, baseEnd_1854273] using wordTrace_append hprefix tailTrace_1854273
  have hstable : (prefixWord ++ tailWord_1854273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854273).length < 2 ^ (prefixWord ++ tailWord_1854273).sum := by decide
  have hdescent : baseEnd_1854273 < baseStart_1854273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854276 : List Nat := [2, 3, 4, 2, 1, 1, 2, 2, 4]
def baseStart_1854276 : Nat := 118140960795 + 1854276 * 2 ^ 59
def prefixEnd_1854276 : Nat := 4983230072969 + 3 ^ 40 * 1854276 * 2
def baseEnd_1854276 : Nat := 423171046265107720143265

theorem tailTrace_1854276 : CollatzResearch.WordTrace tailWord_1854276 prefixEnd_1854276 423171046265107720143265 := by
  unfold tailWord_1854276
  simp only [CollatzResearch.WordTrace]
  refine ⟨33815500915141105986659341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45087334553521474648879121 33815500915141105986659341)
  ·
    refine ⟨12680812843177914744997253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33815500915141105986659341 12680812843177914744997253)
    ·
      refine ⟨2377652408095859014686985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12680812843177914744997253 2377652408095859014686985)
      ·
        refine ⟨1783239306071894261015239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2377652408095859014686985 1783239306071894261015239)
        ·
          refine ⟨2674858959107841391522859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1783239306071894261015239 2674858959107841391522859)
          ·
            refine ⟨4012288438661762087284289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2674858959107841391522859 4012288438661762087284289)
            ·
              refine ⟨3009216328996321565463217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4012288438661762087284289 3009216328996321565463217)
              ·
                refine ⟨2256912246747241174097413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3009216328996321565463217 2256912246747241174097413)
                ·
                  refine ⟨423171046265107720143265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2256912246747241174097413 423171046265107720143265)
                  ·
                    rfl

theorem cell21_1854276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_1854276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1854276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1854276 prefixEnd_1854276 := by exact prefixLift 1854276
  have htrace : WordTrace (prefixWord ++ tailWord_1854276) baseStart_1854276 baseEnd_1854276 := by
    simpa [prefixWord, tailWord_1854276, baseEnd_1854276] using wordTrace_append hprefix tailTrace_1854276
  have hstable : (prefixWord ++ tailWord_1854276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854276).length < 2 ^ (prefixWord ++ tailWord_1854276).sum := by decide
  have hdescent : baseEnd_1854276 < baseStart_1854276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854397 : List Nat := [1, 4, 1, 2, 4, 1, 3, 2, 3]
def baseStart_1854397 : Nat := 118140960795 + 1854397 * 2 ^ 59
def prefixEnd_1854397 : Nat := 4983230072969 + 3 ^ 40 * 1854397 * 2
def baseEnd_1854397 : Nat := 423198660113638398626351

theorem tailTrace_1854397 : CollatzResearch.WordTrace tailWord_1854397 prefixEnd_1854397 423198660113638398626351 := by
  unfold tailWord_1854397
  simp only [CollatzResearch.WordTrace]
  refine ⟨67635415062843849638473445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45090276708562566425648963 67635415062843849638473445)
  ·
    refine ⟨12681640324283221807213771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67635415062843849638473445 12681640324283221807213771)
    ·
      refine ⟨19022460486424832710820657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12681640324283221807213771 19022460486424832710820657)
      ·
        refine ⟨14266845364818624533115493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19022460486424832710820657 14266845364818624533115493)
        ·
          refine ⟨2675033505903492099959155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14266845364818624533115493 2675033505903492099959155)
          ·
            refine ⟨4012550258855238149938733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675033505903492099959155 4012550258855238149938733)
            ·
              refine ⟨1504706347070714306227025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4012550258855238149938733 1504706347070714306227025)
              ·
                refine ⟨1128529760303035729670269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1504706347070714306227025 1128529760303035729670269)
                ·
                  refine ⟨423198660113638398626351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1128529760303035729670269 423198660113638398626351)
                  ·
                    rfl

theorem cell21_1854397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_1854397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1854397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1854397 prefixEnd_1854397 := by exact prefixLift 1854397
  have htrace : WordTrace (prefixWord ++ tailWord_1854397) baseStart_1854397 baseEnd_1854397 := by
    simpa [prefixWord, tailWord_1854397, baseEnd_1854397] using wordTrace_append hprefix tailTrace_1854397
  have hstable : (prefixWord ++ tailWord_1854397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854397).length < 2 ^ (prefixWord ++ tailWord_1854397).sum := by decide
  have hdescent : baseEnd_1854397 < baseStart_1854397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854408 : List Nat := [2, 1, 3, 1, 5, 1, 2, 6]
def baseStart_1854408 : Nat := 118140960795 + 1854408 * 2 ^ 59
def prefixEnd_1854408 : Nat := 4983230072969 + 3 ^ 40 * 1854408 * 2
def baseEnd_1854408 : Nat := 141067056821168274647665

theorem tailTrace_1854408 : CollatzResearch.WordTrace tailWord_1854408 prefixEnd_1854408 141067056821168274647665 := by
  unfold tailWord_1854408
  simp only [CollatzResearch.WordTrace]
  refine ⟨33817908132901999258561939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45090544177202665678082585 33817908132901999258561939)
  ·
    refine ⟨50726862199352998887842909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33817908132901999258561939 50726862199352998887842909)
    ·
      refine ⟨19022573324757374582941091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50726862199352998887842909 19022573324757374582941091)
      ·
        refine ⟨28533859987136061874411637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19022573324757374582941091 28533859987136061874411637)
        ·
          refine ⟨2675049373794005800726091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28533859987136061874411637 2675049373794005800726091)
          ·
            refine ⟨4012574060691008701089137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675049373794005800726091 4012574060691008701089137)
            ·
              refine ⟨3009430545518256525816853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4012574060691008701089137 3009430545518256525816853)
              ·
                refine ⟨141067056821168274647665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3009430545518256525816853 141067056821168274647665)
                ·
                  rfl

theorem cell21_1854408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 6].length) (baseStart_1854408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1854408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1854408 prefixEnd_1854408 := by exact prefixLift 1854408
  have htrace : WordTrace (prefixWord ++ tailWord_1854408) baseStart_1854408 baseEnd_1854408 := by
    simpa [prefixWord, tailWord_1854408, baseEnd_1854408] using wordTrace_append hprefix tailTrace_1854408
  have hstable : (prefixWord ++ tailWord_1854408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854408).length < 2 ^ (prefixWord ++ tailWord_1854408).sum := by decide
  have hdescent : baseEnd_1854408 < baseStart_1854408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854436 : List Nat := [2, 3, 1, 1, 1, 1, 2, 4, 6]
def baseStart_1854436 : Nat := 118140960795 + 1854436 * 2 ^ 59
def prefixEnd_1854436 : Nat := 4983230072969 + 3 ^ 40 * 1854436 * 2
def baseEnd_1854436 : Nat := 423207560444982997476271

theorem tailTrace_1854436 : CollatzResearch.WordTrace tailWord_1854436 prefixEnd_1854436 423207560444982997476271 := by
  unfold tailWord_1854436
  simp only [CollatzResearch.WordTrace]
  refine ⟨33818418754851279649571581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45091225006468372866095441 33818418754851279649571581)
  ·
    refine ⟨12681907033069229868589343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33818418754851279649571581 12681907033069229868589343)
    ·
      refine ⟨19022860549603844802884015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12681907033069229868589343 19022860549603844802884015)
      ·
        refine ⟨28534290824405767204326023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19022860549603844802884015 28534290824405767204326023)
        ·
          refine ⟨42801436236608650806489035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28534290824405767204326023 42801436236608650806489035)
          ·
            refine ⟨64202154354912976209733553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42801436236608650806489035 64202154354912976209733553)
            ·
              refine ⟨48151615766184732157300165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64202154354912976209733553 48151615766184732157300165)
              ·
                refine ⟨9028427956159637279493781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48151615766184732157300165 9028427956159637279493781)
                ·
                  refine ⟨423207560444982997476271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9028427956159637279493781 423207560444982997476271)
                  ·
                    rfl

theorem cell21_1854436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_1854436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1854436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1854436 prefixEnd_1854436 := by exact prefixLift 1854436
  have htrace : WordTrace (prefixWord ++ tailWord_1854436) baseStart_1854436 baseEnd_1854436 := by
    simpa [prefixWord, tailWord_1854436, baseEnd_1854436] using wordTrace_append hprefix tailTrace_1854436
  have hstable : (prefixWord ++ tailWord_1854436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854436).length < 2 ^ (prefixWord ++ tailWord_1854436).sum := by decide
  have hdescent : baseEnd_1854436 < baseStart_1854436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854512 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 6]
def baseStart_1854512 : Nat := 118140960795 + 1854512 * 2 ^ 59
def prefixEnd_1854512 : Nat := 4983230072969 + 3 ^ 40 * 1854512 * 2
def baseEnd_1854512 : Nat := 423224904680423754209449

theorem tailTrace_1854512 : CollatzResearch.WordTrace tailWord_1854512 prefixEnd_1854512 423224904680423754209449 := by
  unfold tailWord_1854512
  simp only [CollatzResearch.WordTrace]
  refine ⟨33819804728713612139454895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45093072971618149519273193 33819804728713612139454895)
  ·
    refine ⟨50729707093070418209182343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33819804728713612139454895 50729707093070418209182343)
    ·
      refine ⟨76094560639605627313773515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50729707093070418209182343 76094560639605627313773515)
      ·
        refine ⟨114141840959408440970660273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76094560639605627313773515 114141840959408440970660273)
        ·
          refine ⟨85606380719556330727995205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114141840959408440970660273 85606380719556330727995205)
          ·
            refine ⟨16051196384916812011499101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85606380719556330727995205 16051196384916812011499101)
            ·
              refine ⟨6019198644343804504312163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16051196384916812011499101 6019198644343804504312163)
              ·
                refine ⟨9028797966515706756468245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6019198644343804504312163 9028797966515706756468245)
                ·
                  refine ⟨423224904680423754209449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9028797966515706756468245 423224904680423754209449)
                  ·
                    rfl

theorem cell21_1854512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_1854512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1854512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1854512 prefixEnd_1854512 := by exact prefixLift 1854512
  have htrace : WordTrace (prefixWord ++ tailWord_1854512) baseStart_1854512 baseEnd_1854512 := by
    simpa [prefixWord, tailWord_1854512, baseEnd_1854512] using wordTrace_append hprefix tailTrace_1854512
  have hstable : (prefixWord ++ tailWord_1854512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854512).length < 2 ^ (prefixWord ++ tailWord_1854512).sum := by decide
  have hdescent : baseEnd_1854512 < baseStart_1854512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854622 : List Nat := [4, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_1854622 : Nat := 118140960795 + 1854622 * 2 ^ 59
def prefixEnd_1854622 : Nat := 4983230072969 + 3 ^ 40 * 1854622 * 2
def baseEnd_1854622 : Nat := 423250008179088007375891

theorem tailTrace_1854622 : CollatzResearch.WordTrace tailWord_1854622 prefixEnd_1854622 423250008179088007375891 := by
  unfold tailWord_1854622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8455452685878589133176765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45095747658019142043609413 8455452685878589133176765)
  ·
    refine ⟨3170794757204470924941287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8455452685878589133176765 3170794757204470924941287)
    ·
      refine ⟨4756192135806706387411931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3170794757204470924941287 4756192135806706387411931)
      ·
        refine ⟨7134288203710059581117897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4756192135806706387411931 7134288203710059581117897)
        ·
          refine ⟨5350716152782544685838423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7134288203710059581117897 5350716152782544685838423)
          ·
            refine ⟨8026074229173817028757635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5350716152782544685838423 8026074229173817028757635)
            ·
              refine ⟨12039111343760725543136453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8026074229173817028757635 12039111343760725543136453)
              ·
                refine ⟨2257333376955136039338085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12039111343760725543136453 2257333376955136039338085)
                ·
                  refine ⟨423250008179088007375891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2257333376955136039338085 423250008179088007375891)
                  ·
                    rfl

theorem cell21_1854622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_1854622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1854622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1854622 prefixEnd_1854622 := by exact prefixLift 1854622
  have htrace : WordTrace (prefixWord ++ tailWord_1854622) baseStart_1854622 baseEnd_1854622 := by
    simpa [prefixWord, tailWord_1854622, baseEnd_1854622] using wordTrace_append hprefix tailTrace_1854622
  have hstable : (prefixWord ++ tailWord_1854622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854622).length < 2 ^ (prefixWord ++ tailWord_1854622).sum := by decide
  have hdescent : baseEnd_1854622 < baseStart_1854622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854698 : List Nat := [3, 1, 3, 1, 1, 4, 3, 1, 4]
def baseStart_1854698 : Nat := 118140960795 + 1854698 * 2 ^ 59
def prefixEnd_1854698 : Nat := 4983230072969 + 3 ^ 40 * 1854698 * 2
def baseEnd_1854698 : Nat := 423267352414528764109069

theorem tailTrace_1854698 : CollatzResearch.WordTrace tailWord_1854698 prefixEnd_1854698 423267352414528764109069 := by
  unfold tailWord_1854698
  simp only [CollatzResearch.WordTrace]
  refine ⟨16911598358688344511295187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45097595623168918696787165 16911598358688344511295187)
  ·
    refine ⟨25367397538032516766942781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16911598358688344511295187 25367397538032516766942781)
    ·
      refine ⟨9512774076762193787603543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25367397538032516766942781 9512774076762193787603543)
      ·
        refine ⟨14269161115143290681405315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9512774076762193787603543 14269161115143290681405315)
        ·
          refine ⟨21403741672714936022107973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14269161115143290681405315 21403741672714936022107973)
          ·
            refine ⟨4013201563634050504145245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21403741672714936022107973 4013201563634050504145245)
            ·
              refine ⟨1504950586362768939054467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4013201563634050504145245 1504950586362768939054467)
              ·
                refine ⟨2257425879544153408581701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1504950586362768939054467 2257425879544153408581701)
                ·
                  refine ⟨423267352414528764109069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2257425879544153408581701 423267352414528764109069)
                  ·
                    rfl

theorem cell21_1854698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_1854698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1854698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1854698 prefixEnd_1854698 := by exact prefixLift 1854698
  have htrace : WordTrace (prefixWord ++ tailWord_1854698) baseStart_1854698 baseEnd_1854698 := by
    simpa [prefixWord, tailWord_1854698, baseEnd_1854698] using wordTrace_append hprefix tailTrace_1854698
  have hstable : (prefixWord ++ tailWord_1854698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854698).length < 2 ^ (prefixWord ++ tailWord_1854698).sum := by decide
  have hdescent : baseEnd_1854698 < baseStart_1854698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854757 : List Nat := [1, 3, 1, 2, 4, 2, 1, 3, 4]
def baseStart_1854757 : Nat := 118140960795 + 1854757 * 2 ^ 59
def prefixEnd_1854757 : Nat := 4983230072969 + 3 ^ 40 * 1854757 * 2
def baseEnd_1854757 : Nat := 423280817018357772625615

theorem tailTrace_1854757 : CollatzResearch.WordTrace tailWord_1854757 prefixEnd_1854757 423280817018357772625615 := by
  unfold tailWord_1854757
  simp only [CollatzResearch.WordTrace]
  refine ⟨67648545341539631121578525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45099030227693087414385683 67648545341539631121578525)
  ·
    refine ⟨25368204503077361670591947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67648545341539631121578525 25368204503077361670591947)
    ·
      refine ⟨38052306754616042505887921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25368204503077361670591947 38052306754616042505887921)
      ·
        refine ⟨28539230065962031879415941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38052306754616042505887921 28539230065962031879415941)
        ·
          refine ⟨5351105637367880977390489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28539230065962031879415941 5351105637367880977390489)
          ·
            refine ⟨4013329228025910733042867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5351105637367880977390489 4013329228025910733042867)
            ·
              refine ⟨6019993842038866099564301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4013329228025910733042867 6019993842038866099564301)
              ·
                refine ⟨2257497690764574787336613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6019993842038866099564301 2257497690764574787336613)
                ·
                  refine ⟨423280817018357772625615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2257497690764574787336613 423280817018357772625615)
                  ·
                    rfl

theorem cell21_1854757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_1854757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1854757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1854757 prefixEnd_1854757 := by exact prefixLift 1854757
  have htrace : WordTrace (prefixWord ++ tailWord_1854757) baseStart_1854757 baseEnd_1854757 := by
    simpa [prefixWord, tailWord_1854757, baseEnd_1854757] using wordTrace_append hprefix tailTrace_1854757
  have hstable : (prefixWord ++ tailWord_1854757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854757).length < 2 ^ (prefixWord ++ tailWord_1854757).sum := by decide
  have hdescent : baseEnd_1854757 < baseStart_1854757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854799 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 10]
def baseStart_1854799 : Nat := 118140960795 + 1854799 * 2 ^ 59
def prefixEnd_1854799 : Nat := 4983230072969 + 3 ^ 40 * 1854799 * 2
def baseEnd_1854799 : Nat := 423290401990575032925529

theorem tailTrace_1854799 : CollatzResearch.WordTrace tailWord_1854799 prefixEnd_1854799 423290401990575032925529 := by
  unfold tailWord_1854799
  simp only [CollatzResearch.WordTrace]
  refine ⟨67650077207387472294607451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45100051471591648196404967 67650077207387472294607451)
  ·
    refine ⟨101475115811081208441911177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67650077207387472294607451 101475115811081208441911177)
    ·
      refine ⟨76106336858310906331433383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101475115811081208441911177 76106336858310906331433383)
      ·
        refine ⟨114159505287466359497150075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76106336858310906331433383 114159505287466359497150075)
        ·
          refine ⟨171239257931199539245725113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114159505287466359497150075 171239257931199539245725113)
          ·
            refine ⟨128429443448399654434293835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171239257931199539245725113 128429443448399654434293835)
            ·
              refine ⟨192644165172599481651440753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128429443448399654434293835 192644165172599481651440753)
              ·
                refine ⟨144483123879449611238580565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192644165172599481651440753 144483123879449611238580565)
                ·
                  refine ⟨423290401990575032925529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 144483123879449611238580565 423290401990575032925529)
                  ·
                    rfl

theorem cell21_1854799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 10].length) (baseStart_1854799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1854799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1854799 prefixEnd_1854799 := by exact prefixLift 1854799
  have htrace : WordTrace (prefixWord ++ tailWord_1854799) baseStart_1854799 baseEnd_1854799 := by
    simpa [prefixWord, tailWord_1854799, baseEnd_1854799] using wordTrace_append hprefix tailTrace_1854799
  have hstable : (prefixWord ++ tailWord_1854799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854799).length < 2 ^ (prefixWord ++ tailWord_1854799).sum := by decide
  have hdescent : baseEnd_1854799 < baseStart_1854799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854850 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1854850 : Nat := 118140960795 + 1854850 * 2 ^ 59
def prefixEnd_1854850 : Nat := 4983230072969 + 3 ^ 40 * 1854850 * 2
def baseEnd_1854850 : Nat := 423302040885410277575425

theorem tailTrace_1854850 : CollatzResearch.WordTrace tailWord_1854850 prefixEnd_1854850 423302040885410277575425 := by
  unfold tailWord_1854850
  simp only [CollatzResearch.WordTrace]
  refine ⟨16912984332550677001178501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45101291553468472003142669 16912984332550677001178501)
  ·
    refine ⟨3171184562353251937720969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16912984332550677001178501 3171184562353251937720969)
    ·
      refine ⟨2378388421764938953290727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3171184562353251937720969 2378388421764938953290727)
      ·
        refine ⟨3567582632647408429936091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2378388421764938953290727 3567582632647408429936091)
        ·
          refine ⟨5351373948971112644904137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3567582632647408429936091 5351373948971112644904137)
          ·
            refine ⟨4013530461728334483678103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5351373948971112644904137 4013530461728334483678103)
            ·
              refine ⟨6020295692592501725517155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4013530461728334483678103 6020295692592501725517155)
              ·
                refine ⟨9030443538888752588275733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6020295692592501725517155 9030443538888752588275733)
                ·
                  refine ⟨423302040885410277575425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9030443538888752588275733 423302040885410277575425)
                  ·
                    rfl

theorem cell21_1854850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1854850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1854850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1854850 prefixEnd_1854850 := by exact prefixLift 1854850
  have htrace : WordTrace (prefixWord ++ tailWord_1854850) baseStart_1854850 baseEnd_1854850 := by
    simpa [prefixWord, tailWord_1854850, baseEnd_1854850] using wordTrace_append hprefix tailTrace_1854850
  have hstable : (prefixWord ++ tailWord_1854850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854850).length < 2 ^ (prefixWord ++ tailWord_1854850).sum := by decide
  have hdescent : baseEnd_1854850 < baseStart_1854850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854968 : List Nat := [2, 1, 2, 1, 1, 5, 1, 4, 4]
def baseStart_1854968 : Nat := 118140960795 + 1854968 * 2 ^ 59
def prefixEnd_1854968 : Nat := 4983230072969 + 3 ^ 40 * 1854968 * 2
def baseEnd_1854968 : Nat := 423328970093068294608517

theorem tailTrace_1854968 : CollatzResearch.WordTrace tailWord_1854968 prefixEnd_1854968 423328970093068294608517 := by
  unfold tailWord_1854968
  simp only [CollatzResearch.WordTrace]
  refine ⟨33828120571887607078754779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45104160762516809438339705 33828120571887607078754779)
  ·
    refine ⟨50742180857831410618132169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33828120571887607078754779 50742180857831410618132169)
    ·
      refine ⟨38056635643373557963599127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50742180857831410618132169 38056635643373557963599127)
      ·
        refine ⟨57084953465060336945398691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38056635643373557963599127 57084953465060336945398691)
        ·
          refine ⟨85627430197590505418098037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57084953465060336945398691 85627430197590505418098037)
          ·
            refine ⟨8027571581024109882946691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85627430197590505418098037 8027571581024109882946691)
            ·
              refine ⟨12041357371536164824420037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8027571581024109882946691 12041357371536164824420037)
              ·
                refine ⟨2257754507163030904578757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12041357371536164824420037 2257754507163030904578757)
                ·
                  refine ⟨423328970093068294608517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2257754507163030904578757 423328970093068294608517)
                  ·
                    rfl

theorem cell21_1854968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_1854968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1854968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1854968 prefixEnd_1854968 := by exact prefixLift 1854968
  have htrace : WordTrace (prefixWord ++ tailWord_1854968) baseStart_1854968 baseEnd_1854968 := by
    simpa [prefixWord, tailWord_1854968, baseEnd_1854968] using wordTrace_append hprefix tailTrace_1854968
  have hstable : (prefixWord ++ tailWord_1854968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854968).length < 2 ^ (prefixWord ++ tailWord_1854968).sum := by decide
  have hdescent : baseEnd_1854968 < baseStart_1854968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1854974 : List Nat := [4, 2, 2, 3, 2, 1, 1, 6]
def baseStart_1854974 : Nat := 118140960795 + 1854974 * 2 ^ 59
def prefixEnd_1854974 : Nat := 4983230072969 + 3 ^ 40 * 1854974 * 2
def baseEnd_1854974 : Nat := 141110113124937872502835

theorem tailTrace_1854974 : CollatzResearch.WordTrace tailWord_1854974 prefixEnd_1854974 141110113124937872502835 := by
  unfold tailWord_1854974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8457057497719184647778497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45104306654502318121485317 8457057497719184647778497)
  ·
    refine ⟨6342793123289388485833873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8457057497719184647778497 6342793123289388485833873)
    ·
      refine ⟨4757094842467041364375405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6342793123289388485833873 4757094842467041364375405)
      ·
        refine ⟨1783910565925140511640777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4757094842467041364375405 1783910565925140511640777)
        ·
          refine ⟨1337932924443855383730583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1783910565925140511640777 1337932924443855383730583)
          ·
            refine ⟨2006899386665783075595875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337932924443855383730583 2006899386665783075595875)
            ·
              refine ⟨3010349079998674613393813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006899386665783075595875 3010349079998674613393813)
              ·
                refine ⟨141110113124937872502835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3010349079998674613393813 141110113124937872502835)
                ·
                  rfl

theorem cell21_1854974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_1854974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1854974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1854974 prefixEnd_1854974 := by exact prefixLift 1854974
  have htrace : WordTrace (prefixWord ++ tailWord_1854974) baseStart_1854974 baseEnd_1854974 := by
    simpa [prefixWord, tailWord_1854974, baseEnd_1854974] using wordTrace_append hprefix tailTrace_1854974
  have hstable : (prefixWord ++ tailWord_1854974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1854974).length < 2 ^ (prefixWord ++ tailWord_1854974).sum := by decide
  have hdescent : baseEnd_1854974 < baseStart_1854974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1854974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855137 : List Nat := [1, 2, 3, 3, 2, 2, 2, 2, 4]
def baseStart_1855137 : Nat := 118140960795 + 1855137 * 2 ^ 59
def prefixEnd_1855137 : Nat := 4983230072969 + 3 ^ 40 * 1855137 * 2
def baseEnd_1855137 : Nat := 423367538195561556291505

theorem tailTrace_1855137 : CollatzResearch.WordTrace tailWord_1855137 prefixEnd_1855137 423367538195561556291505 := by
  unfold tailWord_1855137
  simp only [CollatzResearch.WordTrace]
  refine ⟨67662405080162956020411665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45108270053441970680274443 67662405080162956020411665)
  ·
    refine ⟨50746803810122217015308749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67662405080162956020411665 50746803810122217015308749)
    ·
      refine ⟨19030051428795831380740781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50746803810122217015308749 19030051428795831380740781)
      ·
        refine ⟨7136269285798436767777793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19030051428795831380740781 7136269285798436767777793)
        ·
          refine ⟨5352201964348827575833345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7136269285798436767777793 5352201964348827575833345)
          ·
            refine ⟨4014151473261620681875009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5352201964348827575833345 4014151473261620681875009)
            ·
              refine ⟨3010613604946215511406257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4014151473261620681875009 3010613604946215511406257)
              ·
                refine ⟨2257960203709661633554693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3010613604946215511406257 2257960203709661633554693)
                ·
                  refine ⟨423367538195561556291505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2257960203709661633554693 423367538195561556291505)
                  ·
                    rfl

theorem cell21_1855137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_1855137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1855137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1855137 prefixEnd_1855137 := by exact prefixLift 1855137
  have htrace : WordTrace (prefixWord ++ tailWord_1855137) baseStart_1855137 baseEnd_1855137 := by
    simpa [prefixWord, tailWord_1855137, baseEnd_1855137] using wordTrace_append hprefix tailTrace_1855137
  have hstable : (prefixWord ++ tailWord_1855137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855137).length < 2 ^ (prefixWord ++ tailWord_1855137).sum := by decide
  have hdescent : baseEnd_1855137 < baseStart_1855137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855140 : List Nat := [2, 3, 1, 2, 2, 4, 2, 2, 3]
def baseStart_1855140 : Nat := 118140960795 + 1855140 * 2 ^ 59
def prefixEnd_1855140 : Nat := 4983230072969 + 3 ^ 40 * 1855140 * 2
def baseEnd_1855140 : Nat := 423368222836434217741499

theorem tailTrace_1855140 : CollatzResearch.WordTrace tailWord_1855140 prefixEnd_1855140 423368222836434217741499 := by
  unfold tailWord_1855140
  simp only [CollatzResearch.WordTrace]
  refine ⟨33831257249576043766385437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45108342999434725021847249 33831257249576043766385437)
  ·
    refine ⟨12686721468591016412394539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33831257249576043766385437 12686721468591016412394539)
    ·
      refine ⟨19030082202886524618591809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12686721468591016412394539 19030082202886524618591809)
      ·
        refine ⟨14272561652164893463943857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19030082202886524618591809 14272561652164893463943857)
        ·
          refine ⟨10704421239123670097957893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14272561652164893463943857 10704421239123670097957893)
          ·
            refine ⟨2007078982335688143367105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10704421239123670097957893 2007078982335688143367105)
            ·
              refine ⟨1505309236751766107525329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2007078982335688143367105 1505309236751766107525329)
              ·
                refine ⟨1128981927563824580643997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1505309236751766107525329 1128981927563824580643997)
                ·
                  refine ⟨423368222836434217741499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1128981927563824580643997 423368222836434217741499)
                  ·
                    rfl

theorem cell21_1855140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_1855140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1855140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1855140 prefixEnd_1855140 := by exact prefixLift 1855140
  have htrace : WordTrace (prefixWord ++ tailWord_1855140) baseStart_1855140 baseEnd_1855140 := by
    simpa [prefixWord, tailWord_1855140, baseEnd_1855140] using wordTrace_append hprefix tailTrace_1855140
  have hstable : (prefixWord ++ tailWord_1855140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855140).length < 2 ^ (prefixWord ++ tailWord_1855140).sum := by decide
  have hdescent : baseEnd_1855140 < baseStart_1855140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855148 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 11]
def baseStart_1855148 : Nat := 118140960795 + 1855148 * 2 ^ 59
def prefixEnd_1855148 : Nat := 4983230072969 + 3 ^ 40 * 1855148 * 2
def baseEnd_1855148 : Nat := 423370048545427981608149

theorem tailTrace_1855148 : CollatzResearch.WordTrace tailWord_1855148 prefixEnd_1855148 423370048545427981608149 := by
  unfold tailWord_1855148
  simp only [CollatzResearch.WordTrace]
  refine ⟨33831403141561552449531049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45108537522082069932708065 33831403141561552449531049)
  ·
    refine ⟨25373552356171164337148287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33831403141561552449531049 25373552356171164337148287)
    ·
      refine ⟨38060328534256746505722431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25373552356171164337148287 38060328534256746505722431)
      ·
        refine ⟨57090492801385119758583647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38060328534256746505722431 57090492801385119758583647)
        ·
          refine ⟨85635739202077679637875471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57090492801385119758583647 85635739202077679637875471)
          ·
            refine ⟨128453608803116519456813207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85635739202077679637875471 128453608803116519456813207)
            ·
              refine ⟨192680413204674779185219811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128453608803116519456813207 192680413204674779185219811)
              ·
                refine ⟨289020619807012168777829717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192680413204674779185219811 289020619807012168777829717)
                ·
                  refine ⟨423370048545427981608149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 289020619807012168777829717 423370048545427981608149)
                  ·
                    rfl

theorem cell21_1855148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_1855148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1855148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1855148 prefixEnd_1855148 := by exact prefixLift 1855148
  have htrace : WordTrace (prefixWord ++ tailWord_1855148) baseStart_1855148 baseEnd_1855148 := by
    simpa [prefixWord, tailWord_1855148, baseEnd_1855148] using wordTrace_append hprefix tailTrace_1855148
  have hstable : (prefixWord ++ tailWord_1855148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855148).length < 2 ^ (prefixWord ++ tailWord_1855148).sum := by decide
  have hdescent : baseEnd_1855148 < baseStart_1855148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855165 : List Nat := [1, 4, 1, 2, 1, 2, 3, 2, 5]
def baseStart_1855165 : Nat := 118140960795 + 1855165 * 2 ^ 59
def prefixEnd_1855165 : Nat := 4983230072969 + 3 ^ 40 * 1855165 * 2
def baseEnd_1855165 : Nat := 423373928177039729824781

theorem tailTrace_1855165 : CollatzResearch.WordTrace tailWord_1855165 prefixEnd_1855165 423373928177039729824781 := by
  unfold tailWord_1855165
  simp only [CollatzResearch.WordTrace]
  refine ⟨67663426324061516802430949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45108950882707677868287299 67663426324061516802430949)
  ·
    refine ⟨12686892435761534400455803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67663426324061516802430949 12686892435761534400455803)
    ·
      refine ⟨19030338653642301600683705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12686892435761534400455803 19030338653642301600683705)
      ·
        refine ⟨14272753990231726200512779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19030338653642301600683705 14272753990231726200512779)
        ·
          refine ⟨21409130985347589300769169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14272753990231726200512779 21409130985347589300769169)
          ·
            refine ⟨16056848239010691975576877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21409130985347589300769169 16056848239010691975576877)
            ·
              refine ⟨6021318089629009490841329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16056848239010691975576877 6021318089629009490841329)
              ·
                refine ⟨4515988567221757118130997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6021318089629009490841329 4515988567221757118130997)
                ·
                  refine ⟨423373928177039729824781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4515988567221757118130997 423373928177039729824781)
                  ·
                    rfl

theorem cell21_1855165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_1855165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1855165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1855165 prefixEnd_1855165 := by exact prefixLift 1855165
  have htrace : WordTrace (prefixWord ++ tailWord_1855165) baseStart_1855165 baseEnd_1855165 := by
    simpa [prefixWord, tailWord_1855165, baseEnd_1855165] using wordTrace_append hprefix tailTrace_1855165
  have hstable : (prefixWord ++ tailWord_1855165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855165).length < 2 ^ (prefixWord ++ tailWord_1855165).sum := by decide
  have hdescent : baseEnd_1855165 < baseStart_1855165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855224 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 7]
def baseStart_1855224 : Nat := 118140960795 + 1855224 * 2 ^ 59
def prefixEnd_1855224 : Nat := 4983230072969 + 3 ^ 40 * 1855224 * 2
def baseEnd_1855224 : Nat := 423387392780868738341327

theorem tailTrace_1855224 : CollatzResearch.WordTrace tailWord_1855224 prefixEnd_1855224 423387392780868738341327 := by
  unfold tailWord_1855224
  simp only [CollatzResearch.WordTrace]
  refine ⟨33832789115423884939414363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45110385487231846585885817 33832789115423884939414363)
  ·
    refine ⟨50749183673135827409121545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33832789115423884939414363 50749183673135827409121545)
    ·
      refine ⟨38061887754851870556841159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50749183673135827409121545 38061887754851870556841159)
      ·
        refine ⟨57092831632277805835261739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38061887754851870556841159 57092831632277805835261739)
        ·
          refine ⟨85639247448416708752892609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57092831632277805835261739 85639247448416708752892609)
          ·
            refine ⟨64229435586312531564669457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85639247448416708752892609 64229435586312531564669457)
            ·
              refine ⟨48172076689734398673502093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64229435586312531564669457 48172076689734398673502093)
              ·
                refine ⟨18064528758650399502563285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48172076689734398673502093 18064528758650399502563285)
                ·
                  refine ⟨423387392780868738341327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18064528758650399502563285 423387392780868738341327)
                  ·
                    rfl

theorem cell21_1855224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 7].length) (baseStart_1855224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1855224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1855224 prefixEnd_1855224 := by exact prefixLift 1855224
  have htrace : WordTrace (prefixWord ++ tailWord_1855224) baseStart_1855224 baseEnd_1855224 := by
    simpa [prefixWord, tailWord_1855224, baseEnd_1855224] using wordTrace_append hprefix tailTrace_1855224
  have hstable : (prefixWord ++ tailWord_1855224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855224).length < 2 ^ (prefixWord ++ tailWord_1855224).sum := by decide
  have hdescent : baseEnd_1855224 < baseStart_1855224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855258 : List Nat := [3, 1, 1, 3, 2, 4, 1, 1, 5]
def baseStart_1855258 : Nat := 118140960795 + 1855258 * 2 ^ 59
def prefixEnd_1855258 : Nat := 4983230072969 + 3 ^ 40 * 1855258 * 2
def baseEnd_1855258 : Nat := 423395152044092234774591

theorem tailTrace_1855258 : CollatzResearch.WordTrace tailWord_1855258 prefixEnd_1855258 423395152044092234774591 := by
  unfold tailWord_1855258
  simp only [CollatzResearch.WordTrace]
  refine ⟨16916704578181148421391607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45111212208483062457044285 16916704578181148421391607)
  ·
    refine ⟨25375056867271722632087411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16916704578181148421391607 25375056867271722632087411)
    ·
      refine ⟨38062585300907583948131117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25375056867271722632087411 38062585300907583948131117)
      ·
        refine ⟨14273469487840343980549169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38062585300907583948131117 14273469487840343980549169)
        ·
          refine ⟨10705102115880257985411877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14273469487840343980549169 10705102115880257985411877)
          ·
            refine ⟨2007206646727548372264727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10705102115880257985411877 2007206646727548372264727)
            ·
              refine ⟨3010809970091322558397091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2007206646727548372264727 3010809970091322558397091)
              ·
                refine ⟨4516214955136983837595637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3010809970091322558397091 4516214955136983837595637)
                ·
                  refine ⟨423395152044092234774591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4516214955136983837595637 423395152044092234774591)
                  ·
                    rfl

theorem cell21_1855258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_1855258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1855258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1855258 prefixEnd_1855258 := by exact prefixLift 1855258
  have htrace : WordTrace (prefixWord ++ tailWord_1855258) baseStart_1855258 baseEnd_1855258 := by
    simpa [prefixWord, tailWord_1855258, baseEnd_1855258] using wordTrace_append hprefix tailTrace_1855258
  have hstable : (prefixWord ++ tailWord_1855258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855258).length < 2 ^ (prefixWord ++ tailWord_1855258).sum := by decide
  have hdescent : baseEnd_1855258 < baseStart_1855258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855309 : List Nat := [1, 6, 1, 2, 1, 3, 2, 2, 3]
def baseStart_1855309 : Nat := 118140960795 + 1855309 * 2 ^ 59
def prefixEnd_1855309 : Nat := 4983230072969 + 3 ^ 40 * 1855309 * 2
def baseEnd_1855309 : Nat := 423406790938927479424487

theorem tailTrace_1855309 : CollatzResearch.WordTrace tailWord_1855309 prefixEnd_1855309 423406790938927479424487 := by
  unfold tailWord_1855309
  simp only [CollatzResearch.WordTrace]
  refine ⟨67668678435539829395672981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45112452290359886263781987 67668678435539829395672981)
  ·
    refine ⟨3171969301665929502922171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67668678435539829395672981 3171969301665929502922171)
    ·
      refine ⟨4757953952498894254383257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3171969301665929502922171 4757953952498894254383257)
      ·
        refine ⟨3568465464374170690787443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4757953952498894254383257 3568465464374170690787443)
        ·
          refine ⟨5352698196561256036181165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3568465464374170690787443 5352698196561256036181165)
          ·
            refine ⟨2007261823710471013567937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5352698196561256036181165 2007261823710471013567937)
            ·
              refine ⟨1505446367782853260175953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2007261823710471013567937 1505446367782853260175953)
              ·
                refine ⟨1129084775837139945131965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1505446367782853260175953 1129084775837139945131965)
                ·
                  refine ⟨423406790938927479424487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1129084775837139945131965 423406790938927479424487)
                  ·
                    rfl

theorem cell21_1855309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_1855309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1855309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1855309 prefixEnd_1855309 := by exact prefixLift 1855309
  have htrace : WordTrace (prefixWord ++ tailWord_1855309) baseStart_1855309 baseEnd_1855309 := by
    simpa [prefixWord, tailWord_1855309, baseEnd_1855309] using wordTrace_append hprefix tailTrace_1855309
  have hstable : (prefixWord ++ tailWord_1855309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855309).length < 2 ^ (prefixWord ++ tailWord_1855309).sum := by decide
  have hdescent : baseEnd_1855309 < baseStart_1855309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855376 : List Nat := [2, 1, 1, 1, 1, 1, 2, 7, 5]
def baseStart_1855376 : Nat := 118140960795 + 1855376 * 2 ^ 59
def prefixEnd_1855376 : Nat := 4983230072969 + 3 ^ 40 * 1855376 * 2
def baseEnd_1855376 : Nat := 423422081251750251807683

theorem tailTrace_1855376 : CollatzResearch.WordTrace tailWord_1855376 prefixEnd_1855376 423422081251750251807683 := by
  unfold tailWord_1855376
  simp only [CollatzResearch.WordTrace]
  refine ⟨33835561063148549919180991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45114081417531399892241321 33835561063148549919180991)
  ·
    refine ⟨50753341594722824878771487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33835561063148549919180991 50753341594722824878771487)
    ·
      refine ⟨76130012392084237318157231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50753341594722824878771487 76130012392084237318157231)
      ·
        refine ⟨114195018588126355977235847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76130012392084237318157231 114195018588126355977235847)
        ·
          refine ⟨171292527882189533965853771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114195018588126355977235847 171292527882189533965853771)
          ·
            refine ⟨256938791823284300948780657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171292527882189533965853771 256938791823284300948780657)
            ·
              refine ⟨192704093867463225711585493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256938791823284300948780657 192704093867463225711585493)
              ·
                refine ⟨4516502200018669352615285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 192704093867463225711585493 4516502200018669352615285)
                ·
                  refine ⟨423422081251750251807683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4516502200018669352615285 423422081251750251807683)
                  ·
                    rfl

theorem cell21_1855376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_1855376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1855376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1855376 prefixEnd_1855376 := by exact prefixLift 1855376
  have htrace : WordTrace (prefixWord ++ tailWord_1855376) baseStart_1855376 baseEnd_1855376 := by
    simpa [prefixWord, tailWord_1855376, baseEnd_1855376] using wordTrace_append hprefix tailTrace_1855376
  have hstable : (prefixWord ++ tailWord_1855376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855376).length < 2 ^ (prefixWord ++ tailWord_1855376).sum := by decide
  have hdescent : baseEnd_1855376 < baseStart_1855376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855438 : List Nat := [4, 1, 1, 1, 2, 2, 4, 6]
def baseStart_1855438 : Nat := 118140960795 + 1855438 * 2 ^ 59
def prefixEnd_1855438 : Nat := 4983230072969 + 3 ^ 40 * 1855438 * 2
def baseEnd_1855438 : Nat := 141145410165483973924741

theorem tailTrace_1855438 : CollatzResearch.WordTrace tailWord_1855438 prefixEnd_1855438 141145410165483973924741 := by
  unfold tailWord_1855438
  simp only [CollatzResearch.WordTrace]
  refine ⟨8459172931509060553389871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45115588968048322951412645 8459172931509060553389871)
  ·
    refine ⟨12688759397263590830084807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8459172931509060553389871 12688759397263590830084807)
    ·
      refine ⟨19033139095895386245127211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12688759397263590830084807 19033139095895386245127211)
      ·
        refine ⟨28549708643843079367690817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19033139095895386245127211 28549708643843079367690817)
        ·
          refine ⟨21412281482882309525768113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28549708643843079367690817 21412281482882309525768113)
          ·
            refine ⟨16059211112161732144326085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21412281482882309525768113 16059211112161732144326085)
            ·
              refine ⟨3011102083530324777061141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16059211112161732144326085 3011102083530324777061141)
              ·
                refine ⟨141145410165483973924741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3011102083530324777061141 141145410165483973924741)
                ·
                  rfl

theorem cell21_1855438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_1855438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1855438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1855438 prefixEnd_1855438 := by exact prefixLift 1855438
  have htrace : WordTrace (prefixWord ++ tailWord_1855438) baseStart_1855438 baseEnd_1855438 := by
    simpa [prefixWord, tailWord_1855438, baseEnd_1855438] using wordTrace_append hprefix tailTrace_1855438
  have hstable : (prefixWord ++ tailWord_1855438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855438).length < 2 ^ (prefixWord ++ tailWord_1855438).sum := by decide
  have hdescent : baseEnd_1855438 < baseStart_1855438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855483 : List Nat := [1, 1, 1, 1, 1, 3, 5, 4, 4]
def baseStart_1855483 : Nat := 118140960795 + 1855483 * 2 ^ 59
def prefixEnd_1855483 : Nat := 4983230072969 + 3 ^ 40 * 1855483 * 2
def baseEnd_1855483 : Nat := 423446500109541843524131

theorem tailTrace_1855483 : CollatzResearch.WordTrace tailWord_1855483 prefixEnd_1855483 423446500109541843524131 := by
  unfold tailWord_1855483
  simp only [CollatzResearch.WordTrace]
  refine ⟨67675024736909457112507103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45116683157939638075004735 67675024736909457112507103)
  ·
    refine ⟨101512537105364185668760655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67675024736909457112507103 101512537105364185668760655)
    ·
      refine ⟨152268805658046278503140983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101512537105364185668760655 152268805658046278503140983)
      ·
        refine ⟨228403208487069417754711475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152268805658046278503140983 228403208487069417754711475)
        ·
          refine ⟨342604812730604126632067213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228403208487069417754711475 342604812730604126632067213)
          ·
            refine ⟨128476804773976547487025205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342604812730604126632067213 128476804773976547487025205)
            ·
              refine ⟨12044700447560301326908613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128476804773976547487025205 12044700447560301326908613)
              ·
                refine ⟨2258381333917556498795365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12044700447560301326908613 2258381333917556498795365)
                ·
                  refine ⟨423446500109541843524131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2258381333917556498795365 423446500109541843524131)
                  ·
                    rfl

theorem cell21_1855483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 4, 4].length) (baseStart_1855483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1855483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1855483 prefixEnd_1855483 := by exact prefixLift 1855483
  have htrace : WordTrace (prefixWord ++ tailWord_1855483) baseStart_1855483 baseEnd_1855483 := by
    simpa [prefixWord, tailWord_1855483, baseEnd_1855483] using wordTrace_append hprefix tailTrace_1855483
  have hstable : (prefixWord ++ tailWord_1855483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855483).length < 2 ^ (prefixWord ++ tailWord_1855483).sum := by decide
  have hdescent : baseEnd_1855483 < baseStart_1855483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855649 : List Nat := [1, 2, 3, 3, 1, 11]
def baseStart_1855649 : Nat := 118140960795 + 1855649 * 2 ^ 59
def prefixEnd_1855649 : Nat := 4983230072969 + 3 ^ 40 * 1855649 * 2
def baseEnd_1855649 : Nat := 15684606798931942361375

theorem tailTrace_1855649 : CollatzResearch.WordTrace tailWord_1855649 prefixEnd_1855649 15684606798931942361375 := by
  unfold tailWord_1855649
  simp only [CollatzResearch.WordTrace]
  refine ⟨67681079254308067463050001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45120719502872044975366667 67681079254308067463050001)
  ·
    refine ⟨50760809440731050597287501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67681079254308067463050001 50760809440731050597287501)
    ·
      refine ⟨19035303540274143973982813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50760809440731050597287501 19035303540274143973982813)
      ·
        refine ⟨7138238827602803990243555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19035303540274143973982813 7138238827602803990243555)
        ·
          refine ⟨10707358241404205985365333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7138238827602803990243555 10707358241404205985365333)
          ·
            refine ⟨15684606798931942361375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10707358241404205985365333 15684606798931942361375)
            ·
              rfl

theorem cell21_1855649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 11].length) (baseStart_1855649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1855649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1855649 prefixEnd_1855649 := by exact prefixLift 1855649
  have htrace : WordTrace (prefixWord ++ tailWord_1855649) baseStart_1855649 baseEnd_1855649 := by
    simpa [prefixWord, tailWord_1855649, baseEnd_1855649] using wordTrace_append hprefix tailTrace_1855649
  have hstable : (prefixWord ++ tailWord_1855649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855649).length < 2 ^ (prefixWord ++ tailWord_1855649).sum := by decide
  have hdescent : baseEnd_1855649 < baseStart_1855649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855655 : List Nat := [1, 1, 6, 2, 2, 1, 1, 4, 3]
def baseStart_1855655 : Nat := 118140960795 + 1855655 * 2 ^ 59
def prefixEnd_1855655 : Nat := 4983230072969 + 3 ^ 40 * 1855655 * 2
def baseEnd_1855655 : Nat := 423485752852907766657113

theorem tailTrace_1855655 : CollatzResearch.WordTrace tailWord_1855655 prefixEnd_1855655 423485752852907766657113 := by
  unfold tailWord_1855655
  simp only [CollatzResearch.WordTrace]
  refine ⟨67681298092286330487768419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45120865394857553658512279 67681298092286330487768419)
  ·
    refine ⟨101521947138429495731652629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67681298092286330487768419 101521947138429495731652629)
    ·
      refine ⟨4758841272113882612421217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101521947138429495731652629 4758841272113882612421217)
      ·
        refine ⟨3569130954085411959315913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4758841272113882612421217 3569130954085411959315913)
        ·
          refine ⟨2676848215564058969486935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3569130954085411959315913 2676848215564058969486935)
          ·
            refine ⟨4015272323346088454230403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2676848215564058969486935 4015272323346088454230403)
            ·
              refine ⟨6022908485019132681345605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4015272323346088454230403 6022908485019132681345605)
              ·
                refine ⟨1129295340941087377752301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6022908485019132681345605 1129295340941087377752301)
                ·
                  refine ⟨423485752852907766657113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1129295340941087377752301 423485752852907766657113)
                  ·
                    rfl

theorem cell21_1855655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 3].length) (baseStart_1855655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1855655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1855655 prefixEnd_1855655 := by exact prefixLift 1855655
  have htrace : WordTrace (prefixWord ++ tailWord_1855655) baseStart_1855655 baseEnd_1855655 := by
    simpa [prefixWord, tailWord_1855655, baseEnd_1855655] using wordTrace_append hprefix tailTrace_1855655
  have hstable : (prefixWord ++ tailWord_1855655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855655).length < 2 ^ (prefixWord ++ tailWord_1855655).sum := by decide
  have hdescent : baseEnd_1855655 < baseStart_1855655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855680 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 7]
def baseStart_1855680 : Nat := 118140960795 + 1855680 * 2 ^ 59
def prefixEnd_1855680 : Nat := 4983230072969 + 3 ^ 40 * 1855680 * 2
def baseEnd_1855680 : Nat := 423491458193513278740395

theorem tailTrace_1855680 : CollatzResearch.WordTrace tailWord_1855680 prefixEnd_1855680 423491458193513278740395 := by
  unfold tailWord_1855680
  simp only [CollatzResearch.WordTrace]
  refine ⟨33841104958597879878714247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45121473278130506504952329 33841104958597879878714247)
  ·
    refine ⟨50761657437896819818071371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33841104958597879878714247 50761657437896819818071371)
    ·
      refine ⟨76142486156845229727107057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50761657437896819818071371 76142486156845229727107057)
      ·
        refine ⟨57106864617633922295330293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76142486156845229727107057 57106864617633922295330293)
        ·
          refine ⟨5353768557903180215187215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57106864617633922295330293 5353768557903180215187215)
          ·
            refine ⟨8030652836854770322780823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5353768557903180215187215 8030652836854770322780823)
            ·
              refine ⟨12045979255282155484171235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8030652836854770322780823 12045979255282155484171235)
              ·
                refine ⟨18068968882923233226256853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12045979255282155484171235 18068968882923233226256853)
                ·
                  refine ⟨423491458193513278740395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18068968882923233226256853 423491458193513278740395)
                  ·
                    rfl

theorem cell21_1855680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_1855680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1855680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1855680 prefixEnd_1855680 := by exact prefixLift 1855680
  have htrace : WordTrace (prefixWord ++ tailWord_1855680) baseStart_1855680 baseEnd_1855680 := by
    simpa [prefixWord, tailWord_1855680, baseEnd_1855680] using wordTrace_append hprefix tailTrace_1855680
  have hstable : (prefixWord ++ tailWord_1855680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855680).length < 2 ^ (prefixWord ++ tailWord_1855680).sum := by decide
  have hdescent : baseEnd_1855680 < baseStart_1855680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855697 : List Nat := [1, 2, 2, 1, 2, 2, 3, 5, 3]
def baseStart_1855697 : Nat := 118140960795 + 1855697 * 2 ^ 59
def prefixEnd_1855697 : Nat := 4983230072969 + 3 ^ 40 * 1855697 * 2
def baseEnd_1855697 : Nat := 423495337825125026957027

theorem tailTrace_1855697 : CollatzResearch.WordTrace tailWord_1855697 prefixEnd_1855697 423495337825125026957027 := by
  unfold tailWord_1855697
  simp only [CollatzResearch.WordTrace]
  refine ⟨67682829958134171660797345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45121886638756114440531563 67682829958134171660797345)
  ·
    refine ⟨50762122468600628745598009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67682829958134171660797345 50762122468600628745598009)
    ·
      refine ⟨38071591851450471559198507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50762122468600628745598009 38071591851450471559198507)
      ·
        refine ⟨57107387777175707338797761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38071591851450471559198507 57107387777175707338797761)
        ·
          refine ⟨42830540832881780504098321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57107387777175707338797761 42830540832881780504098321)
          ·
            refine ⟨32122905624661335378073741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42830540832881780504098321 32122905624661335378073741)
            ·
              refine ⟨12046089609248000766777653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32122905624661335378073741 12046089609248000766777653)
              ·
                refine ⟨1129320900867000071885405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12046089609248000766777653 1129320900867000071885405)
                ·
                  refine ⟨423495337825125026957027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1129320900867000071885405 423495337825125026957027)
                  ·
                    rfl

theorem cell21_1855697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 3].length) (baseStart_1855697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1855697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1855697 prefixEnd_1855697 := by exact prefixLift 1855697
  have htrace : WordTrace (prefixWord ++ tailWord_1855697) baseStart_1855697 baseEnd_1855697 := by
    simpa [prefixWord, tailWord_1855697, baseEnd_1855697] using wordTrace_append hprefix tailTrace_1855697
  have hstable : (prefixWord ++ tailWord_1855697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855697).length < 2 ^ (prefixWord ++ tailWord_1855697).sum := by decide
  have hdescent : baseEnd_1855697 < baseStart_1855697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855742 : List Nat := [4, 2, 2, 1, 1, 1, 3, 7]
def baseStart_1855742 : Nat := 118140960795 + 1855742 * 2 ^ 59
def prefixEnd_1855742 : Nat := 4983230072969 + 3 ^ 40 * 1855742 * 2
def baseEnd_1855742 : Nat := 141168535812738316235645

theorem tailTrace_1855742 : CollatzResearch.WordTrace tailWord_1855742 prefixEnd_1855742 141168535812738316235645 := by
  unfold tailWord_1855742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8460558905371393043273185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45122980828647429564123653 8460558905371393043273185)
  ·
    refine ⟨6345419179028544782454889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8460558905371393043273185 6345419179028544782454889)
    ·
      refine ⟨4759064384271408586841167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6345419179028544782454889 4759064384271408586841167)
      ·
        refine ⟨7138596576407112880261751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4759064384271408586841167 7138596576407112880261751)
        ·
          refine ⟨10707894864610669320392627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7138596576407112880261751 10707894864610669320392627)
          ·
            refine ⟨16061842296916003980588941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10707894864610669320392627 16061842296916003980588941)
            ·
              refine ⟨6023190861343501492720853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16061842296916003980588941 6023190861343501492720853)
              ·
                refine ⟨141168535812738316235645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6023190861343501492720853 141168535812738316235645)
                ·
                  rfl

theorem cell21_1855742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_1855742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1855742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1855742 prefixEnd_1855742 := by exact prefixLift 1855742
  have htrace : WordTrace (prefixWord ++ tailWord_1855742) baseStart_1855742 baseEnd_1855742 := by
    simpa [prefixWord, tailWord_1855742, baseEnd_1855742] using wordTrace_append hprefix tailTrace_1855742
  have hstable : (prefixWord ++ tailWord_1855742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855742).length < 2 ^ (prefixWord ++ tailWord_1855742).sum := by decide
  have hdescent : baseEnd_1855742 < baseStart_1855742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855748 : List Nat := [2, 3, 2, 2, 4, 1, 1, 3, 3]
def baseStart_1855748 : Nat := 118140960795 + 1855748 * 2 ^ 59
def prefixEnd_1855748 : Nat := 4983230072969 + 3 ^ 40 * 1855748 * 2
def baseEnd_1855748 : Nat := 423506976719960271606923

theorem tailTrace_1855748 : CollatzResearch.WordTrace tailWord_1855748 prefixEnd_1855748 423506976719960271606923 := by
  unfold tailWord_1855748
  simp only [CollatzResearch.WordTrace]
  refine ⟨33842345040474703685451949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45123126720632938247269265 33842345040474703685451949)
  ·
    refine ⟨12690879390178013882044481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33842345040474703685451949 12690879390178013882044481)
    ·
      refine ⟨9518159542633510411533361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12690879390178013882044481 9518159542633510411533361)
      ·
        refine ⟨7138619656975132808650021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9518159542633510411533361 7138619656975132808650021)
        ·
          refine ⟨1338491185682837401621879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7138619656975132808650021 1338491185682837401621879)
          ·
            refine ⟨2007736778524256102432819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338491185682837401621879 2007736778524256102432819)
            ·
              refine ⟨3011605167786384153649229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2007736778524256102432819 3011605167786384153649229)
              ·
                refine ⟨1129351937919894057618461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3011605167786384153649229 1129351937919894057618461)
                ·
                  refine ⟨423506976719960271606923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1129351937919894057618461 423506976719960271606923)
                  ·
                    rfl

theorem cell21_1855748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_1855748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1855748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1855748 prefixEnd_1855748 := by exact prefixLift 1855748
  have htrace : WordTrace (prefixWord ++ tailWord_1855748) baseStart_1855748 baseEnd_1855748 := by
    simpa [prefixWord, tailWord_1855748, baseEnd_1855748] using wordTrace_append hprefix tailTrace_1855748
  have hstable : (prefixWord ++ tailWord_1855748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855748).length < 2 ^ (prefixWord ++ tailWord_1855748).sum := by decide
  have hdescent : baseEnd_1855748 < baseStart_1855748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855908 : List Nat := [2, 3, 1, 2, 1, 1, 4, 2, 5]
def baseStart_1855908 : Nat := 118140960795 + 1855908 * 2 ^ 59
def prefixEnd_1855908 : Nat := 4983230072969 + 3 ^ 40 * 1855908 * 2
def baseEnd_1855908 : Nat := 423543490899835548939929

theorem tailTrace_1855908 : CollatzResearch.WordTrace tailWord_1855908 prefixEnd_1855908 423543490899835548939929 := by
  unfold tailWord_1855908
  simp only [CollatzResearch.WordTrace]
  refine ⟨33845262880184877348364189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45127017173579836464485585 33845262880184877348364189)
  ·
    refine ⟨12691973580069329005636571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33845262880184877348364189 12691973580069329005636571)
    ·
      refine ⟨19037960370103993508454857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12691973580069329005636571 19037960370103993508454857)
      ·
        refine ⟨14278470277577995131341143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19037960370103993508454857 14278470277577995131341143)
        ·
          refine ⟨21417705416366992697011715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14278470277577995131341143 21417705416366992697011715)
          ·
            refine ⟨32126558124550489045517573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21417705416366992697011715 32126558124550489045517573)
            ·
              refine ⟨6023729648353216696034545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32126558124550489045517573 6023729648353216696034545)
              ·
                refine ⟨4517797236264912522025909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6023729648353216696034545 4517797236264912522025909)
                ·
                  refine ⟨423543490899835548939929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4517797236264912522025909 423543490899835548939929)
                  ·
                    rfl

theorem cell21_1855908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_1855908 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1855908 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1855908 prefixEnd_1855908 := by exact prefixLift 1855908
  have htrace : WordTrace (prefixWord ++ tailWord_1855908) baseStart_1855908 baseEnd_1855908 := by
    simpa [prefixWord, tailWord_1855908, baseEnd_1855908] using wordTrace_append hprefix tailTrace_1855908
  have hstable : (prefixWord ++ tailWord_1855908).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855908).length < 2 ^ (prefixWord ++ tailWord_1855908).sum := by decide
  have hdescent : baseEnd_1855908 < baseStart_1855908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855911 : List Nat := [1, 1, 6, 1, 1, 4, 2, 5]
def baseStart_1855911 : Nat := 118140960795 + 1855911 * 2 ^ 59
def prefixEnd_1855911 : Nat := 4983230072969 + 3 ^ 40 * 1855911 * 2
def baseEnd_1855911 : Nat := 141181391846902736796641

theorem tailTrace_1855911 : CollatzResearch.WordTrace tailWord_1855911 prefixEnd_1855911 141181391846902736796641 := by
  unfold tailWord_1855911
  simp only [CollatzResearch.WordTrace]
  refine ⟨67690635179358886209087587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45127090119572590806058391 67690635179358886209087587)
  ·
    refine ⟨101535952769038329313631381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67690635179358886209087587 101535952769038329313631381)
    ·
      refine ⟨4759497786048671686576471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101535952769038329313631381 4759497786048671686576471)
      ·
        refine ⟨7139246679073007529864707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4759497786048671686576471 7139246679073007529864707)
        ·
          refine ⟨10708870018609511294797061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7139246679073007529864707 10708870018609511294797061)
          ·
            refine ⟨2007913128489283367774449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10708870018609511294797061 2007913128489283367774449)
            ·
              refine ⟨1505934846366962525830837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2007913128489283367774449 1505934846366962525830837)
              ·
                refine ⟨141181391846902736796641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1505934846366962525830837 141181391846902736796641)
                ·
                  rfl

theorem cell21_1855911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 5].length) (baseStart_1855911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1855911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1855911 prefixEnd_1855911 := by exact prefixLift 1855911
  have htrace : WordTrace (prefixWord ++ tailWord_1855911) baseStart_1855911 baseEnd_1855911 := by
    simpa [prefixWord, tailWord_1855911, baseEnd_1855911] using wordTrace_append hprefix tailTrace_1855911
  have hstable : (prefixWord ++ tailWord_1855911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855911).length < 2 ^ (prefixWord ++ tailWord_1855911).sum := by decide
  have hdescent : baseEnd_1855911 < baseStart_1855911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855922 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 8]
def baseStart_1855922 : Nat := 118140960795 + 1855922 * 2 ^ 59
def prefixEnd_1855922 : Nat := 4983230072969 + 3 ^ 40 * 1855922 * 2
def baseEnd_1855922 : Nat := 423546685890574635706567

theorem tailTrace_1855922 : CollatzResearch.WordTrace tailWord_1855922 prefixEnd_1855922 423546685890574635706567 := by
  unfold tailWord_1855922
  simp only [CollatzResearch.WordTrace]
  refine ⟨16922759095579758771934505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45127357588212690058492013 16922759095579758771934505)
  ·
    refine ⟨12692069321684819078950879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16922759095579758771934505 12692069321684819078950879)
    ·
      refine ⟨19038103982527228618426319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12692069321684819078950879 19038103982527228618426319)
      ·
        refine ⟨28557155973790842927639479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19038103982527228618426319 28557155973790842927639479)
        ·
          refine ⟨42835733960686264391459219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28557155973790842927639479 42835733960686264391459219)
          ·
            refine ⟨64253600941029396587188829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42835733960686264391459219 64253600941029396587188829)
            ·
              refine ⟨24095100352886023720195811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64253600941029396587188829 24095100352886023720195811)
              ·
                refine ⟨36142650529329035580293717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24095100352886023720195811 36142650529329035580293717)
                ·
                  refine ⟨423546685890574635706567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36142650529329035580293717 423546685890574635706567)
                  ·
                    rfl

theorem cell21_1855922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_1855922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1855922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1855922 prefixEnd_1855922 := by exact prefixLift 1855922
  have htrace : WordTrace (prefixWord ++ tailWord_1855922) baseStart_1855922 baseEnd_1855922 := by
    simpa [prefixWord, tailWord_1855922, baseEnd_1855922] using wordTrace_append hprefix tailTrace_1855922
  have hstable : (prefixWord ++ tailWord_1855922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855922).length < 2 ^ (prefixWord ++ tailWord_1855922).sum := by decide
  have hdescent : baseEnd_1855922 < baseStart_1855922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1855956 : List Nat := [2, 4, 1, 2, 2, 2, 1, 3, 4]
def baseStart_1855956 : Nat := 118140960795 + 1855956 * 2 ^ 59
def prefixEnd_1855956 : Nat := 4983230072969 + 3 ^ 40 * 1855956 * 2
def baseEnd_1855956 : Nat := 423554445153798132139831

theorem tailTrace_1855956 : CollatzResearch.WordTrace tailWord_1855956 prefixEnd_1855956 423554445153798132139831 := by
  unfold tailWord_1855956
  simp only [CollatzResearch.WordTrace]
  refine ⟨33846138232097929447237861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45128184309463905929650481 33846138232097929447237861)
  ·
    refine ⟨6346150918518361771357099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33846138232097929447237861 6346150918518361771357099)
    ·
      refine ⟨9519226377777542657035649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6346150918518361771357099 9519226377777542657035649)
      ·
        refine ⟨7139419783333156992776737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9519226377777542657035649 7139419783333156992776737)
        ·
          refine ⟨5354564837499867744582553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7139419783333156992776737 5354564837499867744582553)
          ·
            refine ⟨4015923628124900808436915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5354564837499867744582553 4015923628124900808436915)
            ·
              refine ⟨6023885442187351212655373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4015923628124900808436915 6023885442187351212655373)
              ·
                refine ⟨2258957040820256704745765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6023885442187351212655373 2258957040820256704745765)
                ·
                  refine ⟨423554445153798132139831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2258957040820256704745765 423554445153798132139831)
                  ·
                    rfl

theorem cell21_1855956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_1855956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1855956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1855956 prefixEnd_1855956 := by exact prefixLift 1855956
  have htrace : WordTrace (prefixWord ++ tailWord_1855956) baseStart_1855956 baseEnd_1855956 := by
    simpa [prefixWord, tailWord_1855956, baseEnd_1855956] using wordTrace_append hprefix tailTrace_1855956
  have hstable : (prefixWord ++ tailWord_1855956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1855956).length < 2 ^ (prefixWord ++ tailWord_1855956).sum := by decide
  have hdescent : baseEnd_1855956 < baseStart_1855956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1855956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856046 : List Nat := [4, 1, 3, 1, 3, 1, 8]
def baseStart_1856046 : Nat := 118140960795 + 1856046 * 2 ^ 59
def prefixEnd_1856046 : Nat := 4983230072969 + 3 ^ 40 * 1856046 * 2
def baseEnd_1856046 : Nat := 47063887153330886182183

theorem tailTrace_1856046 : CollatzResearch.WordTrace tailWord_1856046 prefixEnd_1856046 47063887153330886182183 := by
  unfold tailWord_1856046
  simp only [CollatzResearch.WordTrace]
  refine ⟨8461944879233725533156499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45130372689246536176834661 8461944879233725533156499)
  ·
    refine ⟨12692917318850588299734749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8461944879233725533156499 12692917318850588299734749)
    ·
      refine ⟨4759843994568970612400531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12692917318850588299734749 4759843994568970612400531)
      ·
        refine ⟨7139765991853455918600797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4759843994568970612400531 7139765991853455918600797)
        ·
          refine ⟨2677412246945045969475299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7139765991853455918600797 2677412246945045969475299)
          ·
            refine ⟨4016118370417568954212949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2677412246945045969475299 4016118370417568954212949)
            ·
              refine ⟨47063887153330886182183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4016118370417568954212949 47063887153330886182183)
              ·
                rfl

theorem cell21_1856046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 8].length) (baseStart_1856046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1856046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1856046 prefixEnd_1856046 := by exact prefixLift 1856046
  have htrace : WordTrace (prefixWord ++ tailWord_1856046) baseStart_1856046 baseEnd_1856046 := by
    simpa [prefixWord, tailWord_1856046, baseEnd_1856046] using wordTrace_append hprefix tailTrace_1856046
  have hstable : (prefixWord ++ tailWord_1856046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856046).length < 2 ^ (prefixWord ++ tailWord_1856046).sum := by decide
  have hdescent : baseEnd_1856046 < baseStart_1856046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856060 : List Nat := [2, 2, 2, 2, 3, 1, 1, 3, 5]
def baseStart_1856060 : Nat := 118140960795 + 1856060 * 2 ^ 59
def prefixEnd_1856060 : Nat := 4983230072969 + 3 ^ 40 * 1856060 * 2
def baseEnd_1856060 : Nat := 423578179370717062406285

theorem tailTrace_1856060 : CollatzResearch.WordTrace tailWord_1856060 prefixEnd_1856060 423578179370717062406285 := by
  unfold tailWord_1856060
  simp only [CollatzResearch.WordTrace]
  refine ⟨33848034827909542328130817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45130713103879389770841089 33848034827909542328130817)
  ·
    refine ⟨25386026120932156746098113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33848034827909542328130817 25386026120932156746098113)
    ·
      refine ⟨19039519590699117559573585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25386026120932156746098113 19039519590699117559573585)
      ·
        refine ⟨14279639693024338169680189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19039519590699117559573585 14279639693024338169680189)
        ·
          refine ⟨5354864884884126813630071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14279639693024338169680189 5354864884884126813630071)
          ·
            refine ⟨8032297327326190220445107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5354864884884126813630071 8032297327326190220445107)
            ·
              refine ⟨12048445990989285330667661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8032297327326190220445107 12048445990989285330667661)
              ·
                refine ⟨4518167246620981999000373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12048445990989285330667661 4518167246620981999000373)
                ·
                  refine ⟨423578179370717062406285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4518167246620981999000373 423578179370717062406285)
                  ·
                    rfl

theorem cell21_1856060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_1856060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1856060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1856060 prefixEnd_1856060 := by exact prefixLift 1856060
  have htrace : WordTrace (prefixWord ++ tailWord_1856060) baseStart_1856060 baseEnd_1856060 := by
    simpa [prefixWord, tailWord_1856060, baseEnd_1856060] using wordTrace_append hprefix tailTrace_1856060
  have hstable : (prefixWord ++ tailWord_1856060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856060).length < 2 ^ (prefixWord ++ tailWord_1856060).sum := by decide
  have hdescent : baseEnd_1856060 < baseStart_1856060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856077 : List Nat := [1, 6, 1, 1, 2, 1, 2, 2, 5]
def baseStart_1856077 : Nat := 118140960795 + 1856077 * 2 ^ 59
def prefixEnd_1856077 : Nat := 4983230072969 + 3 ^ 40 * 1856077 * 2
def baseEnd_1856077 : Nat := 423582059002328810622917

theorem tailTrace_1856077 : CollatzResearch.WordTrace tailWord_1856077 prefixEnd_1856077 423582059002328810622917 := by
  unfold tailWord_1856077
  simp only [CollatzResearch.WordTrace]
  refine ⟨67696689696757496559630485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45131126464504997706420323 67696689696757496559630485)
  ·
    refine ⟨3173282329535507651232679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67696689696757496559630485 3173282329535507651232679)
    ·
      refine ⟨4759923494303261476849019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3173282329535507651232679 4759923494303261476849019)
      ·
        refine ⟨7139885241454892215273529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4759923494303261476849019 7139885241454892215273529)
        ·
          refine ⟨5354913931091169161455147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7139885241454892215273529 5354913931091169161455147)
          ·
            refine ⟨8032370896636753742182721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5354913931091169161455147 8032370896636753742182721)
            ·
              refine ⟨6024278172477565306637041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8032370896636753742182721 6024278172477565306637041)
              ·
                refine ⟨4518208629358173979977781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6024278172477565306637041 4518208629358173979977781)
                ·
                  refine ⟨423582059002328810622917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4518208629358173979977781 423582059002328810622917)
                  ·
                    rfl

theorem cell21_1856077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_1856077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1856077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1856077 prefixEnd_1856077 := by exact prefixLift 1856077
  have htrace : WordTrace (prefixWord ++ tailWord_1856077) baseStart_1856077 baseEnd_1856077 := by
    simpa [prefixWord, tailWord_1856077, baseEnd_1856077] using wordTrace_append hprefix tailTrace_1856077
  have hstable : (prefixWord ++ tailWord_1856077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856077).length < 2 ^ (prefixWord ++ tailWord_1856077).sum := by decide
  have hdescent : baseEnd_1856077 < baseStart_1856077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856125 : List Nat := [1, 4, 1, 1, 5, 2, 2, 1, 4]
def baseStart_1856125 : Nat := 118140960795 + 1856125 * 2 ^ 59
def prefixEnd_1856125 : Nat := 4983230072969 + 3 ^ 40 * 1856125 * 2
def baseEnd_1856125 : Nat := 423593013256291393822819

theorem tailTrace_1856125 : CollatzResearch.WordTrace tailWord_1856125 prefixEnd_1856125 423593013256291393822819 := by
  unfold tailWord_1856125
  simp only [CollatzResearch.WordTrace]
  refine ⟨67698440400583600757377829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45132293600389067171585219 67698440400583600757377829)
  ·
    refine ⟨12693457575109425142008343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67698440400583600757377829 12693457575109425142008343)
    ·
      refine ⟨19040186362664137713012515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12693457575109425142008343 19040186362664137713012515)
      ·
        refine ⟨28560279543996206569518773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19040186362664137713012515 28560279543996206569518773)
        ·
          refine ⟨2677526207249644365892385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28560279543996206569518773 2677526207249644365892385)
          ·
            refine ⟨2008144655437233274419289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2677526207249644365892385 2008144655437233274419289)
            ·
              refine ⟨1506108491577924955814467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2008144655437233274419289 1506108491577924955814467)
              ·
                refine ⟨2259162737366887433721701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1506108491577924955814467 2259162737366887433721701)
                ·
                  refine ⟨423593013256291393822819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2259162737366887433721701 423593013256291393822819)
                  ·
                    rfl

theorem cell21_1856125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_1856125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1856125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1856125 prefixEnd_1856125 := by exact prefixLift 1856125
  have htrace : WordTrace (prefixWord ++ tailWord_1856125) baseStart_1856125 baseEnd_1856125 := by
    simpa [prefixWord, tailWord_1856125, baseEnd_1856125] using wordTrace_append hprefix tailTrace_1856125
  have hstable : (prefixWord ++ tailWord_1856125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856125).length < 2 ^ (prefixWord ++ tailWord_1856125).sum := by decide
  have hdescent : baseEnd_1856125 < baseStart_1856125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856229 : List Nat := [1, 3, 1, 4, 1, 2, 2, 4, 3]
def baseStart_1856229 : Nat := 118140960795 + 1856229 * 2 ^ 59
def prefixEnd_1856229 : Nat := 4983230072969 + 3 ^ 40 * 1856229 * 2
def baseEnd_1856229 : Nat := 423616747473210324089273

theorem tailTrace_1856229 : CollatzResearch.WordTrace tailWord_1856229 prefixEnd_1856229 423616747473210324089273 := by
  unfold tailWord_1856229
  simp only [CollatzResearch.WordTrace]
  refine ⟨67702233592206826519163741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45134822394804551012775827 67702233592206826519163741)
  ·
    refine ⟨25388337597077559944686403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67702233592206826519163741 25388337597077559944686403)
    ·
      refine ⟨38082506395616339917029605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25388337597077559944686403 38082506395616339917029605)
      ·
        refine ⟨7140469949178063734443051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38082506395616339917029605 7140469949178063734443051)
        ·
          refine ⟨10710704923767095601664577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7140469949178063734443051 10710704923767095601664577)
          ·
            refine ⟨8033028692825321701248433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10710704923767095601664577 8033028692825321701248433)
            ·
              refine ⟨6024771519618991275936325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8033028692825321701248433 6024771519618991275936325)
              ·
                refine ⟨1129644659928560864238061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6024771519618991275936325 1129644659928560864238061)
                ·
                  refine ⟨423616747473210324089273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1129644659928560864238061 423616747473210324089273)
                  ·
                    rfl

theorem cell21_1856229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_1856229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1856229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1856229 prefixEnd_1856229 := by exact prefixLift 1856229
  have htrace : WordTrace (prefixWord ++ tailWord_1856229) baseStart_1856229 baseEnd_1856229 := by
    simpa [prefixWord, tailWord_1856229, baseEnd_1856229] using wordTrace_append hprefix tailTrace_1856229
  have hstable : (prefixWord ++ tailWord_1856229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856229).length < 2 ^ (prefixWord ++ tailWord_1856229).sum := by decide
  have hdescent : baseEnd_1856229 < baseStart_1856229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856240 : List Nat := [2, 1, 1, 1, 3, 1, 4, 8]
def baseStart_1856240 : Nat := 118140960795 + 1856240 * 2 ^ 59
def prefixEnd_1856240 : Nat := 4983230072969 + 3 ^ 40 * 1856240 * 2
def baseEnd_1856240 : Nat := 141206419274358916468639

theorem tailTrace_1856240 : CollatzResearch.WordTrace tailWord_1856240 prefixEnd_1856240 141206419274358916468639 := by
  unfold tailWord_1856240
  simp only [CollatzResearch.WordTrace]
  refine ⟨33851317397583487698907087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45135089863444650265209449 33851317397583487698907087)
  ·
    refine ⟨50776976096375231548360631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33851317397583487698907087 50776976096375231548360631)
    ·
      refine ⟨76165464144562847322540947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50776976096375231548360631 76165464144562847322540947)
      ·
        refine ⟨114248196216844270983811421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76165464144562847322540947 114248196216844270983811421)
        ·
          refine ⟨42843073581316601618929283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114248196216844270983811421 42843073581316601618929283)
          ·
            refine ⟨64264610371974902428393925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42843073581316601618929283 64264610371974902428393925)
            ·
              refine ⟨12049614444745294205323861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64264610371974902428393925 12049614444745294205323861)
              ·
                refine ⟨141206419274358916468639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12049614444745294205323861 141206419274358916468639)
                ·
                  rfl

theorem cell21_1856240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 8].length) (baseStart_1856240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1856240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1856240 prefixEnd_1856240 := by exact prefixLift 1856240
  have htrace : WordTrace (prefixWord ++ tailWord_1856240) baseStart_1856240 baseEnd_1856240 := by
    simpa [prefixWord, tailWord_1856240, baseEnd_1856240] using wordTrace_append hprefix tailTrace_1856240
  have hstable : (prefixWord ++ tailWord_1856240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856240).length < 2 ^ (prefixWord ++ tailWord_1856240).sum := by decide
  have hdescent : baseEnd_1856240 < baseStart_1856240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856288 : List Nat := [2, 1, 1, 5, 1, 2, 3, 1, 5]
def baseStart_1856288 : Nat := 118140960795 + 1856288 * 2 ^ 59
def prefixEnd_1856288 : Nat := 4983230072969 + 3 ^ 40 * 1856288 * 2
def baseEnd_1856288 : Nat := 423630212077039332605819

theorem tailTrace_1856288 : CollatzResearch.WordTrace tailWord_1856288 prefixEnd_1856288 423630212077039332605819 := by
  unfold tailWord_1856288
  simp only [CollatzResearch.WordTrace]
  refine ⟨33852192749496539797780759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45136256999328719730374345 33852192749496539797780759)
  ·
    refine ⟨50778289124244809696671139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33852192749496539797780759 50778289124244809696671139)
    ·
      refine ⟨76167433686367214545006709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50778289124244809696671139 76167433686367214545006709)
      ·
        refine ⟨7140696908096926363594379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76167433686367214545006709 7140696908096926363594379)
        ·
          refine ⟨10711045362145389545391569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7140696908096926363594379 10711045362145389545391569)
          ·
            refine ⟨8033284021609042159043677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10711045362145389545391569 8033284021609042159043677)
            ·
              refine ⟨3012481508103390809641379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8033284021609042159043677 3012481508103390809641379)
              ·
                refine ⟨4518722262155086214462069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012481508103390809641379 4518722262155086214462069)
                ·
                  refine ⟨423630212077039332605819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4518722262155086214462069 423630212077039332605819)
                  ·
                    rfl

theorem cell21_1856288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_1856288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1856288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1856288 prefixEnd_1856288 := by exact prefixLift 1856288
  have htrace : WordTrace (prefixWord ++ tailWord_1856288) baseStart_1856288 baseEnd_1856288 := by
    simpa [prefixWord, tailWord_1856288, baseEnd_1856288] using wordTrace_append hprefix tailTrace_1856288
  have hstable : (prefixWord ++ tailWord_1856288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856288).length < 2 ^ (prefixWord ++ tailWord_1856288).sum := by decide
  have hdescent : baseEnd_1856288 < baseStart_1856288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856333 : List Nat := [1, 6, 1, 2, 11]
def baseStart_1856333 : Nat := 118140960795 + 1856333 * 2 ^ 59
def prefixEnd_1856333 : Nat := 4983230072969 + 3 ^ 40 * 1856333 * 2
def baseEnd_1856333 : Nat := 5230129403581842646367

theorem tailTrace_1856333 : CollatzResearch.WordTrace tailWord_1856333 prefixEnd_1856333 5230129403581842646367 := by
  unfold tailWord_1856333
  simp only [CollatzResearch.WordTrace]
  refine ⟨67706026783830052280949653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45137351189220034853966435 67706026783830052280949653)
  ·
    refine ⟨3173720005492033700669515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67706026783830052280949653 3173720005492033700669515)
    ·
      refine ⟨4760580008238050551004273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3173720005492033700669515 4760580008238050551004273)
      ·
        refine ⟨3570435006178537913253205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4760580008238050551004273 3570435006178537913253205)
        ·
          refine ⟨5230129403581842646367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3570435006178537913253205 5230129403581842646367)
          ·
            rfl

theorem cell21_1856333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 11].length) (baseStart_1856333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1856333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1856333 prefixEnd_1856333 := by exact prefixLift 1856333
  have htrace : WordTrace (prefixWord ++ tailWord_1856333) baseStart_1856333 baseEnd_1856333 := by
    simpa [prefixWord, tailWord_1856333, baseEnd_1856333] using wordTrace_append hprefix tailTrace_1856333
  have hstable : (prefixWord ++ tailWord_1856333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856333).length < 2 ^ (prefixWord ++ tailWord_1856333).sum := by decide
  have hdescent : baseEnd_1856333 < baseStart_1856333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856361 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 10]
def baseStart_1856361 : Nat := 118140960795 + 1856361 * 2 ^ 59
def prefixEnd_1856361 : Nat := 4983230072969 + 3 ^ 40 * 1856361 * 2
def baseEnd_1856361 : Nat := 423646871671607427889003

theorem tailTrace_1856361 : CollatzResearch.WordTrace tailWord_1856361 prefixEnd_1856361 423646871671607427889003 := by
  unfold tailWord_1856361
  simp only [CollatzResearch.WordTrace]
  refine ⟨67707048027728613062968937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45138032018485742041979291 67707048027728613062968937)
  ·
    refine ⟨50780286020796459797226703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67707048027728613062968937 50780286020796459797226703)
    ·
      refine ⟨76170429031194689695840055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50780286020796459797226703 76170429031194689695840055)
      ·
        refine ⟨114255643546792034543760083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76170429031194689695840055 114255643546792034543760083)
        ·
          refine ⟨171383465320188051815640125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114255643546792034543760083 171383465320188051815640125)
          ·
            refine ⟨64268799495070519430865047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171383465320188051815640125 64268799495070519430865047)
            ·
              refine ⟨96403199242605779146297571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64268799495070519430865047 96403199242605779146297571)
              ·
                refine ⟨144604798863908668719446357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96403199242605779146297571 144604798863908668719446357)
                ·
                  refine ⟨423646871671607427889003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 144604798863908668719446357 423646871671607427889003)
                  ·
                    rfl

theorem cell21_1856361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_1856361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1856361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1856361 prefixEnd_1856361 := by exact prefixLift 1856361
  have htrace : WordTrace (prefixWord ++ tailWord_1856361) baseStart_1856361 baseEnd_1856361 := by
    simpa [prefixWord, tailWord_1856361, baseEnd_1856361] using wordTrace_append hprefix tailTrace_1856361
  have hstable : (prefixWord ++ tailWord_1856361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856361).length < 2 ^ (prefixWord ++ tailWord_1856361).sum := by decide
  have hdescent : baseEnd_1856361 < baseStart_1856361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856564 : List Nat := [2, 5, 1, 2, 1, 1, 3, 2, 4]
def baseStart_1856564 : Nat := 118140960795 + 1856564 * 2 ^ 59
def prefixEnd_1856564 : Nat := 4983230072969 + 3 ^ 40 * 1856564 * 2
def baseEnd_1856564 : Nat := 423693199037324186005255

theorem tailTrace_1856564 : CollatzResearch.WordTrace tailWord_1856564 prefixEnd_1856564 423693199037324186005255 := by
  unfold tailWord_1856564
  simp only [CollatzResearch.WordTrace]
  refine ⟨33857226022996589366304373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45142968030662119155072497 33857226022996589366304373)
  ·
    refine ⟨3174114939655930253091035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33857226022996589366304373 3174114939655930253091035)
    ·
      refine ⟨4761172409483895379636553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3174114939655930253091035 4761172409483895379636553)
      ·
        refine ⟨3570879307112921534727415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4761172409483895379636553 3570879307112921534727415)
        ·
          refine ⟨5356318960669382302091123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3570879307112921534727415 5356318960669382302091123)
          ·
            refine ⟨8034478441004073453136685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5356318960669382302091123 8034478441004073453136685)
            ·
              refine ⟨3012929415376527544926257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8034478441004073453136685 3012929415376527544926257)
              ·
                refine ⟨2259697061532395658694693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3012929415376527544926257 2259697061532395658694693)
                ·
                  refine ⟨423693199037324186005255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2259697061532395658694693 423693199037324186005255)
                  ·
                    rfl

theorem cell21_1856564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_1856564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1856564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1856564 prefixEnd_1856564 := by exact prefixLift 1856564
  have htrace : WordTrace (prefixWord ++ tailWord_1856564) baseStart_1856564 baseEnd_1856564 := by
    simpa [prefixWord, tailWord_1856564, baseEnd_1856564] using wordTrace_append hprefix tailTrace_1856564
  have hstable : (prefixWord ++ tailWord_1856564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856564).length < 2 ^ (prefixWord ++ tailWord_1856564).sum := by decide
  have hdescent : baseEnd_1856564 < baseStart_1856564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856733 : List Nat := [1, 4, 3, 2, 3, 1, 1, 2, 4]
def baseStart_1856733 : Nat := 118140960795 + 1856733 * 2 ^ 59
def prefixEnd_1856733 : Nat := 4983230072969 + 3 ^ 40 * 1856733 * 2
def baseEnd_1856733 : Nat := 423731767139817447688243

theorem tailTrace_1856733 : CollatzResearch.WordTrace tailWord_1856733 prefixEnd_1856733 423731767139817447688243 := by
  unfold tailWord_1856733
  simp only [CollatzResearch.WordTrace]
  refine ⟨67720615982380920595510853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45147077321587280397007235 67720615982380920595510853)
  ·
    refine ⟨12697615496696422611658285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67720615982380920595510853 12697615496696422611658285)
    ·
      refine ⟨4761605811261158479371857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12697615496696422611658285 4761605811261158479371857)
      ·
        refine ⟨3571204358445868859528893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4761605811261158479371857 3571204358445868859528893)
        ·
          refine ⟨1339201634417200822323335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3571204358445868859528893 1339201634417200822323335)
          ·
            refine ⟨2008802451625801233485003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1339201634417200822323335 2008802451625801233485003)
            ·
              refine ⟨3013203677438701850227505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008802451625801233485003 3013203677438701850227505)
              ·
                refine ⟨2259902758079026387670629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3013203677438701850227505 2259902758079026387670629)
                ·
                  refine ⟨423731767139817447688243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2259902758079026387670629 423731767139817447688243)
                  ·
                    rfl

theorem cell21_1856733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_1856733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1856733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1856733 prefixEnd_1856733 := by exact prefixLift 1856733
  have htrace : WordTrace (prefixWord ++ tailWord_1856733) baseStart_1856733 baseEnd_1856733 := by
    simpa [prefixWord, tailWord_1856733, baseEnd_1856733] using wordTrace_append hprefix tailTrace_1856733
  have hstable : (prefixWord ++ tailWord_1856733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856733).length < 2 ^ (prefixWord ++ tailWord_1856733).sum := by decide
  have hdescent : baseEnd_1856733 < baseStart_1856733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856744 : List Nat := [2, 1, 4, 1, 2, 1, 1, 6, 3]
def baseStart_1856744 : Nat := 118140960795 + 1856744 * 2 ^ 59
def prefixEnd_1856744 : Nat := 4983230072969 + 3 ^ 40 * 1856744 * 2
def baseEnd_1856744 : Nat := 423734277489683873004887

theorem tailTrace_1856744 : CollatzResearch.WordTrace tailWord_1856744 prefixEnd_1856744 423734277489683873004887 := by
  unfold tailWord_1856744
  simp only [CollatzResearch.WordTrace]
  refine ⟨33860508592670534737080643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45147344790227379649440857 33860508592670534737080643)
  ·
    refine ⟨50790762889005802105620965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33860508592670534737080643 50790762889005802105620965)
    ·
      refine ⟨9523268041688587894803931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50790762889005802105620965 9523268041688587894803931)
      ·
        refine ⟨14284902062532881842205897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9523268041688587894803931 14284902062532881842205897)
        ·
          refine ⟨10713676546899661381654423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14284902062532881842205897 10713676546899661381654423)
          ·
            refine ⟨16070514820349492072481635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10713676546899661381654423 16070514820349492072481635)
            ·
              refine ⟨24105772230524238108722453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16070514820349492072481635 24105772230524238108722453)
              ·
                refine ⟨1129958073305823661346365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24105772230524238108722453 1129958073305823661346365)
                ·
                  refine ⟨423734277489683873004887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1129958073305823661346365 423734277489683873004887)
                  ·
                    rfl

theorem cell21_1856744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 3].length) (baseStart_1856744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1856744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1856744 prefixEnd_1856744 := by exact prefixLift 1856744
  have htrace : WordTrace (prefixWord ++ tailWord_1856744) baseStart_1856744 baseEnd_1856744 := by
    simpa [prefixWord, tailWord_1856744, baseEnd_1856744] using wordTrace_append hprefix tailTrace_1856744
  have hstable : (prefixWord ++ tailWord_1856744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856744).length < 2 ^ (prefixWord ++ tailWord_1856744).sum := by decide
  have hdescent : baseEnd_1856744 < baseStart_1856744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856803 : List Nat := [1, 1, 1, 4, 2, 3, 3, 1, 5]
def baseStart_1856803 : Nat := 118140960795 + 1856803 * 2 ^ 59
def prefixEnd_1856803 : Nat := 4983230072969 + 3 ^ 40 * 1856803 * 2
def baseEnd_1856803 : Nat := 423747742093512881521433

theorem tailTrace_1856803 : CollatzResearch.WordTrace tailWord_1856803 prefixEnd_1856803 423747742093512881521433 := by
  unfold tailWord_1856803
  simp only [CollatzResearch.WordTrace]
  refine ⟨67723169092127322550559063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45148779394751548367039375 67723169092127322550559063)
  ·
    refine ⟨101584753638190983825838595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67723169092127322550559063 101584753638190983825838595)
    ·
      refine ⟨152377130457286475738757893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101584753638190983825838595 152377130457286475738757893)
      ·
        refine ⟨28570711960741214201017105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152377130457286475738757893 28570711960741214201017105)
        ·
          refine ⟨21428033970555910650762829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28570711960741214201017105 21428033970555910650762829)
          ·
            refine ⟨8035512738958466494036061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21428033970555910650762829 8035512738958466494036061)
            ·
              refine ⟨3013317277109424935263523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8035512738958466494036061 3013317277109424935263523)
              ·
                refine ⟨4519975915664137402895285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3013317277109424935263523 4519975915664137402895285)
                ·
                  refine ⟨423747742093512881521433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4519975915664137402895285 423747742093512881521433)
                  ·
                    rfl

theorem cell21_1856803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 5].length) (baseStart_1856803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1856803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1856803 prefixEnd_1856803 := by exact prefixLift 1856803
  have htrace : WordTrace (prefixWord ++ tailWord_1856803) baseStart_1856803 baseEnd_1856803 := by
    simpa [prefixWord, tailWord_1856803, baseEnd_1856803] using wordTrace_append hprefix tailTrace_1856803
  have hstable : (prefixWord ++ tailWord_1856803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856803).length < 2 ^ (prefixWord ++ tailWord_1856803).sum := by decide
  have hdescent : baseEnd_1856803 < baseStart_1856803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856893 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 6]
def baseStart_1856893 : Nat := 118140960795 + 1856893 * 2 ^ 59
def prefixEnd_1856893 : Nat := 4983230072969 + 3 ^ 40 * 1856893 * 2
def baseEnd_1856893 : Nat := 423768281319692725021249

theorem tailTrace_1856893 : CollatzResearch.WordTrace tailWord_1856893 prefixEnd_1856893 423768281319692725021249 := by
  unfold tailWord_1856893
  simp only [CollatzResearch.WordTrace]
  refine ⟨67726451661801267921335333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45150967774534178614223555 67726451661801267921335333)
  ·
    refine ⟨12698709686587737735250375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67726451661801267921335333 12698709686587737735250375)
    ·
      refine ⟨19048064529881606602875563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12698709686587737735250375 19048064529881606602875563)
      ·
        refine ⟨28572096794822409904313345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19048064529881606602875563 28572096794822409904313345)
        ·
          refine ⟨21429072596116807428235009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28572096794822409904313345 21429072596116807428235009)
          ·
            refine ⟨16071804447087605571176257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21429072596116807428235009 16071804447087605571176257)
            ·
              refine ⟨12053853335315704178382193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16071804447087605571176257 12053853335315704178382193)
              ·
                refine ⟨9040390001486778133786645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12053853335315704178382193 9040390001486778133786645)
                ·
                  refine ⟨423768281319692725021249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9040390001486778133786645 423768281319692725021249)
                  ·
                    rfl

theorem cell21_1856893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_1856893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1856893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1856893 prefixEnd_1856893 := by exact prefixLift 1856893
  have htrace : WordTrace (prefixWord ++ tailWord_1856893) baseStart_1856893 baseEnd_1856893 := by
    simpa [prefixWord, tailWord_1856893, baseEnd_1856893] using wordTrace_append hprefix tailTrace_1856893
  have hstable : (prefixWord ++ tailWord_1856893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856893).length < 2 ^ (prefixWord ++ tailWord_1856893).sum := by decide
  have hdescent : baseEnd_1856893 < baseStart_1856893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856907 : List Nat := [1, 1, 1, 1, 4, 3, 10]
def baseStart_1856907 : Nat := 118140960795 + 1856907 * 2 ^ 59
def prefixEnd_1856907 : Nat := 4983230072969 + 3 ^ 40 * 1856907 * 2
def baseEnd_1856907 : Nat := 47085719590047979087543

theorem tailTrace_1856907 : CollatzResearch.WordTrace tailWord_1856907 prefixEnd_1856907 47085719590047979087543 := by
  unfold tailWord_1856907
  simp only [CollatzResearch.WordTrace]
  refine ⟨67726962283750548312344975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45151308189167032208229983 67726962283750548312344975)
  ·
    refine ⟨101590443425625822468517463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67726962283750548312344975 101590443425625822468517463)
    ·
      refine ⟨152385665138438733702776195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101590443425625822468517463 152385665138438733702776195)
      ·
        refine ⟨228578497707658100554164293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152385665138438733702776195 228578497707658100554164293)
        ·
          refine ⟨42858468320185893853905805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228578497707658100554164293 42858468320185893853905805)
          ·
            refine ⟨16071925620069710195214677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42858468320185893853905805 16071925620069710195214677)
            ·
              refine ⟨47085719590047979087543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16071925620069710195214677 47085719590047979087543)
              ·
                rfl

theorem cell21_1856907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 10].length) (baseStart_1856907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1856907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1856907 prefixEnd_1856907 := by exact prefixLift 1856907
  have htrace : WordTrace (prefixWord ++ tailWord_1856907) baseStart_1856907 baseEnd_1856907 := by
    simpa [prefixWord, tailWord_1856907, baseEnd_1856907] using wordTrace_append hprefix tailTrace_1856907
  have hstable : (prefixWord ++ tailWord_1856907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856907).length < 2 ^ (prefixWord ++ tailWord_1856907).sum := by decide
  have hdescent : baseEnd_1856907 < baseStart_1856907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856927 : List Nat := [1, 1, 2, 5, 1, 3, 3, 1, 4]
def baseStart_1856927 : Nat := 118140960795 + 1856927 * 2 ^ 59
def prefixEnd_1856927 : Nat := 4983230072969 + 3 ^ 40 * 1856927 * 2
def baseEnd_1856927 : Nat := 423776040582916221454513

theorem tailTrace_1856927 : CollatzResearch.WordTrace tailWord_1856927 prefixEnd_1856927 423776040582916221454513 := by
  unfold tailWord_1856927
  simp only [CollatzResearch.WordTrace]
  refine ⟨67727691743678091728073035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45151794495785394485382023 67727691743678091728073035)
  ·
    refine ⟨101591537615517137592109553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67727691743678091728073035 101591537615517137592109553)
    ·
      refine ⟨76193653211637853194082165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101591537615517137592109553 76193653211637853194082165)
      ·
        refine ⟨7143154988591048736945203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76193653211637853194082165 7143154988591048736945203)
        ·
          refine ⟨10714732482886573105417805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7143154988591048736945203 10714732482886573105417805)
          ·
            refine ⟨4018024681082464914531677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10714732482886573105417805 4018024681082464914531677)
            ·
              refine ⟨1506759255405924342949379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4018024681082464914531677 1506759255405924342949379)
              ·
                refine ⟨2260138883108886514424069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1506759255405924342949379 2260138883108886514424069)
                ·
                  refine ⟨423776040582916221454513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2260138883108886514424069 423776040582916221454513)
                  ·
                    rfl

theorem cell21_1856927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 4].length) (baseStart_1856927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1856927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1856927 prefixEnd_1856927 := by exact prefixLift 1856927
  have htrace : WordTrace (prefixWord ++ tailWord_1856927) baseStart_1856927 baseEnd_1856927 := by
    simpa [prefixWord, tailWord_1856927, baseEnd_1856927] using wordTrace_append hprefix tailTrace_1856927
  have hstable : (prefixWord ++ tailWord_1856927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856927).length < 2 ^ (prefixWord ++ tailWord_1856927).sum := by decide
  have hdescent : baseEnd_1856927 < baseStart_1856927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856941 : List Nat := [1, 5, 2, 2, 1, 2, 1, 7]
def baseStart_1856941 : Nat := 118140960795 + 1856941 * 2 ^ 59
def prefixEnd_1856941 : Nat := 4983230072969 + 3 ^ 40 * 1856941 * 2
def baseEnd_1856941 : Nat := 141259745191218436073717

theorem tailTrace_1856941 : CollatzResearch.WordTrace tailWord_1856941 prefixEnd_1856941 141259745191218436073717 := by
  unfold tailWord_1856941
  simp only [CollatzResearch.WordTrace]
  refine ⟨67728202365627372119082677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45152134910418248079388451 67728202365627372119082677)
  ·
    refine ⟨6349518971777566136164001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67728202365627372119082677 6349518971777566136164001)
    ·
      refine ⟨4762139228833174602123001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6349518971777566136164001 4762139228833174602123001)
      ·
        refine ⟨3571604421624880951592251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4762139228833174602123001 3571604421624880951592251)
        ·
          refine ⟨5357406632437321427388377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3571604421624880951592251 5357406632437321427388377)
          ·
            refine ⟨4018054974327991070541283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5357406632437321427388377 4018054974327991070541283)
            ·
              refine ⟨6027082461491986605811925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4018054974327991070541283 6027082461491986605811925)
              ·
                refine ⟨141259745191218436073717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6027082461491986605811925 141259745191218436073717)
                ·
                  rfl

theorem cell21_1856941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 7].length) (baseStart_1856941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1856941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1856941 prefixEnd_1856941 := by exact prefixLift 1856941
  have htrace : WordTrace (prefixWord ++ tailWord_1856941) baseStart_1856941 baseEnd_1856941 := by
    simpa [prefixWord, tailWord_1856941, baseEnd_1856941] using wordTrace_append hprefix tailTrace_1856941
  have hstable : (prefixWord ++ tailWord_1856941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856941).length < 2 ^ (prefixWord ++ tailWord_1856941).sum := by decide
  have hdescent : baseEnd_1856941 < baseStart_1856941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856969 : List Nat := [1, 2, 1, 1, 2, 1, 3, 6, 4]
def baseStart_1856969 : Nat := 118140960795 + 1856969 * 2 ^ 59
def prefixEnd_1856969 : Nat := 4983230072969 + 3 ^ 40 * 1856969 * 2
def baseEnd_1856969 : Nat := 423785625555133481754427

theorem tailTrace_1856969 : CollatzResearch.WordTrace tailWord_1856969 prefixEnd_1856969 423785625555133481754427 := by
  unfold tailWord_1856969
  simp only [CollatzResearch.WordTrace]
  refine ⟨67729223609525932901101961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45152815739683955267401307 67729223609525932901101961)
  ·
    refine ⟨50796917707144449675826471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67729223609525932901101961 50796917707144449675826471)
    ·
      refine ⟨76195376560716674513739707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50796917707144449675826471 76195376560716674513739707)
      ·
        refine ⟨114293064841075011770609561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76195376560716674513739707 114293064841075011770609561)
        ·
          refine ⟨85719798630806258827957171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114293064841075011770609561 85719798630806258827957171)
          ·
            refine ⟨128579697946209388241935757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85719798630806258827957171 128579697946209388241935757)
            ·
              refine ⟨48217386729828520590725909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128579697946209388241935757 48217386729828520590725909)
              ·
                refine ⟨2260190002960711902690277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48217386729828520590725909 2260190002960711902690277)
                ·
                  refine ⟨423785625555133481754427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2260190002960711902690277 423785625555133481754427)
                  ·
                    rfl

theorem cell21_1856969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_1856969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1856969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1856969 prefixEnd_1856969 := by exact prefixLift 1856969
  have htrace : WordTrace (prefixWord ++ tailWord_1856969) baseStart_1856969 baseEnd_1856969 := by
    simpa [prefixWord, tailWord_1856969, baseEnd_1856969] using wordTrace_append hprefix tailTrace_1856969
  have hstable : (prefixWord ++ tailWord_1856969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856969).length < 2 ^ (prefixWord ++ tailWord_1856969).sum := by decide
  have hdescent : baseEnd_1856969 < baseStart_1856969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856972 : List Nat := [2, 2, 1, 4, 2, 3, 1, 1, 5]
def baseStart_1856972 : Nat := 118140960795 + 1856972 * 2 ^ 59
def prefixEnd_1856972 : Nat := 4983230072969 + 3 ^ 40 * 1856972 * 2
def baseEnd_1856972 : Nat := 423786310196006143204421

theorem tailTrace_1856972 : CollatzResearch.WordTrace tailWord_1856972 prefixEnd_1856972 423786310196006143204421 := by
  unfold tailWord_1856972
  simp only [CollatzResearch.WordTrace]
  refine ⟨33864666514257532206730585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45152888685676709608974113 33864666514257532206730585)
  ·
    refine ⟨25398499885693149155047939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33864666514257532206730585 25398499885693149155047939)
    ·
      refine ⟨38097749828539723732571909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25398499885693149155047939 38097749828539723732571909)
      ·
        refine ⟨7143328092851198199857233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38097749828539723732571909 7143328092851198199857233)
        ·
          refine ⟨5357496069638398649892925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7143328092851198199857233 5357496069638398649892925)
          ·
            refine ⟨2009061026114399493709847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5357496069638398649892925 2009061026114399493709847)
            ·
              refine ⟨3013591539171599240564771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2009061026114399493709847 3013591539171599240564771)
              ·
                refine ⟨4520387308757398860847157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3013591539171599240564771 4520387308757398860847157)
                ·
                  refine ⟨423786310196006143204421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4520387308757398860847157 423786310196006143204421)
                  ·
                    rfl

theorem cell21_1856972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_1856972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1856972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1856972 prefixEnd_1856972 := by exact prefixLift 1856972
  have htrace : WordTrace (prefixWord ++ tailWord_1856972) baseStart_1856972 baseEnd_1856972 := by
    simpa [prefixWord, tailWord_1856972, baseEnd_1856972] using wordTrace_append hprefix tailTrace_1856972
  have hstable : (prefixWord ++ tailWord_1856972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856972).length < 2 ^ (prefixWord ++ tailWord_1856972).sum := by decide
  have hdescent : baseEnd_1856972 < baseStart_1856972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1856986 : List Nat := [3, 1, 1, 2, 3, 3, 1, 3, 4]
def baseStart_1856986 : Nat := 118140960795 + 1856986 * 2 ^ 59
def prefixEnd_1856986 : Nat := 4983230072969 + 3 ^ 40 * 1856986 * 2
def baseEnd_1856986 : Nat := 423789505186745229971059

theorem tailTrace_1856986 : CollatzResearch.WordTrace tailWord_1856986 prefixEnd_1856986 423789505186745229971059 := by
  unfold tailWord_1856986
  simp only [CollatzResearch.WordTrace]
  refine ⟨16932460912616086201117703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45153229100309563202980541 16932460912616086201117703)
  ·
    refine ⟨25398691368924129301676555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16932460912616086201117703 25398691368924129301676555)
    ·
      refine ⟨38098037053386193952514833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25398691368924129301676555 38098037053386193952514833)
      ·
        refine ⟨28573527790039645464386125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38098037053386193952514833 28573527790039645464386125)
        ·
          refine ⟨10715072921264867049144797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28573527790039645464386125 10715072921264867049144797)
          ·
            refine ⟨4018152345474325143429299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10715072921264867049144797 4018152345474325143429299)
            ·
              refine ⟨6027228518211487715143949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4018152345474325143429299 6027228518211487715143949)
              ·
                refine ⟨2260210694329307893178981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6027228518211487715143949 2260210694329307893178981)
                ·
                  refine ⟨423789505186745229971059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2260210694329307893178981 423789505186745229971059)
                  ·
                    rfl

theorem cell21_1856986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_1856986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1856986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1856986 prefixEnd_1856986 := by exact prefixLift 1856986
  have htrace : WordTrace (prefixWord ++ tailWord_1856986) baseStart_1856986 baseEnd_1856986 := by
    simpa [prefixWord, tailWord_1856986, baseEnd_1856986] using wordTrace_append hprefix tailTrace_1856986
  have hstable : (prefixWord ++ tailWord_1856986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1856986).length < 2 ^ (prefixWord ++ tailWord_1856986).sum := by decide
  have hdescent : baseEnd_1856986 < baseStart_1856986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1856986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857124 : List Nat := [2, 3, 1, 1, 2, 3, 3, 3, 3]
def baseStart_1857124 : Nat := 118140960795 + 1857124 * 2 ^ 59
def prefixEnd_1857124 : Nat := 4983230072969 + 3 ^ 40 * 1857124 * 2
def baseEnd_1857124 : Nat := 423820998666887656670777

theorem tailTrace_1857124 : CollatzResearch.WordTrace tailWord_1857124 prefixEnd_1857124 423820998666887656670777 := by
  unfold tailWord_1857124
  simp only [CollatzResearch.WordTrace]
  refine ⟨33867438461982197186497213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45156584615976262915329617 33867438461982197186497213)
  ·
    refine ⟨12700289423243323944936455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33867438461982197186497213 12700289423243323944936455)
    ·
      refine ⟨19050434134864985917404683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12700289423243323944936455 19050434134864985917404683)
      ·
        refine ⟨28575651202297478876107025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19050434134864985917404683 28575651202297478876107025)
        ·
          refine ⟨21431738401723109157080269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28575651202297478876107025 21431738401723109157080269)
          ·
            refine ⟨8036901900646165933905101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21431738401723109157080269 8036901900646165933905101)
            ·
              refine ⟨3013838212742312225214413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8036901900646165933905101 3013838212742312225214413)
              ·
                refine ⟨1130189329778367084455405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3013838212742312225214413 1130189329778367084455405)
                ·
                  refine ⟨423820998666887656670777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1130189329778367084455405 423820998666887656670777)
                  ·
                    rfl

theorem cell21_1857124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_1857124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1857124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1857124 prefixEnd_1857124 := by exact prefixLift 1857124
  have htrace : WordTrace (prefixWord ++ tailWord_1857124) baseStart_1857124 baseEnd_1857124 := by
    simpa [prefixWord, tailWord_1857124, baseEnd_1857124] using wordTrace_append hprefix tailTrace_1857124
  have hstable : (prefixWord ++ tailWord_1857124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857124).length < 2 ^ (prefixWord ++ tailWord_1857124).sum := by decide
  have hdescent : baseEnd_1857124 < baseStart_1857124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857192 : List Nat := [2, 1, 7, 1, 1, 2, 2, 2, 3]
def baseStart_1857192 : Nat := 118140960795 + 1857192 * 2 ^ 59
def prefixEnd_1857192 : Nat := 4983230072969 + 3 ^ 40 * 1857192 * 2
def baseEnd_1857192 : Nat := 423836517193334649537305

theorem tailTrace_1857192 : CollatzResearch.WordTrace tailWord_1857192 prefixEnd_1857192 423836517193334649537305 := by
  unfold tailWord_1857192
  simp only [CollatzResearch.WordTrace]
  refine ⟨33868678543859020993234915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45158238058478694657646553 33868678543859020993234915)
  ·
    refine ⟨50803017815788531489852373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33868678543859020993234915 50803017815788531489852373)
    ·
      refine ⟨1190695730057543706793415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 50803017815788531489852373 1190695730057543706793415)
      ·
        refine ⟨1786043595086315560190123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1190695730057543706793415 1786043595086315560190123)
        ·
          refine ⟨2679065392629473340285185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1786043595086315560190123 2679065392629473340285185)
          ·
            refine ⟨2009299044472105005213889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2679065392629473340285185 2009299044472105005213889)
            ·
              refine ⟨1506974283354078753910417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2009299044472105005213889 1506974283354078753910417)
              ·
                refine ⟨1130230712515559065432813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1506974283354078753910417 1130230712515559065432813)
                ·
                  refine ⟨423836517193334649537305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1130230712515559065432813 423836517193334649537305)
                  ·
                    rfl

theorem cell21_1857192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 3].length) (baseStart_1857192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1857192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1857192 prefixEnd_1857192 := by exact prefixLift 1857192
  have htrace : WordTrace (prefixWord ++ tailWord_1857192) baseStart_1857192 baseEnd_1857192 := by
    simpa [prefixWord, tailWord_1857192, baseEnd_1857192] using wordTrace_append hprefix tailTrace_1857192
  have hstable : (prefixWord ++ tailWord_1857192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857192).length < 2 ^ (prefixWord ++ tailWord_1857192).sum := by decide
  have hdescent : baseEnd_1857192 < baseStart_1857192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857200 : List Nat := [2, 1, 1, 1, 2, 1, 8, 2, 3]
def baseStart_1857200 : Nat := 118140960795 + 1857200 * 2 ^ 59
def prefixEnd_1857200 : Nat := 4983230072969 + 3 ^ 40 * 1857200 * 2
def baseEnd_1857200 : Nat := 423838342902328413403955

theorem tailTrace_1857200 : CollatzResearch.WordTrace tailWord_1857200 prefixEnd_1857200 423838342902328413403955 := by
  unfold tailWord_1857200
  simp only [CollatzResearch.WordTrace]
  refine ⟨33868824435844529676380527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45158432581126039568507369 33868824435844529676380527)
  ·
    refine ⟨50803236653766794514570791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33868824435844529676380527 50803236653766794514570791)
    ·
      refine ⟨76204854980650191771856187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50803236653766794514570791 76204854980650191771856187)
      ·
        refine ⟨114307282470975287657784281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76204854980650191771856187 114307282470975287657784281)
        ·
          refine ⟨85730461853231465743338211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114307282470975287657784281 85730461853231465743338211)
          ·
            refine ⟨128595692779847198615007317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85730461853231465743338211 128595692779847198615007317)
            ·
              refine ⟨1506980774763834358769617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 128595692779847198615007317 1506980774763834358769617)
              ·
                refine ⟨1130235581072875769077213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1506980774763834358769617 1130235581072875769077213)
                ·
                  refine ⟨423838342902328413403955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1130235581072875769077213 423838342902328413403955)
                  ·
                    rfl

theorem cell21_1857200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 3].length) (baseStart_1857200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1857200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1857200 prefixEnd_1857200 := by exact prefixLift 1857200
  have htrace : WordTrace (prefixWord ++ tailWord_1857200) baseStart_1857200 baseEnd_1857200 := by
    simpa [prefixWord, tailWord_1857200, baseEnd_1857200] using wordTrace_append hprefix tailTrace_1857200
  have hstable : (prefixWord ++ tailWord_1857200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857200).length < 2 ^ (prefixWord ++ tailWord_1857200).sum := by decide
  have hdescent : baseEnd_1857200 < baseStart_1857200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857214 : List Nat := [4, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_1857214 : Nat := 118140960795 + 1857214 * 2 ^ 59
def prefixEnd_1857214 : Nat := 4983230072969 + 3 ^ 40 * 1857214 * 2
def baseEnd_1857214 : Nat := 423841537893067500170593

theorem tailTrace_1857214 : CollatzResearch.WordTrace tailWord_1857214 prefixEnd_1857214 423841537893067500170593 := by
  unfold tailWord_1857214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8467269936704792467971337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45158772995758893162513797 8467269936704792467971337)
  ·
    refine ⟨6350452452528594350978503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8467269936704792467971337 6350452452528594350978503)
    ·
      refine ⟨9525678678792891526467755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6350452452528594350978503 9525678678792891526467755)
      ·
        refine ⟨14288518018189337289701633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9525678678792891526467755 14288518018189337289701633)
        ·
          refine ⟨10716388513642002967276225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14288518018189337289701633 10716388513642002967276225)
          ·
            refine ⟨8037291385231502225457169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10716388513642002967276225 8037291385231502225457169)
            ·
              refine ⟨6027968538923626669092877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8037291385231502225457169 6027968538923626669092877)
              ·
                refine ⟨2260488202096360000909829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6027968538923626669092877 2260488202096360000909829)
                ·
                  refine ⟨423841537893067500170593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2260488202096360000909829 423841537893067500170593)
                  ·
                    rfl

theorem cell21_1857214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_1857214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1857214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1857214 prefixEnd_1857214 := by exact prefixLift 1857214
  have htrace : WordTrace (prefixWord ++ tailWord_1857214) baseStart_1857214 baseEnd_1857214 := by
    simpa [prefixWord, tailWord_1857214, baseEnd_1857214] using wordTrace_append hprefix tailTrace_1857214
  have hstable : (prefixWord ++ tailWord_1857214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857214).length < 2 ^ (prefixWord ++ tailWord_1857214).sum := by decide
  have hdescent : baseEnd_1857214 < baseStart_1857214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857245 : List Nat := [1, 4, 3, 3, 1, 1, 8]
def baseStart_1857245 : Nat := 118140960795 + 1857245 * 2 ^ 59
def prefixEnd_1857245 : Nat := 4983230072969 + 3 ^ 40 * 1857245 * 2
def baseEnd_1857245 : Nat := 47094290279490926128207

theorem tailTrace_1857245 : CollatzResearch.WordTrace tailWord_1857245 prefixEnd_1857245 47094290279490926128207 := by
  unfold tailWord_1857245
  simp only [CollatzResearch.WordTrace]
  refine ⟨67739290156526032038149189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45159526771017354692099459 67739290156526032038149189)
  ·
    refine ⟨12701116904348631007152973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67739290156526032038149189 12701116904348631007152973)
    ·
      refine ⟨4762918839130736627682365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12701116904348631007152973 4762918839130736627682365)
      ·
        refine ⟨1786094564674026235380887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4762918839130736627682365 1786094564674026235380887)
        ·
          refine ⟨2679141847011039353071331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1786094564674026235380887 2679141847011039353071331)
          ·
            refine ⟨4018712770516559029606997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2679141847011039353071331 4018712770516559029606997)
            ·
              refine ⟨47094290279490926128207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4018712770516559029606997 47094290279490926128207)
              ·
                rfl

theorem cell21_1857245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 8].length) (baseStart_1857245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1857245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1857245 prefixEnd_1857245 := by exact prefixLift 1857245
  have htrace : WordTrace (prefixWord ++ tailWord_1857245) baseStart_1857245 baseEnd_1857245 := by
    simpa [prefixWord, tailWord_1857245, baseEnd_1857245] using wordTrace_append hprefix tailTrace_1857245
  have hstable : (prefixWord ++ tailWord_1857245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857245).length < 2 ^ (prefixWord ++ tailWord_1857245).sum := by decide
  have hdescent : baseEnd_1857245 < baseStart_1857245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857259 : List Nat := [1, 1, 1, 1, 2, 4, 4, 4, 3]
def baseStart_1857259 : Nat := 118140960795 + 1857259 * 2 ^ 59
def prefixEnd_1857259 : Nat := 4983230072969 + 3 ^ 40 * 1857259 * 2
def baseEnd_1857259 : Nat := 423851807506157421920501

theorem tailTrace_1857259 : CollatzResearch.WordTrace tailWord_1857259 prefixEnd_1857259 423851807506157421920501 := by
  unfold tailWord_1857259
  simp only [CollatzResearch.WordTrace]
  refine ⟨67739800778475312429158831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45159867185650208286105887 67739800778475312429158831)
  ·
    refine ⟨101609701167712968643738247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67739800778475312429158831 101609701167712968643738247)
    ·
      refine ⟨152414551751569452965607371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101609701167712968643738247 152414551751569452965607371)
      ·
        refine ⟨228621827627354179448411057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152414551751569452965607371 228621827627354179448411057)
        ·
          refine ⟨171466370720515634586308293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228621827627354179448411057 171466370720515634586308293)
          ·
            refine ⟨32149944510096681484932805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171466370720515634586308293 32149944510096681484932805)
            ·
              refine ⟨6028114595643127778424901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32149944510096681484932805 6028114595643127778424901)
              ·
                refine ⟨1130271486683086458454669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6028114595643127778424901 1130271486683086458454669)
                ·
                  refine ⟨423851807506157421920501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1130271486683086458454669 423851807506157421920501)
                  ·
                    rfl

theorem cell21_1857259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4, 3].length) (baseStart_1857259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1857259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1857259 prefixEnd_1857259 := by exact prefixLift 1857259
  have htrace : WordTrace (prefixWord ++ tailWord_1857259) baseStart_1857259 baseEnd_1857259 := by
    simpa [prefixWord, tailWord_1857259, baseEnd_1857259] using wordTrace_append hprefix tailTrace_1857259
  have hstable : (prefixWord ++ tailWord_1857259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857259).length < 2 ^ (prefixWord ++ tailWord_1857259).sum := by decide
  have hdescent : baseEnd_1857259 < baseStart_1857259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857310 : List Nat := [4, 3, 2, 2, 1, 2, 1, 1, 5]
def baseStart_1857310 : Nat := 118140960795 + 1857310 * 2 ^ 59
def prefixEnd_1857310 : Nat := 4983230072969 + 3 ^ 40 * 1857310 * 2
def baseEnd_1857310 : Nat := 423863446400992666570397

theorem tailTrace_1857310 : CollatzResearch.WordTrace tailWord_1857310 prefixEnd_1857310 423863446400992666570397 := by
  unfold tailWord_1857310
  simp only [CollatzResearch.WordTrace]
  refine ⟨8467707612661318517408173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45161107267527032092843589 8467707612661318517408173)
  ·
    refine ⟨3175390354747994444028065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8467707612661318517408173 3175390354747994444028065)
    ·
      refine ⟨2381542766060995833021049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3175390354747994444028065 2381542766060995833021049)
      ·
        refine ⟨1786157074545746874765787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2381542766060995833021049 1786157074545746874765787)
        ·
          refine ⟨2679235611818620312148681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1786157074545746874765787 2679235611818620312148681)
          ·
            refine ⟨2009426708863965234111511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2679235611818620312148681 2009426708863965234111511)
            ·
              refine ⟨3014140063295947851167267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2009426708863965234111511 3014140063295947851167267)
              ·
                refine ⟨4521210094943921776750901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3014140063295947851167267 4521210094943921776750901)
                ·
                  refine ⟨423863446400992666570397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4521210094943921776750901 423863446400992666570397)
                  ·
                    rfl

theorem cell21_1857310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_1857310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1857310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1857310 prefixEnd_1857310 := by exact prefixLift 1857310
  have htrace : WordTrace (prefixWord ++ tailWord_1857310) baseStart_1857310 baseEnd_1857310 := by
    simpa [prefixWord, tailWord_1857310, baseEnd_1857310] using wordTrace_append hprefix tailTrace_1857310
  have hstable : (prefixWord ++ tailWord_1857310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857310).length < 2 ^ (prefixWord ++ tailWord_1857310).sum := by decide
  have hdescent : baseEnd_1857310 < baseStart_1857310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857408 : List Nat := [2, 1, 1, 2, 1, 2, 4, 2, 6]
def baseStart_1857408 : Nat := 118140960795 + 1857408 * 2 ^ 59
def prefixEnd_1857408 : Nat := 4983230072969 + 3 ^ 40 * 1857408 * 2
def baseEnd_1857408 : Nat := 423885811336166273936863

theorem tailTrace_1857408 : CollatzResearch.WordTrace tailWord_1857408 prefixEnd_1857408 423885811336166273936863 := by
  unfold tailWord_1857408
  simp only [CollatzResearch.WordTrace]
  refine ⟨33872617627467755438166439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45163490169957007250888585 33872617627467755438166439)
  ·
    refine ⟨50808926441201633157249659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33872617627467755438166439 50808926441201633157249659)
    ·
      refine ⟨76213389661802449735874489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50808926441201633157249659 76213389661802449735874489)
      ·
        refine ⟨57160042246351837301905867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76213389661802449735874489 57160042246351837301905867)
        ·
          refine ⟨85740063369527755952858801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57160042246351837301905867 85740063369527755952858801)
          ·
            refine ⟨64305047527145816964644101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85740063369527755952858801 64305047527145816964644101)
            ·
              refine ⟨12057196411339840680870769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64305047527145816964644101 12057196411339840680870769)
              ·
                refine ⟨9042897308504880510653077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12057196411339840680870769 9042897308504880510653077)
                ·
                  refine ⟨423885811336166273936863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9042897308504880510653077 423885811336166273936863)
                  ·
                    rfl

theorem cell21_1857408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_1857408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1857408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1857408 prefixEnd_1857408 := by exact prefixLift 1857408
  have htrace : WordTrace (prefixWord ++ tailWord_1857408) baseStart_1857408 baseEnd_1857408 := by
    simpa [prefixWord, tailWord_1857408, baseEnd_1857408] using wordTrace_append hprefix tailTrace_1857408
  have hstable : (prefixWord ++ tailWord_1857408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857408).length < 2 ^ (prefixWord ++ tailWord_1857408).sum := by decide
  have hdescent : baseEnd_1857408 < baseStart_1857408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857411 : List Nat := [1, 1, 1, 3, 4, 2, 1, 5, 3]
def baseStart_1857411 : Nat := 118140960795 + 1857411 * 2 ^ 59
def prefixEnd_1857411 : Nat := 4983230072969 + 3 ^ 40 * 1857411 * 2
def baseEnd_1857411 : Nat := 423886495977038935386857

theorem tailTrace_1857411 : CollatzResearch.WordTrace tailWord_1857411 prefixEnd_1857411 423886495977038935386857 := by
  unfold tailWord_1857411
  simp only [CollatzResearch.WordTrace]
  refine ⟨67745344673924642388692087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45163563115949761592461391 67745344673924642388692087)
  ·
    refine ⟨101618017010886963583038131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67745344673924642388692087 101618017010886963583038131)
    ·
      refine ⟨152427025516330445374557197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101618017010886963583038131 152427025516330445374557197)
      ·
        refine ⟨57160134568623917015458949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152427025516330445374557197 57160134568623917015458949)
        ·
          refine ⟨10717525231616984440398553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57160134568623917015458949 10717525231616984440398553)
          ·
            refine ⟨8038143923712738330298915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10717525231616984440398553 8038143923712738330298915)
            ·
              refine ⟨12057215885569107495448373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8038143923712738330298915 12057215885569107495448373)
              ·
                refine ⟨1130363989272103827698285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12057215885569107495448373 1130363989272103827698285)
                ·
                  refine ⟨423886495977038935386857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1130363989272103827698285 423886495977038935386857)
                  ·
                    rfl

theorem cell21_1857411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 3].length) (baseStart_1857411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1857411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1857411 prefixEnd_1857411 := by exact prefixLift 1857411
  have htrace : WordTrace (prefixWord ++ tailWord_1857411) baseStart_1857411 baseEnd_1857411 := by
    simpa [prefixWord, tailWord_1857411, baseEnd_1857411] using wordTrace_append hprefix tailTrace_1857411
  have hstable : (prefixWord ++ tailWord_1857411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857411).length < 2 ^ (prefixWord ++ tailWord_1857411).sum := by decide
  have hdescent : baseEnd_1857411 < baseStart_1857411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857425 : List Nat := [1, 2, 2, 1, 1, 1, 7, 2, 4]
def baseStart_1857425 : Nat := 118140960795 + 1857425 * 2 ^ 59
def prefixEnd_1857425 : Nat := 4983230072969 + 3 ^ 40 * 1857425 * 2
def baseEnd_1857425 : Nat := 423889690967778022153495

theorem tailTrace_1857425 : CollatzResearch.WordTrace tailWord_1857425 prefixEnd_1857425 423889690967778022153495 := by
  unfold tailWord_1857425
  simp only [CollatzResearch.WordTrace]
  refine ⟨67745855295873922779701729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45163903530582615186467819 67745855295873922779701729)
  ·
    refine ⟨50809391471905442084776297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67745855295873922779701729 50809391471905442084776297)
    ·
      refine ⟨38107043603929081563582223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50809391471905442084776297 38107043603929081563582223)
      ·
        refine ⟨57160565405893622345373335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38107043603929081563582223 57160565405893622345373335)
        ·
          refine ⟨85740848108840433518060003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57160565405893622345373335 85740848108840433518060003)
          ·
            refine ⟨128611272163260650277090005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85740848108840433518060003 128611272163260650277090005)
            ·
              refine ⟨3014326691326421490869297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 128611272163260650277090005 3014326691326421490869297)
              ·
                refine ⟨2260745018494816118151973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3014326691326421490869297 2260745018494816118151973)
                ·
                  refine ⟨423889690967778022153495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2260745018494816118151973 423889690967778022153495)
                  ·
                    rfl

theorem cell21_1857425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_1857425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1857425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1857425 prefixEnd_1857425 := by exact prefixLift 1857425
  have htrace : WordTrace (prefixWord ++ tailWord_1857425) baseStart_1857425 baseEnd_1857425 := by
    simpa [prefixWord, tailWord_1857425, baseEnd_1857425] using wordTrace_append hprefix tailTrace_1857425
  have hstable : (prefixWord ++ tailWord_1857425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857425).length < 2 ^ (prefixWord ++ tailWord_1857425).sum := by decide
  have hdescent : baseEnd_1857425 < baseStart_1857425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857428 : List Nat := [2, 4, 2, 1, 1, 2, 2, 4, 3]
def baseStart_1857428 : Nat := 118140960795 + 1857428 * 2 ^ 59
def prefixEnd_1857428 : Nat := 4983230072969 + 3 ^ 40 * 1857428 * 2
def baseEnd_1857428 : Nat := 423890375608650683603489

theorem tailTrace_1857428 : CollatzResearch.WordTrace tailWord_1857428 prefixEnd_1857428 423890375608650683603489 := by
  unfold tailWord_1857428
  simp only [CollatzResearch.WordTrace]
  refine ⟨33872982357431527146030469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45163976476575369528040625 33872982357431527146030469)
  ·
    refine ⟨6351184192018411339880713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33872982357431527146030469 6351184192018411339880713)
    ·
      refine ⟨4763388144013808504910535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6351184192018411339880713 4763388144013808504910535)
      ·
        refine ⟨7145082216020712757365803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4763388144013808504910535 7145082216020712757365803)
        ·
          refine ⟨10717623324031069136048705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7145082216020712757365803 10717623324031069136048705)
          ·
            refine ⟨8038217493023301852036529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10717623324031069136048705 8038217493023301852036529)
            ·
              refine ⟨6028663119767476389027397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8038217493023301852036529 6028663119767476389027397)
              ·
                refine ⟨1130374334956401822942637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6028663119767476389027397 1130374334956401822942637)
                ·
                  refine ⟨423890375608650683603489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1130374334956401822942637 423890375608650683603489)
                  ·
                    rfl

theorem cell21_1857428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_1857428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1857428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1857428 prefixEnd_1857428 := by exact prefixLift 1857428
  have htrace : WordTrace (prefixWord ++ tailWord_1857428) baseStart_1857428 baseEnd_1857428 := by
    simpa [prefixWord, tailWord_1857428, baseEnd_1857428] using wordTrace_append hprefix tailTrace_1857428
  have hstable : (prefixWord ++ tailWord_1857428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857428).length < 2 ^ (prefixWord ++ tailWord_1857428).sum := by decide
  have hdescent : baseEnd_1857428 < baseStart_1857428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857636 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 6]
def baseStart_1857636 : Nat := 118140960795 + 1857636 * 2 ^ 59
def prefixEnd_1857636 : Nat := 4983230072969 + 3 ^ 40 * 1857636 * 2
def baseEnd_1857636 : Nat := 423937844042488544136397

theorem tailTrace_1857636 : CollatzResearch.WordTrace tailWord_1857636 prefixEnd_1857636 423937844042488544136397 := by
  unfold tailWord_1857636
  simp only [CollatzResearch.WordTrace]
  refine ⟨33876775549054752907816381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45169034065406337210421841 33876775549054752907816381)
  ·
    refine ⟨12703790830895532340431143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33876775549054752907816381 12703790830895532340431143)
    ·
      refine ⟨19055686246343298510646715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12703790830895532340431143 19055686246343298510646715)
      ·
        refine ⟨28583529369514947765970073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19055686246343298510646715 28583529369514947765970073)
        ·
          refine ⟨21437647027136210824477555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28583529369514947765970073 21437647027136210824477555)
          ·
            refine ⟨32156470540704316236716333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21437647027136210824477555 32156470540704316236716333)
            ·
              refine ⟨12058676452764118588768625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32156470540704316236716333 12058676452764118588768625)
              ·
                refine ⟨9044007339573088941576469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12058676452764118588768625 9044007339573088941576469)
                ·
                  refine ⟨423937844042488544136397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9044007339573088941576469 423937844042488544136397)
                  ·
                    rfl

theorem cell21_1857636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_1857636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1857636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1857636 prefixEnd_1857636 := by exact prefixLift 1857636
  have htrace : WordTrace (prefixWord ++ tailWord_1857636) baseStart_1857636 baseEnd_1857636 := by
    simpa [prefixWord, tailWord_1857636, baseEnd_1857636] using wordTrace_append hprefix tailTrace_1857636
  have hstable : (prefixWord ++ tailWord_1857636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857636).length < 2 ^ (prefixWord ++ tailWord_1857636).sum := by decide
  have hdescent : baseEnd_1857636 < baseStart_1857636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857667 : List Nat := [1, 1, 1, 3, 3, 4, 2, 6]
def baseStart_1857667 : Nat := 118140960795 + 1857667 * 2 ^ 59
def prefixEnd_1857667 : Nat := 4983230072969 + 3 ^ 40 * 1857667 * 2
def baseEnd_1857667 : Nat := 141314972888279793039889

theorem tailTrace_1857667 : CollatzResearch.WordTrace tailWord_1857667 prefixEnd_1857667 141314972888279793039889 := by
  unfold tailWord_1857667
  simp only [CollatzResearch.WordTrace]
  refine ⟨67754681760997198110011255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45169787840664798740007503 67754681760997198110011255)
  ·
    refine ⟨101632022641495797165016883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67754681760997198110011255 101632022641495797165016883)
    ·
      refine ⟨152448033962243695747525325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101632022641495797165016883 152448033962243695747525325)
      ·
        refine ⟨57168012735841385905321997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152448033962243695747525325 57168012735841385905321997)
        ·
          refine ⟨21438004775940519714495749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57168012735841385905321997 21438004775940519714495749)
          ·
            refine ⟨4019625895488847446467953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21438004775940519714495749 4019625895488847446467953)
            ·
              refine ⟨3014719421616635584850965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4019625895488847446467953 3014719421616635584850965)
              ·
                refine ⟨141314972888279793039889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3014719421616635584850965 141314972888279793039889)
                ·
                  rfl

theorem cell21_1857667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 6].length) (baseStart_1857667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1857667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1857667 prefixEnd_1857667 := by exact prefixLift 1857667
  have htrace : WordTrace (prefixWord ++ tailWord_1857667) baseStart_1857667 baseEnd_1857667 := by
    simpa [prefixWord, tailWord_1857667, baseEnd_1857667] using wordTrace_append hprefix tailTrace_1857667
  have hstable : (prefixWord ++ tailWord_1857667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857667).length < 2 ^ (prefixWord ++ tailWord_1857667).sum := by decide
  have hdescent : baseEnd_1857667 < baseStart_1857667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857743 : List Nat := [1, 1, 2, 1, 1, 3, 7, 5]
def baseStart_1857743 : Nat := 118140960795 + 1857743 * 2 ^ 59
def prefixEnd_1857743 : Nat := 4983230072969 + 3 ^ 40 * 1857743 * 2
def baseEnd_1857743 : Nat := 141320754300093378617615

theorem tailTrace_1857743 : CollatzResearch.WordTrace tailWord_1857743 prefixEnd_1857743 141320754300093378617615 := by
  unfold tailWord_1857743
  simp only [CollatzResearch.WordTrace]
  refine ⟨67757453708721863089777883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45171635805814575393185255 67757453708721863089777883)
  ·
    refine ⟨101636180563082794634666825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67757453708721863089777883 101636180563082794634666825)
    ·
      refine ⟨76227135422312095976000119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101636180563082794634666825 76227135422312095976000119)
      ·
        refine ⟨114340703133468143964000179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76227135422312095976000119 114340703133468143964000179)
        ·
          refine ⟨171511054700202215946000269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114340703133468143964000179 171511054700202215946000269)
          ·
            refine ⟨64316645512575830979750101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171511054700202215946000269 64316645512575830979750101)
            ·
              refine ⟨1507421379200996038587893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 64316645512575830979750101 1507421379200996038587893)
              ·
                refine ⟨141320754300093378617615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1507421379200996038587893 141320754300093378617615)
                ·
                  rfl

theorem cell21_1857743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 5].length) (baseStart_1857743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1857743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1857743 prefixEnd_1857743 := by exact prefixLift 1857743
  have htrace : WordTrace (prefixWord ++ tailWord_1857743) baseStart_1857743 baseEnd_1857743 := by
    simpa [prefixWord, tailWord_1857743, baseEnd_1857743] using wordTrace_append hprefix tailTrace_1857743
  have hstable : (prefixWord ++ tailWord_1857743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857743).length < 2 ^ (prefixWord ++ tailWord_1857743).sum := by decide
  have hdescent : baseEnd_1857743 < baseStart_1857743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857763 : List Nat := [1, 1, 1, 8, 1, 2, 1, 2, 4]
def baseStart_1857763 : Nat := 118140960795 + 1857763 * 2 ^ 59
def prefixEnd_1857763 : Nat := 4983230072969 + 3 ^ 40 * 1857763 * 2
def baseEnd_1857763 : Nat := 423966827172764545519471

theorem tailTrace_1857763 : CollatzResearch.WordTrace tailWord_1857763 prefixEnd_1857763 423966827172764545519471 := by
  unfold tailWord_1857763
  simp only [CollatzResearch.WordTrace]
  refine ⟨67758183168649406505505943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45172122112432937670337295 67758183168649406505505943)
  ·
    refine ⟨101637274752974109758258915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67758183168649406505505943 101637274752974109758258915)
    ·
      refine ⟨152455912129461164637388373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101637274752974109758258915 152455912129461164637388373)
      ·
        refine ⟨1786592720267123023094395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 152455912129461164637388373 1786592720267123023094395)
        ·
          refine ⟨2679889080400684534641593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1786592720267123023094395 2679889080400684534641593)
          ·
            refine ⟨2009916810300513400981195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2679889080400684534641593 2009916810300513400981195)
            ·
              refine ⟨3014875215450770101471793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2009916810300513400981195 3014875215450770101471793)
              ·
                refine ⟨2261156411588077576103845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3014875215450770101471793 2261156411588077576103845)
                ·
                  refine ⟨423966827172764545519471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2261156411588077576103845 423966827172764545519471)
                  ·
                    rfl

theorem cell21_1857763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 2, 4].length) (baseStart_1857763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1857763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1857763 prefixEnd_1857763 := by exact prefixLift 1857763
  have htrace : WordTrace (prefixWord ++ tailWord_1857763) baseStart_1857763 baseEnd_1857763 := by
    simpa [prefixWord, tailWord_1857763, baseEnd_1857763] using wordTrace_append hprefix tailTrace_1857763
  have hstable : (prefixWord ++ tailWord_1857763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857763).length < 2 ^ (prefixWord ++ tailWord_1857763).sum := by decide
  have hdescent : baseEnd_1857763 < baseStart_1857763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857822 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1857822 : Nat := 118140960795 + 1857822 * 2 ^ 59
def prefixEnd_1857822 : Nat := 4983230072969 + 3 ^ 40 * 1857822 * 2
def baseEnd_1857822 : Nat := 423980291776593554036017

theorem tailTrace_1857822 : CollatzResearch.WordTrace tailWord_1857822 prefixEnd_1857822 423980291776593554036017 := by
  unfold tailWord_1857822
  simp only [CollatzResearch.WordTrace]
  refine ⟨8470041884429457447737965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45173556716957106387935813 8470041884429457447737965)
  ·
    refine ⟨3176265706661046542901737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8470041884429457447737965 3176265706661046542901737)
    ·
      refine ⟨2382199279995784907176303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3176265706661046542901737 2382199279995784907176303)
      ·
        refine ⟨3573298919993677360764455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2382199279995784907176303 3573298919993677360764455)
        ·
          refine ⟨5359948379990516041146683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3573298919993677360764455 5359948379990516041146683)
          ·
            refine ⟨8039922569985774061720025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5359948379990516041146683 8039922569985774061720025)
            ·
              refine ⟨6029941927489330546290019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8039922569985774061720025 6029941927489330546290019)
              ·
                refine ⟨9044912891233995819435029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6029941927489330546290019 9044912891233995819435029)
                ·
                  refine ⟨423980291776593554036017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9044912891233995819435029 423980291776593554036017)
                  ·
                    rfl

theorem cell21_1857822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1857822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1857822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1857822 prefixEnd_1857822 := by exact prefixLift 1857822
  have htrace : WordTrace (prefixWord ++ tailWord_1857822) baseStart_1857822 baseEnd_1857822 := by
    simpa [prefixWord, tailWord_1857822, baseEnd_1857822] using wordTrace_append hprefix tailTrace_1857822
  have hstable : (prefixWord ++ tailWord_1857822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857822).length < 2 ^ (prefixWord ++ tailWord_1857822).sum := by decide
  have hdescent : baseEnd_1857822 < baseStart_1857822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857895 : List Nat := [1, 1, 5, 1, 3, 1, 3, 6]
def baseStart_1857895 : Nat := 118140960795 + 1857895 * 2 ^ 59
def prefixEnd_1857895 : Nat := 4983230072969 + 3 ^ 40 * 1857895 * 2
def baseEnd_1857895 : Nat := 141332317123720549773067

theorem tailTrace_1857895 : CollatzResearch.WordTrace tailWord_1857895 prefixEnd_1857895 141332317123720549773067 := by
  unfold tailWord_1857895
  simp only [CollatzResearch.WordTrace]
  refine ⟨67762997604171193049311139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45175331736114128699540759 67762997604171193049311139)
  ·
    refine ⟨101644496406256789573966709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67762997604171193049311139 101644496406256789573966709)
    ·
      refine ⟨9529171538086574022559379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101644496406256789573966709 9529171538086574022559379)
      ·
        refine ⟨14293757307129861033839069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9529171538086574022559379 14293757307129861033839069)
        ·
          refine ⟨5360158990173697887689651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14293757307129861033839069 5360158990173697887689651)
          ·
            refine ⟨8040238485260546831534477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5360158990173697887689651 8040238485260546831534477)
            ·
              refine ⟨3015089431972705061825429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8040238485260546831534477 3015089431972705061825429)
              ·
                refine ⟨141332317123720549773067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3015089431972705061825429 141332317123720549773067)
                ·
                  rfl

theorem cell21_1857895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 6].length) (baseStart_1857895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1857895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1857895 prefixEnd_1857895 := by exact prefixLift 1857895
  have htrace : WordTrace (prefixWord ++ tailWord_1857895) baseStart_1857895 baseEnd_1857895 := by
    simpa [prefixWord, tailWord_1857895, baseEnd_1857895] using wordTrace_append hprefix tailTrace_1857895
  have hstable : (prefixWord ++ tailWord_1857895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857895).length < 2 ^ (prefixWord ++ tailWord_1857895).sum := by decide
  have hdescent : baseEnd_1857895 < baseStart_1857895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857957 : List Nat := [1, 3, 1, 2, 1, 1, 7, 1, 4]
def baseStart_1857957 : Nat := 118140960795 + 1857957 * 2 ^ 59
def prefixEnd_1857957 : Nat := 4983230072969 + 3 ^ 40 * 1857957 * 2
def baseEnd_1857957 : Nat := 424011100615863319285741

theorem tailTrace_1857957 : CollatzResearch.WordTrace tailWord_1857957 prefixEnd_1857957 424011100615863319285741 := by
  unfold tailWord_1857957
  simp only [CollatzResearch.WordTrace]
  refine ⟨67765258929946577638068125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45176839286631051758712083 67765258929946577638068125)
  ·
    refine ⟨25411972098729966614275547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67765258929946577638068125 25411972098729966614275547)
    ·
      refine ⟨38117958148094949921413321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25411972098729966614275547 38117958148094949921413321)
      ·
        refine ⟨28588468611071212441059991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38117958148094949921413321 28588468611071212441059991)
        ·
          refine ⟨42882702916606818661589987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28588468611071212441059991 42882702916606818661589987)
          ·
            refine ⟨64324054374910227992384981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42882702916606818661589987 64324054374910227992384981)
            ·
              refine ⟨1507595024411958468571523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 64324054374910227992384981 1507595024411958468571523)
              ·
                refine ⟨2261392536617937702857285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1507595024411958468571523 2261392536617937702857285)
                ·
                  refine ⟨424011100615863319285741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2261392536617937702857285 424011100615863319285741)
                  ·
                    rfl

theorem cell21_1857957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_1857957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1857957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1857957 prefixEnd_1857957 := by exact prefixLift 1857957
  have htrace : WordTrace (prefixWord ++ tailWord_1857957) baseStart_1857957 baseEnd_1857957 := by
    simpa [prefixWord, tailWord_1857957, baseEnd_1857957] using wordTrace_append hprefix tailTrace_1857957
  have hstable : (prefixWord ++ tailWord_1857957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857957).length < 2 ^ (prefixWord ++ tailWord_1857957).sum := by decide
  have hdescent : baseEnd_1857957 < baseStart_1857957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1857988 : List Nat := [2, 3, 3, 2, 2, 2, 7]
def baseStart_1857988 : Nat := 118140960795 + 1857988 * 2 ^ 59
def prefixEnd_1857988 : Nat := 4983230072969 + 3 ^ 40 * 1857988 * 2
def baseEnd_1857988 : Nat := 47113130582023794918779

theorem tailTrace_1857988 : CollatzResearch.WordTrace tailWord_1857988 prefixEnd_1857988 47113130582023794918779 := by
  unfold tailWord_1857988
  simp only [CollatzResearch.WordTrace]
  refine ⟨33883194796417134966223309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45177593061889513288297745 33883194796417134966223309)
  ·
    refine ⟨12706198048656425612333741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33883194796417134966223309 12706198048656425612333741)
    ·
      refine ⟨4764824268246159604625153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12706198048656425612333741 4764824268246159604625153)
      ·
        refine ⟨3573618201184619703468865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4764824268246159604625153 3573618201184619703468865)
        ·
          refine ⟨2680213650888464777601649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3573618201184619703468865 2680213650888464777601649)
          ·
            refine ⟨2010160238166348583201237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2680213650888464777601649 2010160238166348583201237)
            ·
              refine ⟨47113130582023794918779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2010160238166348583201237 47113130582023794918779)
              ·
                rfl

theorem cell21_1857988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 7].length) (baseStart_1857988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1857988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1857988 prefixEnd_1857988 := by exact prefixLift 1857988
  have htrace : WordTrace (prefixWord ++ tailWord_1857988) baseStart_1857988 baseEnd_1857988 := by
    simpa [prefixWord, tailWord_1857988, baseEnd_1857988] using wordTrace_append hprefix tailTrace_1857988
  have hstable : (prefixWord ++ tailWord_1857988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1857988).length < 2 ^ (prefixWord ++ tailWord_1857988).sum := by decide
  have hdescent : baseEnd_1857988 < baseStart_1857988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1857988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858016 : List Nat := [2, 1, 1, 3, 1, 1, 5, 3, 4]
def baseStart_1858016 : Nat := 118140960795 + 1858016 * 2 ^ 59
def prefixEnd_1858016 : Nat := 4983230072969 + 3 ^ 40 * 1858016 * 2
def baseEnd_1858016 : Nat := 424024565219692327802287

theorem tailTrace_1858016 : CollatzResearch.WordTrace tailWord_1858016 prefixEnd_1858016 424024565219692327802287 := by
  unfold tailWord_1858016
  simp only [CollatzResearch.WordTrace]
  refine ⟨33883705418366415357232951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45178273891155220476310601 33883705418366415357232951)
  ·
    refine ⟨50825558127549623035849427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33883705418366415357232951 50825558127549623035849427)
    ·
      refine ⟨76238337191324434553774141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50825558127549623035849427 76238337191324434553774141)
      ·
        refine ⟨28589376446746662957665303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76238337191324434553774141 28589376446746662957665303)
        ·
          refine ⟨42884064670119994436497955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28589376446746662957665303 42884064670119994436497955)
          ·
            refine ⟨64326097005179991654746933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42884064670119994436497955 64326097005179991654746933)
            ·
              refine ⟨6030571594235624217632525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64326097005179991654746933 6030571594235624217632525)
              ·
                refine ⟨2261464347838359081612197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6030571594235624217632525 2261464347838359081612197)
                ·
                  refine ⟨424024565219692327802287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2261464347838359081612197 424024565219692327802287)
                  ·
                    rfl

theorem cell21_1858016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_1858016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858016 prefixEnd_1858016 := by exact prefixLift 1858016
  have htrace : WordTrace (prefixWord ++ tailWord_1858016) baseStart_1858016 baseEnd_1858016 := by
    simpa [prefixWord, tailWord_1858016, baseEnd_1858016] using wordTrace_append hprefix tailTrace_1858016
  have hstable : (prefixWord ++ tailWord_1858016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858016).length < 2 ^ (prefixWord ++ tailWord_1858016).sum := by decide
  have hdescent : baseEnd_1858016 < baseStart_1858016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858106 : List Nat := [3, 1, 1, 1, 3, 4, 8]
def baseStart_1858106 : Nat := 118140960795 + 1858106 * 2 ^ 59
def prefixEnd_1858106 : Nat := 4983230072969 + 3 ^ 40 * 1858106 * 2
def baseEnd_1858106 : Nat := 47116122716208019033567

theorem tailTrace_1858106 : CollatzResearch.WordTrace tailWord_1858106 prefixEnd_1858106 47116122716208019033567 := by
  unfold tailWord_1858106
  simp only [CollatzResearch.WordTrace]
  refine ⟨16942673351601694021310543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45180462270937850723494781 16942673351601694021310543)
  ·
    refine ⟨25414010027402541031965815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16942673351601694021310543 25414010027402541031965815)
    ·
      refine ⟨38121015041103811547948723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25414010027402541031965815 38121015041103811547948723)
      ·
        refine ⟨57181522561655717321923085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38121015041103811547948723 57181522561655717321923085)
        ·
          refine ⟨21443070960620893995721157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57181522561655717321923085 21443070960620893995721157)
          ·
            refine ⟨4020575805116417624197717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21443070960620893995721157 4020575805116417624197717)
            ·
              refine ⟨47116122716208019033567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4020575805116417624197717 47116122716208019033567)
              ·
                rfl

theorem cell21_1858106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 8].length) (baseStart_1858106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858106 prefixEnd_1858106 := by exact prefixLift 1858106
  have htrace : WordTrace (prefixWord ++ tailWord_1858106) baseStart_1858106 baseEnd_1858106 := by
    simpa [prefixWord, tailWord_1858106, baseEnd_1858106] using wordTrace_append hprefix tailTrace_1858106
  have hstable : (prefixWord ++ tailWord_1858106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858106).length < 2 ^ (prefixWord ++ tailWord_1858106).sum := by decide
  have hdescent : baseEnd_1858106 < baseStart_1858106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858109 : List Nat := [1, 4, 1, 3, 2, 1, 3, 2, 4]
def baseStart_1858109 : Nat := 118140960795 + 1858109 * 2 ^ 59
def prefixEnd_1858109 : Nat := 4983230072969 + 3 ^ 40 * 1858109 * 2
def baseEnd_1858109 : Nat := 424045789086744832752097

theorem tailTrace_1858109 : CollatzResearch.WordTrace tailWord_1858109 prefixEnd_1858109 424045789086744832752097 := by
  unfold tailWord_1858109
  simp only [CollatzResearch.WordTrace]
  refine ⟨67770802825395907597601381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45180535216930605065067587 67770802825395907597601381)
  ·
    refine ⟨12707025529761732674550259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67770802825395907597601381 12707025529761732674550259)
    ·
      refine ⟨19060538294642599011825389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12707025529761732674550259 19060538294642599011825389)
      ·
        refine ⟨7147701860490974629434521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19060538294642599011825389 7147701860490974629434521)
        ·
          refine ⟨5360776395368230972075891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7147701860490974629434521 5360776395368230972075891)
          ·
            refine ⟨8041164593052346458113837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5360776395368230972075891 8041164593052346458113837)
            ·
              refine ⟨3015436722394629921792689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8041164593052346458113837 3015436722394629921792689)
              ·
                refine ⟨2261577541795972441344517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3015436722394629921792689 2261577541795972441344517)
                ·
                  refine ⟨424045789086744832752097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2261577541795972441344517 424045789086744832752097)
                  ·
                    rfl

theorem cell21_1858109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_1858109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858109 prefixEnd_1858109 := by exact prefixLift 1858109
  have htrace : WordTrace (prefixWord ++ tailWord_1858109) baseStart_1858109 baseEnd_1858109 := by
    simpa [prefixWord, tailWord_1858109, baseEnd_1858109] using wordTrace_append hprefix tailTrace_1858109
  have hstable : (prefixWord ++ tailWord_1858109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858109).length < 2 ^ (prefixWord ++ tailWord_1858109).sum := by decide
  have hdescent : baseEnd_1858109 < baseStart_1858109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858146 : List Nat := [3, 3, 2, 3, 2, 1, 1, 3, 3]
def baseStart_1858146 : Nat := 118140960795 + 1858146 * 2 ^ 59
def prefixEnd_1858146 : Nat := 4983230072969 + 3 ^ 40 * 1858146 * 2
def baseEnd_1858146 : Nat := 424054232990840990635355

theorem tailTrace_1858146 : CollatzResearch.WordTrace tailWord_1858146 prefixEnd_1858146 424054232990840990635355 := by
  unfold tailWord_1858146
  simp only [CollatzResearch.WordTrace]
  refine ⟨16943038081565465729174573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45181434884174575277798861 16943038081565465729174573)
  ·
    refine ⟨6353639280587049648440465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16943038081565465729174573 6353639280587049648440465)
    ·
      refine ⟨4765229460440287236330349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6353639280587049648440465 4765229460440287236330349)
      ·
        refine ⟨1786961047665107713623881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4765229460440287236330349 1786961047665107713623881)
        ·
          refine ⟨1340220785748830785217911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1786961047665107713623881 1340220785748830785217911)
          ·
            refine ⟨2010331178623246177826867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340220785748830785217911 2010331178623246177826867)
            ·
              refine ⟨3015496767934869266740301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2010331178623246177826867 3015496767934869266740301)
              ·
                refine ⟨1130811287975575975027613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3015496767934869266740301 1130811287975575975027613)
                ·
                  refine ⟨424054232990840990635355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1130811287975575975027613 424054232990840990635355)
                  ·
                    rfl

theorem cell21_1858146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_1858146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858146 prefixEnd_1858146 := by exact prefixLift 1858146
  have htrace : WordTrace (prefixWord ++ tailWord_1858146) baseStart_1858146 baseEnd_1858146 := by
    simpa [prefixWord, tailWord_1858146, baseEnd_1858146] using wordTrace_append hprefix tailTrace_1858146
  have hstable : (prefixWord ++ tailWord_1858146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858146).length < 2 ^ (prefixWord ++ tailWord_1858146).sum := by decide
  have hdescent : baseEnd_1858146 < baseStart_1858146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858272 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 9]
def baseStart_1858272 : Nat := 118140960795 + 1858272 * 2 ^ 59
def prefixEnd_1858272 : Nat := 4983230072969 + 3 ^ 40 * 1858272 * 2
def baseEnd_1858272 : Nat := 424082987907492771535097

theorem tailTrace_1858272 : CollatzResearch.WordTrace tailWord_1858272 prefixEnd_1858272 424082987907492771535097 := by
  unfold tailWord_1858272
  simp only [CollatzResearch.WordTrace]
  refine ⟨33888373961902693217892535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45184498615870257623856713 33888373961902693217892535)
  ·
    refine ⟨50832560942854039826838803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33888373961902693217892535 50832560942854039826838803)
    ·
      refine ⟨76248841414281059740258205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50832560942854039826838803 76248841414281059740258205)
      ·
        refine ⟨28593315530355397402596827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76248841414281059740258205 28593315530355397402596827)
        ·
          refine ⟨42889973295533096103895241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28593315530355397402596827 42889973295533096103895241)
          ·
            refine ⟨32167479971649822077921431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42889973295533096103895241 32167479971649822077921431)
            ·
              refine ⟨48251219957474733116882147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32167479971649822077921431 48251219957474733116882147)
              ·
                refine ⟨72376829936212099675323221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48251219957474733116882147 72376829936212099675323221)
                ·
                  refine ⟨424082987907492771535097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72376829936212099675323221 424082987907492771535097)
                  ·
                    rfl

theorem cell21_1858272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_1858272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858272 prefixEnd_1858272 := by exact prefixLift 1858272
  have htrace : WordTrace (prefixWord ++ tailWord_1858272) baseStart_1858272 baseEnd_1858272 := by
    simpa [prefixWord, tailWord_1858272, baseEnd_1858272] using wordTrace_append hprefix tailTrace_1858272
  have hstable : (prefixWord ++ tailWord_1858272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858272).length < 2 ^ (prefixWord ++ tailWord_1858272).sum := by decide
  have hdescent : baseEnd_1858272 < baseStart_1858272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858289 : List Nat := [1, 2, 2, 2, 2, 2, 4, 1, 5]
def baseStart_1858289 : Nat := 118140960795 + 1858289 * 2 ^ 59
def prefixEnd_1858289 : Nat := 4983230072969 + 3 ^ 40 * 1858289 * 2
def baseEnd_1858289 : Nat := 424086867539104519751729

theorem tailTrace_1858289 : CollatzResearch.WordTrace tailWord_1858289 prefixEnd_1858289 424086867539104519751729 := by
  unfold tailWord_1858289
  simp only [CollatzResearch.WordTrace]
  refine ⟨67777367964743798339153921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45184911976495865559435947 67777367964743798339153921)
  ·
    refine ⟨50833025973557848754365441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67777367964743798339153921 50833025973557848754365441)
    ·
      refine ⟨38124769480168386565774081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50833025973557848754365441 38124769480168386565774081)
      ·
        refine ⟨28593577110126289924330561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38124769480168386565774081 28593577110126289924330561)
        ·
          refine ⟨21445182832594717443247921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28593577110126289924330561 21445182832594717443247921)
          ·
            refine ⟨16083887124446038082435941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21445182832594717443247921 16083887124446038082435941)
            ·
              refine ⟨3015728835833632140456739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16083887124446038082435941 3015728835833632140456739)
              ·
                refine ⟨4523593253750448210685109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3015728835833632140456739 4523593253750448210685109)
                ·
                  refine ⟨424086867539104519751729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4523593253750448210685109 424086867539104519751729)
                  ·
                    rfl

theorem cell21_1858289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_1858289 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858289 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858289 prefixEnd_1858289 := by exact prefixLift 1858289
  have htrace : WordTrace (prefixWord ++ tailWord_1858289) baseStart_1858289 baseEnd_1858289 := by
    simpa [prefixWord, tailWord_1858289, baseEnd_1858289] using wordTrace_append hprefix tailTrace_1858289
  have hstable : (prefixWord ++ tailWord_1858289).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858289).length < 2 ^ (prefixWord ++ tailWord_1858289).sum := by decide
  have hdescent : baseEnd_1858289 < baseStart_1858289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858306 : List Nat := [3, 4, 1, 1, 1, 2, 2, 2, 5]
def baseStart_1858306 : Nat := 118140960795 + 1858306 * 2 ^ 59
def prefixEnd_1858306 : Nat := 4983230072969 + 3 ^ 40 * 1858306 * 2
def baseEnd_1858306 : Nat := 424090747170716267968361

theorem tailTrace_1858306 : CollatzResearch.WordTrace tailWord_1858306 prefixEnd_1858306 424090747170716267968361 := by
  unfold tailWord_1858306
  simp only [CollatzResearch.WordTrace]
  refine ⟨16944497001420552560630693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45185325337121473495015181 16944497001420552560630693)
  ·
    refine ⟨3177093187766353605118255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16944497001420552560630693 3177093187766353605118255)
    ·
      refine ⟨4765639781649530407677383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3177093187766353605118255 4765639781649530407677383)
      ·
        refine ⟨7148459672474295611516075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4765639781649530407677383 7148459672474295611516075)
        ·
          refine ⟨10722689508711443417274113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7148459672474295611516075 10722689508711443417274113)
          ·
            refine ⟨8042017131533582562955585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10722689508711443417274113 8042017131533582562955585)
            ·
              refine ⟨6031512848650186922216689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8042017131533582562955585 6031512848650186922216689)
              ·
                refine ⟨4523634636487640191662517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6031512848650186922216689 4523634636487640191662517)
                ·
                  refine ⟨424090747170716267968361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4523634636487640191662517 424090747170716267968361)
                  ·
                    rfl

theorem cell21_1858306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_1858306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858306 prefixEnd_1858306 := by exact prefixLift 1858306
  have htrace : WordTrace (prefixWord ++ tailWord_1858306) baseStart_1858306 baseEnd_1858306 := by
    simpa [prefixWord, tailWord_1858306, baseEnd_1858306] using wordTrace_append hprefix tailTrace_1858306
  have hstable : (prefixWord ++ tailWord_1858306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858306).length < 2 ^ (prefixWord ++ tailWord_1858306).sum := by decide
  have hdescent : baseEnd_1858306 < baseStart_1858306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858340 : List Nat := [2, 3, 1, 3, 3, 1, 3, 2, 3]
def baseStart_1858340 : Nat := 118140960795 + 1858340 * 2 ^ 59
def prefixEnd_1858340 : Nat := 4983230072969 + 3 ^ 40 * 1858340 * 2
def baseEnd_1858340 : Nat := 424098506433939764401625

theorem tailTrace_1858340 : CollatzResearch.WordTrace tailWord_1858340 prefixEnd_1858340 424098506433939764401625 := by
  unfold tailWord_1858340
  simp only [CollatzResearch.WordTrace]
  refine ⟨33889614043779517024630237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45186152058372689366173649 33889614043779517024630237)
  ·
    refine ⟨12708605266417318884236339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33889614043779517024630237 12708605266417318884236339)
    ·
      refine ⟨19062907899625978326354509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12708605266417318884236339 19062907899625978326354509)
      ·
        refine ⟨7148590462359741872382941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19062907899625978326354509 7148590462359741872382941)
        ·
          refine ⟨2680721423384903202143603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7148590462359741872382941 2680721423384903202143603)
          ·
            refine ⟨4021082135077354803215405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2680721423384903202143603 4021082135077354803215405)
            ·
              refine ⟨1507905800654008051205777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4021082135077354803215405 1507905800654008051205777)
              ·
                refine ⟨1130929350490506038404333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1507905800654008051205777 1130929350490506038404333)
                ·
                  refine ⟨424098506433939764401625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1130929350490506038404333 424098506433939764401625)
                  ·
                    rfl

theorem cell21_1858340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_1858340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858340 prefixEnd_1858340 := by exact prefixLift 1858340
  have htrace : WordTrace (prefixWord ++ tailWord_1858340) baseStart_1858340 baseEnd_1858340 := by
    simpa [prefixWord, tailWord_1858340, baseEnd_1858340] using wordTrace_append hprefix tailTrace_1858340
  have hstable : (prefixWord ++ tailWord_1858340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858340).length < 2 ^ (prefixWord ++ tailWord_1858340).sum := by decide
  have hdescent : baseEnd_1858340 < baseStart_1858340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858393 : List Nat := [1, 2, 1, 2, 2, 13]
def baseStart_1858393 : Nat := 118140960795 + 1858393 * 2 ^ 59
def prefixEnd_1858393 : Nat := 4983230072969 + 3 ^ 40 * 1858393 * 2
def baseEnd_1858393 : Nat := 15707800065037905556229

theorem tailTrace_1858393 : CollatzResearch.WordTrace tailWord_1858393 prefixEnd_1858393 15707800065037905556229 := by
  unfold tailWord_1858393
  simp only [CollatzResearch.WordTrace]
  refine ⟨67781161156367024100939833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45187440770911349400626555 67781161156367024100939833)
  ·
    refine ⟨50835870867275268075704875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67781161156367024100939833 50835870867275268075704875)
    ·
      refine ⟨76253806300912902113557313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50835870867275268075704875 76253806300912902113557313)
      ·
        refine ⟨57190354725684676585167985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76253806300912902113557313 57190354725684676585167985)
        ·
          refine ⟨42892766044263507438875989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57190354725684676585167985 42892766044263507438875989)
          ·
            refine ⟨15707800065037905556229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 42892766044263507438875989 15707800065037905556229)
            ·
              rfl

theorem cell21_1858393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 13].length) (baseStart_1858393 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858393 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858393 prefixEnd_1858393 := by exact prefixLift 1858393
  have htrace : WordTrace (prefixWord ++ tailWord_1858393) baseStart_1858393 baseEnd_1858393 := by
    simpa [prefixWord, tailWord_1858393, baseEnd_1858393] using wordTrace_append hprefix tailTrace_1858393
  have hstable : (prefixWord ++ tailWord_1858393).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858393).length < 2 ^ (prefixWord ++ tailWord_1858393).sum := by decide
  have hdescent : baseEnd_1858393 < baseStart_1858393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858455 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 6]
def baseStart_1858455 : Nat := 118140960795 + 1858455 * 2 ^ 59
def prefixEnd_1858455 : Nat := 4983230072969 + 3 ^ 40 * 1858455 * 2
def baseEnd_1858455 : Nat := 424124751000725119984723

theorem tailTrace_1858455 : CollatzResearch.WordTrace tailWord_1858455 prefixEnd_1858455 424124751000725119984723 := by
  unfold tailWord_1858455
  simp only [CollatzResearch.WordTrace]
  refine ⟨67783422482142408689696819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45188948321428272459797879 67783422482142408689696819)
  ·
    refine ⟨101675133723213613034545229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67783422482142408689696819 101675133723213613034545229)
    ·
      refine ⟨38128175146205104887954461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101675133723213613034545229 38128175146205104887954461)
      ·
        refine ⟨14298065679826914332982923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38128175146205104887954461 14298065679826914332982923)
        ·
          refine ⟨21447098519740371499474385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14298065679826914332982923 21447098519740371499474385)
          ·
            refine ⟨16085323889805278624605789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21447098519740371499474385 16085323889805278624605789)
            ·
              refine ⟨6031996458676979484227171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16085323889805278624605789 6031996458676979484227171)
              ·
                refine ⟨9047994688015469226340757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6031996458676979484227171 9047994688015469226340757)
                ·
                  refine ⟨424124751000725119984723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9047994688015469226340757 424124751000725119984723)
                  ·
                    rfl

theorem cell21_1858455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 6].length) (baseStart_1858455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858455 prefixEnd_1858455 := by exact prefixLift 1858455
  have htrace : WordTrace (prefixWord ++ tailWord_1858455) baseStart_1858455 baseEnd_1858455 := by
    simpa [prefixWord, tailWord_1858455, baseEnd_1858455] using wordTrace_append hprefix tailTrace_1858455
  have hstable : (prefixWord ++ tailWord_1858455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858455).length < 2 ^ (prefixWord ++ tailWord_1858455).sum := by decide
  have hdescent : baseEnd_1858455 < baseStart_1858455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858458 : List Nat := [3, 1, 1, 4, 3, 1, 2, 1, 5]
def baseStart_1858458 : Nat := 118140960795 + 1858458 * 2 ^ 59
def prefixEnd_1858458 : Nat := 4983230072969 + 3 ^ 40 * 1858458 * 2
def baseEnd_1858458 : Nat := 424125435641597781434717

theorem tailTrace_1858458 : CollatzResearch.WordTrace tailWord_1858458 prefixEnd_1858458 424125435641597781434717 := by
  unfold tailWord_1858458
  simp only [CollatzResearch.WordTrace]
  refine ⟨16945882975282885050514007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45189021267421026801370685 16945882975282885050514007)
  ·
    refine ⟨25418824462924327575771011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16945882975282885050514007 25418824462924327575771011)
    ·
      refine ⟨38128236694386491363656517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25418824462924327575771011 38128236694386491363656517)
      ·
        refine ⟨7149044380197467130685597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38128236694386491363656517 7149044380197467130685597)
        ·
          refine ⟨2680891642574050174007099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7149044380197467130685597 2680891642574050174007099)
          ·
            refine ⟨4021337463861075261010649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2680891642574050174007099 4021337463861075261010649)
            ·
              refine ⟨3016003097895806445757987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4021337463861075261010649 3016003097895806445757987)
              ·
                refine ⟨4524004646843709668636981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3016003097895806445757987 4524004646843709668636981)
                ·
                  refine ⟨424125435641597781434717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4524004646843709668636981 424125435641597781434717)
                  ·
                    rfl

theorem cell21_1858458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_1858458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858458 prefixEnd_1858458 := by exact prefixLift 1858458
  have htrace : WordTrace (prefixWord ++ tailWord_1858458) baseStart_1858458 baseEnd_1858458 := by
    simpa [prefixWord, tailWord_1858458, baseEnd_1858458] using wordTrace_append hprefix tailTrace_1858458
  have hstable : (prefixWord ++ tailWord_1858458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858458).length < 2 ^ (prefixWord ++ tailWord_1858458).sum := by decide
  have hdescent : baseEnd_1858458 < baseStart_1858458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858509 : List Nat := [1, 6, 3, 1, 1, 2, 1, 1, 5]
def baseStart_1858509 : Nat := 118140960795 + 1858509 * 2 ^ 59
def prefixEnd_1858509 : Nat := 4983230072969 + 3 ^ 40 * 1858509 * 2
def baseEnd_1858509 : Nat := 424137074536433026084613

theorem tailTrace_1858509 : CollatzResearch.WordTrace tailWord_1858509 prefixEnd_1858509 424137074536433026084613 := by
  unfold tailWord_1858509
  simp only [CollatzResearch.WordTrace]
  refine ⟨67785392023946775912162581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45190261349297850608108387 67785392023946775912162581)
  ·
    refine ⟨3177440251122505120882621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67785392023946775912162581 3177440251122505120882621)
    ·
      refine ⟨1191540094170939420330983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3177440251122505120882621 1191540094170939420330983)
      ·
        refine ⟨1787310141256409130496475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1191540094170939420330983 1787310141256409130496475)
        ·
          refine ⟨2680965211884613695744713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1787310141256409130496475 2680965211884613695744713)
          ·
            refine ⟨2010723908913460271808535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2680965211884613695744713 2010723908913460271808535)
            ·
              refine ⟨3016085863370190407712803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2010723908913460271808535 3016085863370190407712803)
              ·
                refine ⟨4524128795055285611569205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3016085863370190407712803 4524128795055285611569205)
                ·
                  refine ⟨424137074536433026084613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4524128795055285611569205 424137074536433026084613)
                  ·
                    rfl

theorem cell21_1858509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_1858509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858509 prefixEnd_1858509 := by exact prefixLift 1858509
  have htrace : WordTrace (prefixWord ++ tailWord_1858509) baseStart_1858509 baseEnd_1858509 := by
    simpa [prefixWord, tailWord_1858509, baseEnd_1858509] using wordTrace_append hprefix tailTrace_1858509
  have hstable : (prefixWord ++ tailWord_1858509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858509).length < 2 ^ (prefixWord ++ tailWord_1858509).sum := by decide
  have hdescent : baseEnd_1858509 < baseStart_1858509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858593 : List Nat := [1, 2, 3, 2, 3, 2, 1, 2, 5]
def baseStart_1858593 : Nat := 118140960795 + 1858593 * 2 ^ 59
def prefixEnd_1858593 : Nat := 4983230072969 + 3 ^ 40 * 1858593 * 2
def baseEnd_1858593 : Nat := 424156244480867546684441

theorem tailTrace_1858593 : CollatzResearch.WordTrace tailWord_1858593 prefixEnd_1858593 424156244480867546684441 := by
  unfold tailWord_1858593
  simp only [CollatzResearch.WordTrace]
  refine ⟨67788455755642458258220433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45192303837094972172146955 67788455755642458258220433)
  ·
    refine ⟨50841341816731843693665325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67788455755642458258220433 50841341816731843693665325)
    ·
      refine ⟨19065503181274441385124497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50841341816731843693665325 19065503181274441385124497)
      ·
        refine ⟨14299127385955831038843373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19065503181274441385124497 14299127385955831038843373)
        ·
          refine ⟨5362172769733436639566265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14299127385955831038843373 5362172769733436639566265)
          ·
            refine ⟨4021629577300077479674699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5362172769733436639566265 4021629577300077479674699)
            ·
              refine ⟨6032444365950116219512049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4021629577300077479674699 6032444365950116219512049)
              ·
                refine ⟨4524333274462587164634037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6032444365950116219512049 4524333274462587164634037)
                ·
                  refine ⟨424156244480867546684441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4524333274462587164634037 424156244480867546684441)
                  ·
                    rfl

theorem cell21_1858593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_1858593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858593 prefixEnd_1858593 := by exact prefixLift 1858593
  have htrace : WordTrace (prefixWord ++ tailWord_1858593) baseStart_1858593 baseEnd_1858593 := by
    simpa [prefixWord, tailWord_1858593, baseEnd_1858593] using wordTrace_append hprefix tailTrace_1858593
  have hstable : (prefixWord ++ tailWord_1858593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858593).length < 2 ^ (prefixWord ++ tailWord_1858593).sum := by decide
  have hdescent : baseEnd_1858593 < baseStart_1858593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858610 : List Nat := [3, 2, 1, 1, 2, 2, 4, 3, 3]
def baseStart_1858610 : Nat := 118140960795 + 1858610 * 2 ^ 59
def prefixEnd_1858610 : Nat := 4983230072969 + 3 ^ 40 * 1858610 * 2
def baseEnd_1858610 : Nat := 424160124112479294901073

theorem tailTrace_1858610 : CollatzResearch.WordTrace tailWord_1858610 prefixEnd_1858610 424160124112479294901073 := by
  unfold tailWord_1858610
  simp only [CollatzResearch.WordTrace]
  refine ⟨16947268949145217540397321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45192717197720580107726189 16947268949145217540397321)
  ·
    refine ⟨12710451711858913155297991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16947268949145217540397321 12710451711858913155297991)
    ·
      refine ⟨19065677567788369732946987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12710451711858913155297991 19065677567788369732946987)
      ·
        refine ⟨28598516351682554599420481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19065677567788369732946987 28598516351682554599420481)
        ·
          refine ⟨21448887263761915949565361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28598516351682554599420481 21448887263761915949565361)
          ·
            refine ⟨16086665447821436962174021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21448887263761915949565361 16086665447821436962174021)
            ·
              refine ⟨3016249771466519430407629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16086665447821436962174021 3016249771466519430407629)
              ·
                refine ⟨1131093664299944786402861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3016249771466519430407629 1131093664299944786402861)
                ·
                  refine ⟨424160124112479294901073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1131093664299944786402861 424160124112479294901073)
                  ·
                    rfl

theorem cell21_1858610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_1858610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858610 prefixEnd_1858610 := by exact prefixLift 1858610
  have htrace : WordTrace (prefixWord ++ tailWord_1858610) baseStart_1858610 baseEnd_1858610 := by
    simpa [prefixWord, tailWord_1858610, baseEnd_1858610] using wordTrace_append hprefix tailTrace_1858610
  have hstable : (prefixWord ++ tailWord_1858610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858610).length < 2 ^ (prefixWord ++ tailWord_1858610).sum := by decide
  have hdescent : baseEnd_1858610 < baseStart_1858610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858697 : List Nat := [1, 2, 1, 1, 4, 3, 1, 8]
def baseStart_1858697 : Nat := 118140960795 + 1858697 * 2 ^ 59
def prefixEnd_1858697 : Nat := 4983230072969 + 3 ^ 40 * 1858697 * 2
def baseEnd_1858697 : Nat := 141393326232595492316965

theorem tailTrace_1858697 : CollatzResearch.WordTrace tailWord_1858697 prefixEnd_1858697 141393326232595492316965 := by
  unfold tailWord_1858697
  simp only [CollatzResearch.WordTrace]
  refine ⟨67792248947265684020006345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45194832631510456013337563 67792248947265684020006345)
  ·
    refine ⟨50844186710449263015004759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67792248947265684020006345 50844186710449263015004759)
    ·
      refine ⟨76266280065673894522507139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50844186710449263015004759 76266280065673894522507139)
      ·
        refine ⟨114399420098510841783760709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76266280065673894522507139 114399420098510841783760709)
        ·
          refine ⟨21449891268470782834455133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114399420098510841783760709 21449891268470782834455133)
          ·
            refine ⟨8043709225676543562920675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21449891268470782834455133 8043709225676543562920675)
            ·
              refine ⟨12065563838514815344381013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8043709225676543562920675 12065563838514815344381013)
              ·
                refine ⟨141393326232595492316965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12065563838514815344381013 141393326232595492316965)
                ·
                  rfl

theorem cell21_1858697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 8].length) (baseStart_1858697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858697 prefixEnd_1858697 := by exact prefixLift 1858697
  have htrace : WordTrace (prefixWord ++ tailWord_1858697) baseStart_1858697 baseEnd_1858697 := by
    simpa [prefixWord, tailWord_1858697, baseEnd_1858697] using wordTrace_append hprefix tailTrace_1858697
  have hstable : (prefixWord ++ tailWord_1858697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858697).length < 2 ^ (prefixWord ++ tailWord_1858697).sum := by decide
  have hdescent : baseEnd_1858697 < baseStart_1858697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858714 : List Nat := [3, 1, 1, 5, 1, 1, 2, 7]
def baseStart_1858714 : Nat := 118140960795 + 1858714 * 2 ^ 59
def prefixEnd_1858714 : Nat := 4983230072969 + 3 ^ 40 * 1858714 * 2
def baseEnd_1858714 : Nat := 141394619443132741722509

theorem tailTrace_1858714 : CollatzResearch.WordTrace tailWord_1858714 prefixEnd_1858714 141394619443132741722509 := by
  unfold tailWord_1858714
  simp only [CollatzResearch.WordTrace]
  refine ⟨16948217247051023980843799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45195245992136063948916797 16948217247051023980843799)
  ·
    refine ⟨25422325870576535971265699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16948217247051023980843799 25422325870576535971265699)
    ·
      refine ⟨38133488805864803956898549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25422325870576535971265699 38133488805864803956898549)
      ·
        refine ⟨3575014575549825370959239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38133488805864803956898549 3575014575549825370959239)
        ·
          refine ⟨5362521863324738056438859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3575014575549825370959239 5362521863324738056438859)
          ·
            refine ⟨8043782794987107084658289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5362521863324738056438859 8043782794987107084658289)
            ·
              refine ⟨6032837096240330313493717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8043782794987107084658289 6032837096240330313493717)
              ·
                refine ⟨141394619443132741722509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6032837096240330313493717 141394619443132741722509)
                ·
                  rfl

theorem cell21_1858714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_1858714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858714 prefixEnd_1858714 := by exact prefixLift 1858714
  have htrace : WordTrace (prefixWord ++ tailWord_1858714) baseStart_1858714 baseEnd_1858714 := by
    simpa [prefixWord, tailWord_1858714, baseEnd_1858714] using wordTrace_append hprefix tailTrace_1858714
  have hstable : (prefixWord ++ tailWord_1858714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858714).length < 2 ^ (prefixWord ++ tailWord_1858714).sum := by decide
  have hdescent : baseEnd_1858714 < baseStart_1858714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858765 : List Nat := [1, 6, 2, 2, 1, 1, 3, 5]
def baseStart_1858765 : Nat := 118140960795 + 1858765 * 2 ^ 59
def prefixEnd_1858765 : Nat := 4983230072969 + 3 ^ 40 * 1858765 * 2
def baseEnd_1858765 : Nat := 141398499074744489939141

theorem tailTrace_1858765 : CollatzResearch.WordTrace tailWord_1858765 prefixEnd_1858765 141398499074744489939141 := by
  unfold tailWord_1858765
  simp only [CollatzResearch.WordTrace]
  refine ⟨67794729111019331633481749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45196486074012887755654499 67794729111019331633481749)
  ·
    refine ⟨3177877927079031170319457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67794729111019331633481749 3177877927079031170319457)
    ·
      refine ⟨2383408445309273377739593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3177877927079031170319457 2383408445309273377739593)
      ·
        refine ⟨1787556333981955033304695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2383408445309273377739593 1787556333981955033304695)
        ·
          refine ⟨2681334500972932549957043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1787556333981955033304695 2681334500972932549957043)
          ·
            refine ⟨4022001751459398824935565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2681334500972932549957043 4022001751459398824935565)
            ·
              refine ⟨1508250656797274559350837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4022001751459398824935565 1508250656797274559350837)
              ·
                refine ⟨141398499074744489939141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1508250656797274559350837 141398499074744489939141)
                ·
                  rfl

theorem cell21_1858765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 5].length) (baseStart_1858765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858765 prefixEnd_1858765 := by exact prefixLift 1858765
  have htrace : WordTrace (prefixWord ++ tailWord_1858765) baseStart_1858765 baseEnd_1858765 := by
    simpa [prefixWord, tailWord_1858765, baseEnd_1858765] using wordTrace_append hprefix tailTrace_1858765
  have hstable : (prefixWord ++ tailWord_1858765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858765).length < 2 ^ (prefixWord ++ tailWord_1858765).sum := by decide
  have hdescent : baseEnd_1858765 < baseStart_1858765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858824 : List Nat := [2, 1, 3, 2, 5, 1, 2, 5]
def baseStart_1858824 : Nat := 118140960795 + 1858824 * 2 ^ 59
def prefixEnd_1858824 : Nat := 4983230072969 + 3 ^ 40 * 1858824 * 2
def baseEnd_1858824 : Nat := 141402987276020826111323

theorem tailTrace_1858824 : CollatzResearch.WordTrace tailWord_1858824 prefixEnd_1858824 141402987276020826111323 := by
  unfold tailWord_1858824
  simp only [CollatzResearch.WordTrace]
  refine ⟨33898440508902792354939763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45197920678537056473253017 33898440508902792354939763)
  ·
    refine ⟨50847660763354188532409645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33898440508902792354939763 50847660763354188532409645)
    ·
      refine ⟨19067872786257820699653617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50847660763354188532409645 19067872786257820699653617)
      ·
        refine ⟨14300904589693365524740213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19067872786257820699653617 14300904589693365524740213)
        ·
          refine ⟨1340709805283753017944395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14300904589693365524740213 1340709805283753017944395)
          ·
            refine ⟨2011064707925629526916593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340709805283753017944395 2011064707925629526916593)
            ·
              refine ⟨1508298530944222145187445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2011064707925629526916593 1508298530944222145187445)
              ·
                refine ⟨141402987276020826111323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1508298530944222145187445 141402987276020826111323)
                ·
                  rfl

theorem cell21_1858824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 5].length) (baseStart_1858824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858824 prefixEnd_1858824 := by exact prefixLift 1858824
  have htrace : WordTrace (prefixWord ++ tailWord_1858824) baseStart_1858824 baseEnd_1858824 := by
    simpa [prefixWord, tailWord_1858824, baseEnd_1858824] using wordTrace_append hprefix tailTrace_1858824
  have hstable : (prefixWord ++ tailWord_1858824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858824).length < 2 ^ (prefixWord ++ tailWord_1858824).sum := by decide
  have hdescent : baseEnd_1858824 < baseStart_1858824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858866 : List Nat := [3, 2, 1, 1, 4, 2, 2, 6]
def baseStart_1858866 : Nat := 118140960795 + 1858866 * 2 ^ 59
def prefixEnd_1858866 : Nat := 4983230072969 + 3 ^ 40 * 1858866 * 2
def baseEnd_1858866 : Nat := 141406182266759912877961

theorem tailTrace_1858866 : CollatzResearch.WordTrace tailWord_1858866 prefixEnd_1858866 141406182266759912877961 := by
  unfold tailWord_1858866
  simp only [CollatzResearch.WordTrace]
  refine ⟨16949603220913356470727113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45198941922435617255272301 16949603220913356470727113)
  ·
    refine ⟨12712202415685017353045335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16949603220913356470727113 12712202415685017353045335)
    ·
      refine ⟨19068303623527526029568003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12712202415685017353045335 19068303623527526029568003)
      ·
        refine ⟨28602455435291289044352005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19068303623527526029568003 28602455435291289044352005)
        ·
          refine ⟨5362960394117116695816001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28602455435291289044352005 5362960394117116695816001)
          ·
            refine ⟨4022220295587837521862001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5362960394117116695816001 4022220295587837521862001)
            ·
              refine ⟨3016665221690878141396501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4022220295587837521862001 3016665221690878141396501)
              ·
                refine ⟨141406182266759912877961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3016665221690878141396501 141406182266759912877961)
                ·
                  rfl

theorem cell21_1858866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_1858866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858866 prefixEnd_1858866 := by exact prefixLift 1858866
  have htrace : WordTrace (prefixWord ++ tailWord_1858866) baseStart_1858866 baseEnd_1858866 := by
    simpa [prefixWord, tailWord_1858866, baseEnd_1858866] using wordTrace_append hprefix tailTrace_1858866
  have hstable : (prefixWord ++ tailWord_1858866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858866).length < 2 ^ (prefixWord ++ tailWord_1858866).sum := by decide
  have hdescent : baseEnd_1858866 < baseStart_1858866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858869 : List Nat := [1, 3, 3, 1, 2, 4, 2, 1, 4]
def baseStart_1858869 : Nat := 118140960795 + 1858869 * 2 ^ 59
def prefixEnd_1858869 : Nat := 4983230072969 + 3 ^ 40 * 1858869 * 2
def baseEnd_1858869 : Nat := 424219231441152400083877

theorem tailTrace_1858869 : CollatzResearch.WordTrace tailWord_1858869 prefixEnd_1858869 424219231441152400083877 := by
  unfold tailWord_1858869
  simp only [CollatzResearch.WordTrace]
  refine ⟨67798522302642557395267661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45199014868428371596845107 67798522302642557395267661)
  ·
    refine ⟨25424445863490959023225373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67798522302642557395267661 25424445863490959023225373)
    ·
      refine ⟨9534167198809109633709515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25424445863490959023225373 9534167198809109633709515)
      ·
        refine ⟨14301250798213664450564273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9534167198809109633709515 14301250798213664450564273)
        ·
          refine ⟨10725938098660248337923205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14301250798213664450564273 10725938098660248337923205)
          ·
            refine ⟨2011113393498796563360601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10725938098660248337923205 2011113393498796563360601)
            ·
              refine ⟨1508335045124097422520451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2011113393498796563360601 1508335045124097422520451)
              ·
                refine ⟨2262502567686146133780677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508335045124097422520451 2262502567686146133780677)
                ·
                  refine ⟨424219231441152400083877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2262502567686146133780677 424219231441152400083877)
                  ·
                    rfl

theorem cell21_1858869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_1858869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858869 prefixEnd_1858869 := by exact prefixLift 1858869
  have htrace : WordTrace (prefixWord ++ tailWord_1858869) baseStart_1858869 baseEnd_1858869 := by
    simpa [prefixWord, tailWord_1858869, baseEnd_1858869] using wordTrace_append hprefix tailTrace_1858869
  have hstable : (prefixWord ++ tailWord_1858869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858869).length < 2 ^ (prefixWord ++ tailWord_1858869).sum := by decide
  have hdescent : baseEnd_1858869 < baseStart_1858869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858897 : List Nat := [1, 2, 2, 1, 4, 1, 2, 5, 3]
def baseStart_1858897 : Nat := 118140960795 + 1858897 * 2 ^ 59
def prefixEnd_1858897 : Nat := 4983230072969 + 3 ^ 40 * 1858897 * 2
def baseEnd_1858897 : Nat := 424225621422630573617153

theorem tailTrace_1858897 : CollatzResearch.WordTrace tailWord_1858897 prefixEnd_1858897 424225621422630573617153 := by
  unfold tailWord_1858897
  simp only [CollatzResearch.WordTrace]
  refine ⟨67799543546541118177286945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45199695697694078784857963 67799543546541118177286945)
  ·
    refine ⟨50849657659905838632965209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67799543546541118177286945 50849657659905838632965209)
    ·
      refine ⟨38137243244929378974723907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50849657659905838632965209 38137243244929378974723907)
      ·
        refine ⟨57205864867394068462085861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38137243244929378974723907 57205864867394068462085861)
        ·
          refine ⟨10726099662636387836641099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57205864867394068462085861 10726099662636387836641099)
          ·
            refine ⟨16089149493954581754961649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10726099662636387836641099 16089149493954581754961649)
            ·
              refine ⟨12066862120465936316221237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16089149493954581754961649 12066862120465936316221237)
              ·
                refine ⟨1131268323793681529645741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12066862120465936316221237 1131268323793681529645741)
                ·
                  refine ⟨424225621422630573617153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1131268323793681529645741 424225621422630573617153)
                  ·
                    rfl

theorem cell21_1858897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 5, 3].length) (baseStart_1858897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858897 prefixEnd_1858897 := by exact prefixLift 1858897
  have htrace : WordTrace (prefixWord ++ tailWord_1858897) baseStart_1858897 baseEnd_1858897 := by
    simpa [prefixWord, tailWord_1858897, baseEnd_1858897] using wordTrace_append hprefix tailTrace_1858897
  have hstable : (prefixWord ++ tailWord_1858897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858897).length < 2 ^ (prefixWord ++ tailWord_1858897).sum := by decide
  have hdescent : baseEnd_1858897 < baseStart_1858897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858914 : List Nat := [3, 3, 2, 1, 1, 1, 3, 4, 3]
def baseStart_1858914 : Nat := 118140960795 + 1858914 * 2 ^ 59
def prefixEnd_1858914 : Nat := 4983230072969 + 3 ^ 40 * 1858914 * 2
def baseEnd_1858914 : Nat := 424229501054242321833785

theorem tailTrace_1858914 : CollatzResearch.WordTrace tailWord_1858914 prefixEnd_1858914 424229501054242321833785 := by
  unfold tailWord_1858914
  simp only [CollatzResearch.WordTrace]
  refine ⟨16950040896869882520163949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45200109058319686720437197 16950040896869882520163949)
  ·
    refine ⟨6356265336326205945061481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16950040896869882520163949 6356265336326205945061481)
    ·
      refine ⟨4767199002244654458796111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6356265336326205945061481 4767199002244654458796111)
      ·
        refine ⟨7150798503366981688194167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4767199002244654458796111 7150798503366981688194167)
        ·
          refine ⟨10726197755050472532291251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7150798503366981688194167 10726197755050472532291251)
          ·
            refine ⟨16089296632575708798436877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10726197755050472532291251 16089296632575708798436877)
            ·
              refine ⟨6033486237215890799413829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16089296632575708798436877 6033486237215890799413829)
              ·
                refine ⟨1131278669477979524890093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6033486237215890799413829 1131278669477979524890093)
                ·
                  refine ⟨424229501054242321833785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1131278669477979524890093 424229501054242321833785)
                  ·
                    rfl

theorem cell21_1858914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_1858914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858914 prefixEnd_1858914 := by exact prefixLift 1858914
  have htrace : WordTrace (prefixWord ++ tailWord_1858914) baseStart_1858914 baseEnd_1858914 := by
    simpa [prefixWord, tailWord_1858914, baseEnd_1858914] using wordTrace_append hprefix tailTrace_1858914
  have hstable : (prefixWord ++ tailWord_1858914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858914).length < 2 ^ (prefixWord ++ tailWord_1858914).sum := by decide
  have hdescent : baseEnd_1858914 < baseStart_1858914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858962 : List Nat := [3, 2, 3, 3, 1, 2, 1, 2, 4]
def baseStart_1858962 : Nat := 118140960795 + 1858962 * 2 ^ 59
def prefixEnd_1858962 : Nat := 4983230072969 + 3 ^ 40 * 1858962 * 2
def baseEnd_1858962 : Nat := 424240455308204905033687

theorem tailTrace_1858962 : CollatzResearch.WordTrace tailWord_1858962 prefixEnd_1858962 424240455308204905033687 := by
  unfold tailWord_1858962
  simp only [CollatzResearch.WordTrace]
  refine ⟨16950478572826408569600785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45201276194203756185602093 16950478572826408569600785)
  ·
    refine ⟨12712858929619806427200589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16950478572826408569600785 12712858929619806427200589)
    ·
      refine ⟨4767322098607427410200221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12712858929619806427200589 4767322098607427410200221)
      ·
        refine ⟨1787745786977785278825083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4767322098607427410200221 1787745786977785278825083)
        ·
          refine ⟨2681618680466677918237625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1787745786977785278825083 2681618680466677918237625)
          ·
            refine ⟨2011214010350008438678219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2681618680466677918237625 2011214010350008438678219)
            ·
              refine ⟨3016821015525012658017329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2011214010350008438678219 3016821015525012658017329)
              ·
                refine ⟨2262615761643759493512997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3016821015525012658017329 2262615761643759493512997)
                ·
                  refine ⟨424240455308204905033687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2262615761643759493512997 424240455308204905033687)
                  ·
                    rfl

theorem cell21_1858962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_1858962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858962 prefixEnd_1858962 := by exact prefixLift 1858962
  have htrace : WordTrace (prefixWord ++ tailWord_1858962) baseStart_1858962 baseEnd_1858962 := by
    simpa [prefixWord, tailWord_1858962, baseEnd_1858962] using wordTrace_append hprefix tailTrace_1858962
  have hstable : (prefixWord ++ tailWord_1858962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858962).length < 2 ^ (prefixWord ++ tailWord_1858962).sum := by decide
  have hdescent : baseEnd_1858962 < baseStart_1858962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1858973 : List Nat := [1, 4, 2, 1, 3, 2, 2, 1, 5]
def baseStart_1858973 : Nat := 118140960795 + 1858973 * 2 ^ 59
def prefixEnd_1858973 : Nat := 4983230072969 + 3 ^ 40 * 1858973 * 2
def baseEnd_1858973 : Nat := 424242965658071330350331

theorem tailTrace_1858973 : CollatzResearch.WordTrace tailWord_1858973 prefixEnd_1858973 424242965658071330350331 := by
  unfold tailWord_1858973
  simp only [CollatzResearch.WordTrace]
  refine ⟨67802315494265783157053573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45201543662843855438035715 67802315494265783157053573)
  ·
    refine ⟨12712934155174834341947545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67802315494265783157053573 12712934155174834341947545)
    ·
      refine ⟨9534700616381125756460659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12712934155174834341947545 9534700616381125756460659)
      ·
        refine ⟨14302050924571688634690989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9534700616381125756460659 14302050924571688634690989)
        ·
          refine ⟨5363269096714383238009121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14302050924571688634690989 5363269096714383238009121)
          ·
            refine ⟨4022451822535787428506841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5363269096714383238009121 4022451822535787428506841)
            ·
              refine ⟨3016838866901840571380131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4022451822535787428506841 3016838866901840571380131)
              ·
                refine ⟨4525258300352760857070197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3016838866901840571380131 4525258300352760857070197)
                ·
                  refine ⟨424242965658071330350331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4525258300352760857070197 424242965658071330350331)
                  ·
                    rfl

theorem cell21_1858973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_1858973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1858973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1858973 prefixEnd_1858973 := by exact prefixLift 1858973
  have htrace : WordTrace (prefixWord ++ tailWord_1858973) baseStart_1858973 baseEnd_1858973 := by
    simpa [prefixWord, tailWord_1858973, baseEnd_1858973] using wordTrace_append hprefix tailTrace_1858973
  have hstable : (prefixWord ++ tailWord_1858973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1858973).length < 2 ^ (prefixWord ++ tailWord_1858973).sum := by decide
  have hdescent : baseEnd_1858973 < baseStart_1858973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1858973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859010 : List Nat := [3, 5, 2, 1, 2, 1, 7]
def baseStart_1859010 : Nat := 118140960795 + 1859010 * 2 ^ 59
def prefixEnd_1859010 : Nat := 4983230072969 + 3 ^ 40 * 1859010 * 2
def baseEnd_1859010 : Nat := 47139045506907498692621

theorem tailTrace_1859010 : CollatzResearch.WordTrace tailWord_1859010 prefixEnd_1859010 47139045506907498692621 := by
  unfold tailWord_1859010
  simp only [CollatzResearch.WordTrace]
  refine ⟨16950916248782934619037621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45202443330087825650766989 16950916248782934619037621)
  ·
    refine ⟨1589148398323400120534777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16950916248782934619037621 1589148398323400120534777)
    ·
      refine ⟨1191861298742550090401083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1589148398323400120534777 1191861298742550090401083)
      ·
        refine ⟨1787791948113825135601625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1191861298742550090401083 1787791948113825135601625)
        ·
          refine ⟨1340843961085368851701219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1787791948113825135601625 1340843961085368851701219)
          ·
            refine ⟨2011265941628053277551829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340843961085368851701219 2011265941628053277551829)
            ·
              refine ⟨47139045506907498692621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2011265941628053277551829 47139045506907498692621)
              ·
                rfl

theorem cell21_1859010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 7].length) (baseStart_1859010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1859010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1859010 prefixEnd_1859010 := by exact prefixLift 1859010
  have htrace : WordTrace (prefixWord ++ tailWord_1859010) baseStart_1859010 baseEnd_1859010 := by
    simpa [prefixWord, tailWord_1859010, baseEnd_1859010] using wordTrace_append hprefix tailTrace_1859010
  have hstable : (prefixWord ++ tailWord_1859010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859010).length < 2 ^ (prefixWord ++ tailWord_1859010).sum := by decide
  have hdescent : baseEnd_1859010 < baseStart_1859010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859032 : List Nat := [2, 1, 2, 2, 2, 1, 5, 1, 5]
def baseStart_1859032 : Nat := 118140960795 + 1859032 * 2 ^ 59
def prefixEnd_1859032 : Nat := 4983230072969 + 3 ^ 40 * 1859032 * 2
def baseEnd_1859032 : Nat := 424256430261900338866877

theorem tailTrace_1859032 : CollatzResearch.WordTrace tailWord_1859032 prefixEnd_1859032 424256430261900338866877 := by
  unfold tailWord_1859032
  simp only [CollatzResearch.WordTrace]
  refine ⟨33902233700526018116725675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45202978267368024155634233 33902233700526018116725675)
  ·
    refine ⟨50853350550789027175088513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33902233700526018116725675 50853350550789027175088513)
    ·
      refine ⟨38140012913091770381316385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50853350550789027175088513 38140012913091770381316385)
      ·
        refine ⟨28605009684818827785987289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38140012913091770381316385 28605009684818827785987289)
        ·
          refine ⟨21453757263614120839490467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28605009684818827785987289 21453757263614120839490467)
          ·
            refine ⟨32180635895421181259235701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21453757263614120839490467 32180635895421181259235701)
            ·
              refine ⟨3016934615195735743053347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32180635895421181259235701 3016934615195735743053347)
              ·
                refine ⟨4525401922793603614580021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3016934615195735743053347 4525401922793603614580021)
                ·
                  refine ⟨424256430261900338866877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4525401922793603614580021 424256430261900338866877)
                  ·
                    rfl

theorem cell21_1859032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 5].length) (baseStart_1859032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1859032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1859032 prefixEnd_1859032 := by exact prefixLift 1859032
  have htrace : WordTrace (prefixWord ++ tailWord_1859032) baseStart_1859032 baseEnd_1859032 := by
    simpa [prefixWord, tailWord_1859032, baseEnd_1859032] using wordTrace_append hprefix tailTrace_1859032
  have hstable : (prefixWord ++ tailWord_1859032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859032).length < 2 ^ (prefixWord ++ tailWord_1859032).sum := by decide
  have hdescent : baseEnd_1859032 < baseStart_1859032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859083 : List Nat := [1, 1, 1, 1, 8, 2, 2, 2, 3]
def baseStart_1859083 : Nat := 118140960795 + 1859083 * 2 ^ 59
def prefixEnd_1859083 : Nat := 4983230072969 + 3 ^ 40 * 1859083 * 2
def baseEnd_1859083 : Nat := 424268069156735583516773

theorem tailTrace_1859083 : CollatzResearch.WordTrace tailWord_1859083 prefixEnd_1859083 424268069156735583516773 := by
  unfold tailWord_1859083
  simp only [CollatzResearch.WordTrace]
  refine ⟨67806327523867271943557903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45204218349244847962371935 67806327523867271943557903)
  ·
    refine ⟨101709491285800907915336855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67806327523867271943557903 101709491285800907915336855)
    ·
      refine ⟨152564236928701361873005283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101709491285800907915336855 152564236928701361873005283)
      ·
        refine ⟨228846355393052042809507925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152564236928701361873005283 228846355393052042809507925)
        ·
          refine ⟨2681793227262328626673921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 228846355393052042809507925 2681793227262328626673921)
          ·
            refine ⟨2011344920446746470005441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2681793227262328626673921 2011344920446746470005441)
            ·
              refine ⟨1508508690335059852504081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2011344920446746470005441 1508508690335059852504081)
              ·
                refine ⟨1131381517751294889378061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1508508690335059852504081 1131381517751294889378061)
                ·
                  refine ⟨424268069156735583516773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1131381517751294889378061 424268069156735583516773)
                  ·
                    rfl

theorem cell21_1859083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 2, 3].length) (baseStart_1859083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1859083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1859083 prefixEnd_1859083 := by exact prefixLift 1859083
  have htrace : WordTrace (prefixWord ++ tailWord_1859083) baseStart_1859083 baseEnd_1859083 := by
    simpa [prefixWord, tailWord_1859083, baseEnd_1859083] using wordTrace_append hprefix tailTrace_1859083
  have hstable : (prefixWord ++ tailWord_1859083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859083).length < 2 ^ (prefixWord ++ tailWord_1859083).sum := by decide
  have hdescent : baseEnd_1859083 < baseStart_1859083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859122 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 6]
def baseStart_1859122 : Nat := 118140960795 + 1859122 * 2 ^ 59
def prefixEnd_1859122 : Nat := 4983230072969 + 3 ^ 40 * 1859122 * 2
def baseEnd_1859122 : Nat := 424276969488080182366693

theorem tailTrace_1859122 : CollatzResearch.WordTrace tailWord_1859122 prefixEnd_1859122 424276969488080182366693 := by
  unfold tailWord_1859122
  simp only [CollatzResearch.WordTrace]
  refine ⟨16951937492681495401056905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45205166647150654402818413 16951937492681495401056905)
  ·
    refine ⟨12713953119511121550792679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16951937492681495401056905 12713953119511121550792679)
    ·
      refine ⟨19070929679266682326189019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12713953119511121550792679 19070929679266682326189019)
      ·
        refine ⟨28606394518900023489283529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19070929679266682326189019 28606394518900023489283529)
        ·
          refine ⟨21454795889175017616962647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28606394518900023489283529 21454795889175017616962647)
          ·
            refine ⟨32182193833762526425443971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21454795889175017616962647 32182193833762526425443971)
            ·
              refine ⟨48273290750643789638165957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32182193833762526425443971 48273290750643789638165957)
              ·
                refine ⟨9051242015745710557156117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48273290750643789638165957 9051242015745710557156117)
                ·
                  refine ⟨424276969488080182366693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9051242015745710557156117 424276969488080182366693)
                  ·
                    rfl

theorem cell21_1859122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_1859122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1859122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1859122 prefixEnd_1859122 := by exact prefixLift 1859122
  have htrace : WordTrace (prefixWord ++ tailWord_1859122) baseStart_1859122 baseEnd_1859122 := by
    simpa [prefixWord, tailWord_1859122, baseEnd_1859122] using wordTrace_append hprefix tailTrace_1859122
  have hstable : (prefixWord ++ tailWord_1859122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859122).length < 2 ^ (prefixWord ++ tailWord_1859122).sum := by decide
  have hdescent : baseEnd_1859122 < baseStart_1859122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859125 : List Nat := [1, 3, 3, 1, 1, 3, 1, 5, 3]
def baseStart_1859125 : Nat := 118140960795 + 1859125 * 2 ^ 59
def prefixEnd_1859125 : Nat := 4983230072969 + 3 ^ 40 * 1859125 * 2
def baseEnd_1859125 : Nat := 424277654128952843816687

theorem tailTrace_1859125 : CollatzResearch.WordTrace tailWord_1859125 prefixEnd_1859125 424277654128952843816687 := by
  unfold tailWord_1859125
  simp only [CollatzResearch.WordTrace]
  refine ⟨67807859389715113116586829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45205239593143408744391219 67807859389715113116586829)
  ·
    refine ⟨25427947271143167418720061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67807859389715113116586829 25427947271143167418720061)
    ·
      refine ⟨9535480226678687782020023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25427947271143167418720061 9535480226678687782020023)
      ·
        refine ⟨14303220340018031673030035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9535480226678687782020023 14303220340018031673030035)
        ·
          refine ⟨21454830510027047509545053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14303220340018031673030035 21454830510027047509545053)
          ·
            refine ⟨8045561441260142816079395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21454830510027047509545053 8045561441260142816079395)
            ·
              refine ⟨12068342161890214224119093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8045561441260142816079395 12068342161890214224119093)
              ·
                refine ⟨1131407077677207583511165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12068342161890214224119093 1131407077677207583511165)
                ·
                  refine ⟨424277654128952843816687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1131407077677207583511165 424277654128952843816687)
                  ·
                    rfl

theorem cell21_1859125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_1859125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1859125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1859125 prefixEnd_1859125 := by exact prefixLift 1859125
  have htrace : WordTrace (prefixWord ++ tailWord_1859125) baseStart_1859125 baseEnd_1859125 := by
    simpa [prefixWord, tailWord_1859125, baseEnd_1859125] using wordTrace_append hprefix tailTrace_1859125
  have hstable : (prefixWord ++ tailWord_1859125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859125).length < 2 ^ (prefixWord ++ tailWord_1859125).sum := by decide
  have hdescent : baseEnd_1859125 < baseStart_1859125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859156 : List Nat := [2, 4, 1, 1, 1, 2, 5, 1, 4]
def baseStart_1859156 : Nat := 118140960795 + 1859156 * 2 ^ 59
def prefixEnd_1859156 : Nat := 4983230072969 + 3 ^ 40 * 1859156 * 2
def baseEnd_1859156 : Nat := 424284728751303678799957

theorem tailTrace_1859156 : CollatzResearch.WordTrace tailWord_1859156 prefixEnd_1859156 424284728751303678799957 := by
  unfold tailWord_1859156
  simp only [CollatzResearch.WordTrace]
  refine ⟨33904495026301402705482661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45205993368401870273976881 33904495026301402705482661)
  ·
    refine ⟨6357092817431513007277999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33904495026301402705482661 6357092817431513007277999)
    ·
      refine ⟨9535639226147269510916999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6357092817431513007277999 9535639226147269510916999)
      ·
        refine ⟨14303458839220904266375499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9535639226147269510916999 14303458839220904266375499)
        ·
          refine ⟨21455188258831356399563249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14303458839220904266375499 21455188258831356399563249)
          ·
            refine ⟨16091391194123517299672437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21455188258831356399563249 16091391194123517299672437)
            ·
              refine ⟨1508567924449079746844291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16091391194123517299672437 1508567924449079746844291)
              ·
                refine ⟨2262851886673619620266437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508567924449079746844291 2262851886673619620266437)
                ·
                  refine ⟨424284728751303678799957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2262851886673619620266437 424284728751303678799957)
                  ·
                    rfl

theorem cell21_1859156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_1859156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1859156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1859156 prefixEnd_1859156 := by exact prefixLift 1859156
  have htrace : WordTrace (prefixWord ++ tailWord_1859156) baseStart_1859156 baseEnd_1859156 := by
    simpa [prefixWord, tailWord_1859156, baseEnd_1859156] using wordTrace_append hprefix tailTrace_1859156
  have hstable : (prefixWord ++ tailWord_1859156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859156).length < 2 ^ (prefixWord ++ tailWord_1859156).sum := by decide
  have hdescent : baseEnd_1859156 < baseStart_1859156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859201 : List Nat := [1, 2, 4, 2, 1, 4, 1, 1, 5]
def baseStart_1859201 : Nat := 118140960795 + 1859201 * 2 ^ 59
def prefixEnd_1859201 : Nat := 4983230072969 + 3 ^ 40 * 1859201 * 2
def baseEnd_1859201 : Nat := 424294998364393600549865

theorem tailTrace_1859201 : CollatzResearch.WordTrace tailWord_1859201 prefixEnd_1859201 424294998364393600549865 := by
  unfold tailWord_1859201
  simp only [CollatzResearch.WordTrace]
  refine ⟨67810631337439778096353457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45207087558293185397568971 67810631337439778096353457)
  ·
    refine ⟨50857973503079833572265093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67810631337439778096353457 50857973503079833572265093)
    ·
      refine ⟨9535870031827468794799705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50857973503079833572265093 9535870031827468794799705)
      ·
        refine ⟨7151902523870601596099779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9535870031827468794799705 7151902523870601596099779)
        ·
          refine ⟨10727853785805902394149669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7151902523870601596099779 10727853785805902394149669)
          ·
            refine ⟨2011472584838606698903063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10727853785805902394149669 2011472584838606698903063)
            ·
              refine ⟨3017208877257910048354595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2011472584838606698903063 3017208877257910048354595)
              ·
                refine ⟨4525813315886865072531893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3017208877257910048354595 4525813315886865072531893)
                ·
                  refine ⟨424294998364393600549865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4525813315886865072531893 424294998364393600549865)
                  ·
                    rfl

theorem cell21_1859201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 5].length) (baseStart_1859201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1859201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1859201 prefixEnd_1859201 := by exact prefixLift 1859201
  have htrace : WordTrace (prefixWord ++ tailWord_1859201) baseStart_1859201 baseEnd_1859201 := by
    simpa [prefixWord, tailWord_1859201, baseEnd_1859201] using wordTrace_append hprefix tailTrace_1859201
  have hstable : (prefixWord ++ tailWord_1859201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859201).length < 2 ^ (prefixWord ++ tailWord_1859201).sum := by decide
  have hdescent : baseEnd_1859201 < baseStart_1859201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859246 : List Nat := [4, 1, 4, 1, 2, 9]
def baseStart_1859246 : Nat := 118140960795 + 1859246 * 2 ^ 59
def prefixEnd_1859246 : Nat := 4983230072969 + 3 ^ 40 * 1859246 * 2
def baseEnd_1859246 : Nat := 15715009925091982307399

theorem tailTrace_1859246 : CollatzResearch.WordTrace tailWord_1859246 prefixEnd_1859246 15715009925091982307399 := by
  unfold tailWord_1859246
  simp only [CollatzResearch.WordTrace]
  refine ⟨8476534077784593847717699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45208181748184500521161061 8476534077784593847717699)
  ·
    refine ⟨12714801116676890771576549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8476534077784593847717699 12714801116676890771576549)
    ·
      refine ⟨2384025209376917019670603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12714801116676890771576549 2384025209376917019670603)
      ·
        refine ⟨3576037814065375529505905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2384025209376917019670603 3576037814065375529505905)
        ·
          refine ⟨2682028360549031647129429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3576037814065375529505905 2682028360549031647129429)
          ·
            refine ⟨15715009925091982307399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2682028360549031647129429 15715009925091982307399)
            ·
              rfl

theorem cell21_1859246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 9].length) (baseStart_1859246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1859246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1859246 prefixEnd_1859246 := by exact prefixLift 1859246
  have htrace : WordTrace (prefixWord ++ tailWord_1859246) baseStart_1859246 baseEnd_1859246 := by
    simpa [prefixWord, tailWord_1859246, baseEnd_1859246] using wordTrace_append hprefix tailTrace_1859246
  have hstable : (prefixWord ++ tailWord_1859246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859246).length < 2 ^ (prefixWord ++ tailWord_1859246).sum := by decide
  have hdescent : baseEnd_1859246 < baseStart_1859246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859277 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 7]
def baseStart_1859277 : Nat := 118140960795 + 1859277 * 2 ^ 59
def prefixEnd_1859277 : Nat := 4983230072969 + 3 ^ 40 * 1859277 * 2
def baseEnd_1859277 : Nat := 424312342599834357283043

theorem tailTrace_1859277 : CollatzResearch.WordTrace tailWord_1859277 prefixEnd_1859277 424312342599834357283043 := by
  unfold tailWord_1859277
  simp only [CollatzResearch.WordTrace]
  refine ⟨67813403285164443076120085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45208935523442962050746723 67813403285164443076120085)
  ·
    refine ⟨3178753278992083269193129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67813403285164443076120085 3178753278992083269193129)
    ·
      refine ⟨2384064959244062451894847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3178753278992083269193129 2384064959244062451894847)
      ·
        refine ⟨3576097438866093677842271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2384064959244062451894847 3576097438866093677842271)
        ·
          refine ⟨5364146158299140516763407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3576097438866093677842271 5364146158299140516763407)
          ·
            refine ⟨8046219237448710775145111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5364146158299140516763407 8046219237448710775145111)
            ·
              refine ⟨12069328856173066162717667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8046219237448710775145111 12069328856173066162717667)
              ·
                refine ⟨18103993284259599244076501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12069328856173066162717667 18103993284259599244076501)
                ·
                  refine ⟨424312342599834357283043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18103993284259599244076501 424312342599834357283043)
                  ·
                    rfl

theorem cell21_1859277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_1859277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1859277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1859277 prefixEnd_1859277 := by exact prefixLift 1859277
  have htrace : WordTrace (prefixWord ++ tailWord_1859277) baseStart_1859277 baseEnd_1859277 := by
    simpa [prefixWord, tailWord_1859277, baseEnd_1859277] using wordTrace_append hprefix tailTrace_1859277
  have hstable : (prefixWord ++ tailWord_1859277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859277).length < 2 ^ (prefixWord ++ tailWord_1859277).sum := by decide
  have hdescent : baseEnd_1859277 < baseStart_1859277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859319 : List Nat := [1, 1, 3, 1, 1, 1, 5, 3, 5]
def baseStart_1859319 : Nat := 118140960795 + 1859319 * 2 ^ 59
def prefixEnd_1859319 : Nat := 4983230072969 + 3 ^ 40 * 1859319 * 2
def baseEnd_1859319 : Nat := 424321927572051617582957

theorem tailTrace_1859319 : CollatzResearch.WordTrace tailWord_1859319 prefixEnd_1859319 424321927572051617582957 := by
  unfold tailWord_1859319
  simp only [CollatzResearch.WordTrace]
  refine ⟨67814935151012284249149011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45209956767341522832766007 67814935151012284249149011)
  ·
    refine ⟨101722402726518426373723517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67814935151012284249149011 101722402726518426373723517)
    ·
      refine ⟨38145901022444409890146319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101722402726518426373723517 38145901022444409890146319)
      ·
        refine ⟨57218851533666614835219479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38145901022444409890146319 57218851533666614835219479)
        ·
          refine ⟨85828277300499922252829219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57218851533666614835219479 85828277300499922252829219)
          ·
            refine ⟨128742415950749883379243829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85828277300499922252829219 128742415950749883379243829)
            ·
              refine ⟨12069601495382801566804109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128742415950749883379243829 12069601495382801566804109)
              ·
                refine ⟨4526100560768550587551541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12069601495382801566804109 4526100560768550587551541)
                ·
                  refine ⟨424321927572051617582957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4526100560768550587551541 424321927572051617582957)
                  ·
                    rfl

theorem cell21_1859319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 5].length) (baseStart_1859319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1859319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1859319 prefixEnd_1859319 := by exact prefixLift 1859319
  have htrace : WordTrace (prefixWord ++ tailWord_1859319) baseStart_1859319 baseEnd_1859319 := by
    simpa [prefixWord, tailWord_1859319, baseEnd_1859319] using wordTrace_append hprefix tailTrace_1859319
  have hstable : (prefixWord ++ tailWord_1859319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859319).length < 2 ^ (prefixWord ++ tailWord_1859319).sum := by decide
  have hdescent : baseEnd_1859319 < baseStart_1859319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859384 : List Nat := [2, 1, 2, 1, 3, 5, 2, 1, 4]
def baseStart_1859384 : Nat := 118140960795 + 1859384 * 2 ^ 59
def prefixEnd_1859384 : Nat := 4983230072969 + 3 ^ 40 * 1859384 * 2
def baseEnd_1859384 : Nat := 424336761457625948999491

theorem tailTrace_1859384 : CollatzResearch.WordTrace tailWord_1859384 prefixEnd_1859384 424336761457625948999491 := by
  unfold tailWord_1859384
  simp only [CollatzResearch.WordTrace]
  refine ⟨33908652947888400175132603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45211537263851200233510137 33908652947888400175132603)
  ·
    refine ⟨50862979421832600262698905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33908652947888400175132603 50862979421832600262698905)
    ·
      refine ⟨38147234566374450197024179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50862979421832600262698905 38147234566374450197024179)
      ·
        refine ⟨57220851849561675295536269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38147234566374450197024179 57220851849561675295536269)
        ·
          refine ⟨21457819443585628235826101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57220851849561675295536269 21457819443585628235826101)
          ·
            refine ⟨2011670572836152647108697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21457819443585628235826101 2011670572836152647108697)
            ·
              refine ⟨1508752929627114485331523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2011670572836152647108697 1508752929627114485331523)
              ·
                refine ⟨2263129394440671727997285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508752929627114485331523 2263129394440671727997285)
                ·
                  refine ⟨424336761457625948999491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2263129394440671727997285 424336761457625948999491)
                  ·
                    rfl

theorem cell21_1859384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 4].length) (baseStart_1859384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1859384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1859384 prefixEnd_1859384 := by exact prefixLift 1859384
  have htrace : WordTrace (prefixWord ++ tailWord_1859384) baseStart_1859384 baseEnd_1859384 := by
    simpa [prefixWord, tailWord_1859384, baseEnd_1859384] using wordTrace_append hprefix tailTrace_1859384
  have hstable : (prefixWord ++ tailWord_1859384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859384).length < 2 ^ (prefixWord ++ tailWord_1859384).sum := by decide
  have hdescent : baseEnd_1859384 < baseStart_1859384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859508 : List Nat := [2, 5, 2, 1, 2, 2, 2, 5]
def baseStart_1859508 : Nat := 118140960795 + 1859508 * 2 ^ 59
def prefixEnd_1859508 : Nat := 4983230072969 + 3 ^ 40 * 1859508 * 2
def baseEnd_1859508 : Nat := 141455019982343096310857

theorem tailTrace_1859508 : CollatzResearch.WordTrace tailWord_1859508 prefixEnd_1859508 141455019982343096310857 := by
  unfold tailWord_1859508
  simp only [CollatzResearch.WordTrace]
  refine ⟨33910914273663784763889589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45214552364885046351852785 33910914273663784763889589)
  ·
    refine ⟨3179148213155979821614649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33910914273663784763889589 3179148213155979821614649)
    ·
      refine ⟨2384361159866984866210987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3179148213155979821614649 2384361159866984866210987)
      ·
        refine ⟨3576541739800477299316481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2384361159866984866210987 3576541739800477299316481)
        ·
          refine ⟨2682406304850357974487361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3576541739800477299316481 2682406304850357974487361)
          ·
            refine ⟨2011804728637768480865521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2682406304850357974487361 2011804728637768480865521)
            ·
              refine ⟨1508853546478326360649141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2011804728637768480865521 1508853546478326360649141)
              ·
                refine ⟨141455019982343096310857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1508853546478326360649141 141455019982343096310857)
                ·
                  rfl

theorem cell21_1859508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 5].length) (baseStart_1859508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1859508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1859508 prefixEnd_1859508 := by exact prefixLift 1859508
  have htrace : WordTrace (prefixWord ++ tailWord_1859508) baseStart_1859508 baseEnd_1859508 := by
    simpa [prefixWord, tailWord_1859508, baseEnd_1859508] using wordTrace_append hprefix tailTrace_1859508
  have hstable : (prefixWord ++ tailWord_1859508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859508).length < 2 ^ (prefixWord ++ tailWord_1859508).sum := by decide
  have hdescent : baseEnd_1859508 < baseStart_1859508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859590 : List Nat := [6, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1859590 : Nat := 118140960795 + 1859590 * 2 ^ 59
def prefixEnd_1859590 : Nat := 4983230072969 + 3 ^ 40 * 1859590 * 2
def baseEnd_1859590 : Nat := 424383773464215368565737

theorem tailTrace_1859590 : CollatzResearch.WordTrace tailWord_1859590 prefixEnd_1859590 424383773464215368565737 := by
  unfold tailWord_1859590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2119525604157203047883257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45216546222020331688176149 2119525604157203047883257)
  ·
    refine ⟨1589644203117902285912443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2119525604157203047883257 1589644203117902285912443)
    ·
      refine ⟨2384466304676853428868665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1589644203117902285912443 2384466304676853428868665)
      ·
        refine ⟨1788349728507640071651499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2384466304676853428868665 1788349728507640071651499)
        ·
          refine ⟨2682524592761460107477249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1788349728507640071651499 2682524592761460107477249)
          ·
            refine ⟨2011893444571095080607937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2682524592761460107477249 2011893444571095080607937)
            ·
              refine ⟨1508920083428321310455953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2011893444571095080607937 1508920083428321310455953)
              ·
                refine ⟨1131690062571240982841965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1508920083428321310455953 1131690062571240982841965)
                ·
                  refine ⟨424383773464215368565737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1131690062571240982841965 424383773464215368565737)
                  ·
                    rfl

theorem cell21_1859590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1859590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1859590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1859590 prefixEnd_1859590 := by exact prefixLift 1859590
  have htrace : WordTrace (prefixWord ++ tailWord_1859590) baseStart_1859590 baseEnd_1859590 := by
    simpa [prefixWord, tailWord_1859590, baseEnd_1859590] using wordTrace_append hprefix tailTrace_1859590
  have hstable : (prefixWord ++ tailWord_1859590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859590).length < 2 ^ (prefixWord ++ tailWord_1859590).sum := by decide
  have hdescent : baseEnd_1859590 < baseStart_1859590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859626 : List Nat := [3, 1, 4, 1, 2, 2, 3, 5]
def baseStart_1859626 : Nat := 118140960795 + 1859626 * 2 ^ 59
def prefixEnd_1859626 : Nat := 4983230072969 + 3 ^ 40 * 1859626 * 2
def baseEnd_1859626 : Nat := 141463996384895768655221

theorem tailTrace_1859626 : CollatzResearch.WordTrace tailWord_1859626 prefixEnd_1859626 141463996384895768655221 := by
  unfold tailWord_1859626
  simp only [CollatzResearch.WordTrace]
  refine ⟨16956533090225018920143683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45217421573933383787049821 16956533090225018920143683)
  ·
    refine ⟨25434799635337528380215525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16956533090225018920143683 25434799635337528380215525)
    ·
      refine ⟨4769024931625786571290411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25434799635337528380215525 4769024931625786571290411)
      ·
        refine ⟨7153537397438679856935617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4769024931625786571290411 7153537397438679856935617)
        ·
          refine ⟨5365153048079009892701713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7153537397438679856935617 5365153048079009892701713)
          ·
            refine ⟨4023864786059257419526285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5365153048079009892701713 4023864786059257419526285)
            ·
              refine ⟨1508949294772221532322357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4023864786059257419526285 1508949294772221532322357)
              ·
                refine ⟨141463996384895768655221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1508949294772221532322357 141463996384895768655221)
                ·
                  rfl

theorem cell21_1859626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_1859626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1859626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1859626 prefixEnd_1859626 := by exact prefixLift 1859626
  have htrace : WordTrace (prefixWord ++ tailWord_1859626) baseStart_1859626 baseEnd_1859626 := by
    simpa [prefixWord, tailWord_1859626, baseEnd_1859626] using wordTrace_append hprefix tailTrace_1859626
  have hstable : (prefixWord ++ tailWord_1859626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859626).length < 2 ^ (prefixWord ++ tailWord_1859626).sum := by decide
  have hdescent : baseEnd_1859626 < baseStart_1859626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859668 : List Nat := [2, 4, 1, 1, 1, 1, 1, 10]
def baseStart_1859668 : Nat := 118140960795 + 1859668 * 2 ^ 59
def prefixEnd_1859668 : Nat := 4983230072969 + 3 ^ 40 * 1859668 * 2
def baseEnd_1859668 : Nat := 141467191375634855421859

theorem tailTrace_1859668 : CollatzResearch.WordTrace tailWord_1859668 prefixEnd_1859668 141467191375634855421859 := by
  unfold tailWord_1859668
  simp only [CollatzResearch.WordTrace]
  refine ⟨33913832113373958426801829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45218442817831944569069105 33913832113373958426801829)
  ·
    refine ⟨6358843521257617205025343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33913832113373958426801829 6358843521257617205025343)
    ·
      refine ⟨9538265281886425807538015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6358843521257617205025343 9538265281886425807538015)
      ·
        refine ⟨14307397922829638711307023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9538265281886425807538015 14307397922829638711307023)
        ·
          refine ⟨21461096884244458066960535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14307397922829638711307023 21461096884244458066960535)
          ·
            refine ⟨32191645326366687100440803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21461096884244458066960535 32191645326366687100440803)
            ·
              refine ⟨48287467989550030650661205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32191645326366687100440803 48287467989550030650661205)
              ·
                refine ⟨141467191375634855421859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48287467989550030650661205 141467191375634855421859)
                ·
                  rfl

theorem cell21_1859668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 10].length) (baseStart_1859668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1859668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1859668 prefixEnd_1859668 := by exact prefixLift 1859668
  have htrace : WordTrace (prefixWord ++ tailWord_1859668) baseStart_1859668 baseEnd_1859668 := by
    simpa [prefixWord, tailWord_1859668, baseEnd_1859668] using wordTrace_append hprefix tailTrace_1859668
  have hstable : (prefixWord ++ tailWord_1859668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859668).length < 2 ^ (prefixWord ++ tailWord_1859668).sum := by decide
  have hdescent : baseEnd_1859668 < baseStart_1859668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859685 : List Nat := [1, 3, 1, 3, 2, 2, 4, 5]
def baseStart_1859685 : Nat := 118140960795 + 1859685 * 2 ^ 59
def prefixEnd_1859685 : Nat := 4983230072969 + 3 ^ 40 * 1859685 * 2
def baseEnd_1859685 : Nat := 141468484586172104827403

theorem tailTrace_1859685 : CollatzResearch.WordTrace tailWord_1859685 prefixEnd_1859685 141468484586172104827403 := by
  unfold tailWord_1859685
  simp only [CollatzResearch.WordTrace]
  refine ⟨67828284267686328756972509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45218856178457552504648339 67828284267686328756972509)
  ·
    refine ⟨25435606600382373283864691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67828284267686328756972509 25435606600382373283864691)
    ·
      refine ⟨38153409900573559925797037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25435606600382373283864691 38153409900573559925797037)
      ·
        refine ⟨14307528712715084972173889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38153409900573559925797037 14307528712715084972173889)
        ·
          refine ⟨10730646534536313729130417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14307528712715084972173889 10730646534536313729130417)
          ·
            refine ⟨8047984900902235296847813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10730646534536313729130417 8047984900902235296847813)
            ·
              refine ⟨1508997168919169118158965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8047984900902235296847813 1508997168919169118158965)
              ·
                refine ⟨141468484586172104827403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1508997168919169118158965 141468484586172104827403)
                ·
                  rfl

theorem cell21_1859685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 5].length) (baseStart_1859685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1859685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1859685 prefixEnd_1859685 := by exact prefixLift 1859685
  have htrace : WordTrace (prefixWord ++ tailWord_1859685) baseStart_1859685 baseEnd_1859685 := by
    simpa [prefixWord, tailWord_1859685, baseEnd_1859685] using wordTrace_append hprefix tailTrace_1859685
  have hstable : (prefixWord ++ tailWord_1859685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859685).length < 2 ^ (prefixWord ++ tailWord_1859685).sum := by decide
  have hdescent : baseEnd_1859685 < baseStart_1859685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859744 : List Nat := [2, 1, 1, 4, 2, 2, 2, 7]
def baseStart_1859744 : Nat := 118140960795 + 1859744 * 2 ^ 59
def prefixEnd_1859744 : Nat := 4983230072969 + 3 ^ 40 * 1859744 * 2
def baseEnd_1859744 : Nat := 141472972787448440999585

theorem tailTrace_1859744 : CollatzResearch.WordTrace tailWord_1859744 prefixEnd_1859744 141472972787448440999585 := by
  unfold tailWord_1859744
  simp only [CollatzResearch.WordTrace]
  refine ⟨33915218087236290916685143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45220290782981721222246857 33915218087236290916685143)
  ·
    refine ⟨50872827130854436375027715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33915218087236290916685143 50872827130854436375027715)
    ·
      refine ⟨76309240696281654562541573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50872827130854436375027715 76309240696281654562541573)
      ·
        refine ⟨14307982630552810230476545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76309240696281654562541573 14307982630552810230476545)
        ·
          refine ⟨10730986972914607672857409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14307982630552810230476545 10730986972914607672857409)
          ·
            refine ⟨8048240229685955754643057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10730986972914607672857409 8048240229685955754643057)
            ·
              refine ⟨6036180172264466815982293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8048240229685955754643057 6036180172264466815982293)
              ·
                refine ⟨141472972787448440999585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6036180172264466815982293 141472972787448440999585)
                ·
                  rfl

theorem cell21_1859744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 7].length) (baseStart_1859744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1859744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1859744 prefixEnd_1859744 := by exact prefixLift 1859744
  have htrace : WordTrace (prefixWord ++ tailWord_1859744) baseStart_1859744 baseEnd_1859744 := by
    simpa [prefixWord, tailWord_1859744, baseEnd_1859744] using wordTrace_append hprefix tailTrace_1859744
  have hstable : (prefixWord ++ tailWord_1859744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859744).length < 2 ^ (prefixWord ++ tailWord_1859744).sum := by decide
  have hdescent : baseEnd_1859744 < baseStart_1859744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859761 : List Nat := [1, 2, 2, 5, 3, 8]
def baseStart_1859761 : Nat := 118140960795 + 1859761 * 2 ^ 59
def prefixEnd_1859761 : Nat := 4983230072969 + 3 ^ 40 * 1859761 * 2
def baseEnd_1859761 : Nat := 15719362888665076711681

theorem tailTrace_1859761 : CollatzResearch.WordTrace tailWord_1859761 prefixEnd_1859761 15719362888665076711681 := by
  unfold tailWord_1859761
  simp only [CollatzResearch.WordTrace]
  refine ⟨67831056215410993736739137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45220704143607329157826091 67831056215410993736739137)
  ·
    refine ⟨50873292161558245302554353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67831056215410993736739137 50873292161558245302554353)
    ·
      refine ⟨38154969121168683976915765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50873292161558245302554353 38154969121168683976915765)
      ·
        refine ⟨3577028355109564122835853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38154969121168683976915765 3577028355109564122835853)
        ·
          refine ⟨1341385633166086546063445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3577028355109564122835853 1341385633166086546063445)
          ·
            refine ⟨15719362888665076711681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1341385633166086546063445 15719362888665076711681)
            ·
              rfl

theorem cell21_1859761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 8].length) (baseStart_1859761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1859761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1859761 prefixEnd_1859761 := by exact prefixLift 1859761
  have htrace : WordTrace (prefixWord ++ tailWord_1859761) baseStart_1859761 baseEnd_1859761 := by
    simpa [prefixWord, tailWord_1859761, baseEnd_1859761] using wordTrace_append hprefix tailTrace_1859761
  have hstable : (prefixWord ++ tailWord_1859761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859761).length < 2 ^ (prefixWord ++ tailWord_1859761).sum := by decide
  have hdescent : baseEnd_1859761 < baseStart_1859761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859823 : List Nat := [1, 1, 2, 1, 6, 3, 1, 2, 4]
def baseStart_1859823 : Nat := 118140960795 + 1859823 * 2 ^ 59
def prefixEnd_1859823 : Nat := 4983230072969 + 3 ^ 40 * 1859823 * 2
def baseEnd_1859823 : Nat := 424436947238658741181927

theorem tailTrace_1859823 : CollatzResearch.WordTrace tailWord_1859823 prefixEnd_1859823 424436947238658741181927 := by
  unfold tailWord_1859823
  simp only [CollatzResearch.WordTrace]
  refine ⟨67833317541186378325496123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45222211694124252216997415 67833317541186378325496123)
  ·
    refine ⟨101749976311779567488244185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67833317541186378325496123 101749976311779567488244185)
    ·
      refine ⟨76312482233834675616183139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101749976311779567488244185 76312482233834675616183139)
      ·
        refine ⟨114468723350752013424274709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76312482233834675616183139 114468723350752013424274709)
        ·
          refine ⟨5365721407066500629262877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114468723350752013424274709 5365721407066500629262877)
          ·
            refine ⟨2012145527649937735973579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5365721407066500629262877 2012145527649937735973579)
            ·
              refine ⟨3018218291474906603960369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012145527649937735973579 3018218291474906603960369)
              ·
                refine ⟨2263663718606179952970277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3018218291474906603960369 2263663718606179952970277)
                ·
                  refine ⟨424436947238658741181927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2263663718606179952970277 424436947238658741181927)
                  ·
                    rfl

theorem cell21_1859823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 2, 4].length) (baseStart_1859823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1859823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1859823 prefixEnd_1859823 := by exact prefixLift 1859823
  have htrace : WordTrace (prefixWord ++ tailWord_1859823) baseStart_1859823 baseEnd_1859823 := by
    simpa [prefixWord, tailWord_1859823, baseEnd_1859823] using wordTrace_append hprefix tailTrace_1859823
  have hstable : (prefixWord ++ tailWord_1859823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859823).length < 2 ^ (prefixWord ++ tailWord_1859823).sum := by decide
  have hdescent : baseEnd_1859823 < baseStart_1859823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1859978 : List Nat := [3, 1, 2, 5, 1, 1, 2, 3, 3]
def baseStart_1859978 : Nat := 118140960795 + 1859978 * 2 ^ 59
def prefixEnd_1859978 : Nat := 4983230072969 + 3 ^ 40 * 1859978 * 2
def baseEnd_1859978 : Nat := 424472320350412916098277

theorem tailTrace_1859978 : CollatzResearch.WordTrace tailWord_1859978 prefixEnd_1859978 424472320350412916098277 := by
  unfold tailWord_1859978
  simp only [CollatzResearch.WordTrace]
  refine ⟨16959742713906209949347147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45225980570416559864925725 16959742713906209949347147)
  ·
    refine ⟨25439614070859314924020721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16959742713906209949347147 25439614070859314924020721)
    ·
      refine ⟨19079710553144486193015541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25439614070859314924020721 19079710553144486193015541)
      ·
        refine ⟨1788722864357295580595207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19079710553144486193015541 1788722864357295580595207)
        ·
          refine ⟨2683084296535943370892811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1788722864357295580595207 2683084296535943370892811)
          ·
            refine ⟨4024626444803915056339217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2683084296535943370892811 4024626444803915056339217)
            ·
              refine ⟨3018469833602936292254413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4024626444803915056339217 3018469833602936292254413)
              ·
                refine ⟨1131926187601101109595405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3018469833602936292254413 1131926187601101109595405)
                ·
                  refine ⟨424472320350412916098277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1131926187601101109595405 424472320350412916098277)
                  ·
                    rfl

theorem cell21_1859978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_1859978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1859978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1859978 prefixEnd_1859978 := by exact prefixLift 1859978
  have htrace : WordTrace (prefixWord ++ tailWord_1859978) baseStart_1859978 baseEnd_1859978 := by
    simpa [prefixWord, tailWord_1859978, baseEnd_1859978] using wordTrace_append hprefix tailTrace_1859978
  have hstable : (prefixWord ++ tailWord_1859978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1859978).length < 2 ^ (prefixWord ++ tailWord_1859978).sum := by decide
  have hdescent : baseEnd_1859978 < baseStart_1859978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1859978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860003 : List Nat := [1, 1, 1, 4, 1, 5, 2, 1, 5]
def baseStart_1860003 : Nat := 118140960795 + 1860003 * 2 ^ 59
def prefixEnd_1860003 : Nat := 4983230072969 + 3 ^ 40 * 1860003 * 2
def baseEnd_1860003 : Nat := 424478025691018428181559

theorem tailTrace_1860003 : CollatzResearch.WordTrace tailWord_1860003 prefixEnd_1860003 424478025691018428181559 := by
  unfold tailWord_1860003
  simp only [CollatzResearch.WordTrace]
  refine ⟨67839882680534269067048663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45226588453689512711365775 67839882680534269067048663)
  ·
    refine ⟨101759824020801403600572995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67839882680534269067048663 101759824020801403600572995)
    ·
      refine ⟨152639736031202105400859493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101759824020801403600572995 152639736031202105400859493)
      ·
        refine ⟨28619950505850394762661155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152639736031202105400859493 28619950505850394762661155)
        ·
          refine ⟨42929925758775592143991733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28619950505850394762661155 42929925758775592143991733)
          ·
            refine ⟨4024680539885211763499225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42929925758775592143991733 4024680539885211763499225)
            ·
              refine ⟨3018510404913908822624419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4024680539885211763499225 3018510404913908822624419)
              ·
                refine ⟨4527765607370863233936629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3018510404913908822624419 4527765607370863233936629)
                ·
                  refine ⟨424478025691018428181559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4527765607370863233936629 424478025691018428181559)
                  ·
                    rfl

theorem cell21_1860003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 5].length) (baseStart_1860003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1860003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1860003 prefixEnd_1860003 := by exact prefixLift 1860003
  have htrace : WordTrace (prefixWord ++ tailWord_1860003) baseStart_1860003 baseEnd_1860003 := by
    simpa [prefixWord, tailWord_1860003, baseEnd_1860003] using wordTrace_append hprefix tailTrace_1860003
  have hstable : (prefixWord ++ tailWord_1860003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860003).length < 2 ^ (prefixWord ++ tailWord_1860003).sum := by decide
  have hdescent : baseEnd_1860003 < baseStart_1860003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860054 : List Nat := [5, 2, 1, 1, 1, 1, 5, 2, 3]
def baseStart_1860054 : Nat := 118140960795 + 1860054 * 2 ^ 59
def prefixEnd_1860054 : Nat := 4983230072969 + 3 ^ 40 * 1860054 * 2
def baseEnd_1860054 : Nat := 424489664585853672831455

theorem tailTrace_1860054 : CollatzResearch.WordTrace tailWord_1860054 prefixEnd_1860054 424489664585853672831455 := by
  unfold tailWord_1860054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4240108925209344048572201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45227828535566336518103477 4240108925209344048572201)
  ·
    refine ⟨3180081693907008036429151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4240108925209344048572201 3180081693907008036429151)
    ·
      refine ⟨4770122540860512054643727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3180081693907008036429151 4770122540860512054643727)
      ·
        refine ⟨7155183811290768081965591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4770122540860512054643727 7155183811290768081965591)
        ·
          refine ⟨10732775716936152122948387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7155183811290768081965591 10732775716936152122948387)
          ·
            refine ⟨16099163575404228184422581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10732775716936152122948387 16099163575404228184422581)
            ·
              refine ⟨1509296585194146392289617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16099163575404228184422581 1509296585194146392289617)
              ·
                refine ⟨1131972438895609794217213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1509296585194146392289617 1131972438895609794217213)
                ·
                  refine ⟨424489664585853672831455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1131972438895609794217213 424489664585853672831455)
                  ·
                    rfl

theorem cell21_1860054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_1860054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1860054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1860054 prefixEnd_1860054 := by exact prefixLift 1860054
  have htrace : WordTrace (prefixWord ++ tailWord_1860054) baseStart_1860054 baseEnd_1860054 := by
    simpa [prefixWord, tailWord_1860054, baseEnd_1860054] using wordTrace_append hprefix tailTrace_1860054
  have hstable : (prefixWord ++ tailWord_1860054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860054).length < 2 ^ (prefixWord ++ tailWord_1860054).sum := by decide
  have hdescent : baseEnd_1860054 < baseStart_1860054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860107 : List Nat := [1, 1, 1, 1, 7, 10]
def baseStart_1860107 : Nat := 118140960795 + 1860107 * 2 ^ 59
def prefixEnd_1860107 : Nat := 4983230072969 + 3 ^ 40 * 1860107 * 2
def baseEnd_1860107 : Nat := 15722287403997679942519

theorem tailTrace_1860107 : CollatzResearch.WordTrace tailWord_1860107 prefixEnd_1860107 15722287403997679942519 := by
  unfold tailWord_1860107
  simp only [CollatzResearch.WordTrace]
  refine ⟨67843675872157494828834575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45229117248104996552556383 67843675872157494828834575)
  ·
    refine ⟨101765513808236242243251863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67843675872157494828834575 101765513808236242243251863)
    ·
      refine ⟨152648270712354363364877795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101765513808236242243251863 152648270712354363364877795)
      ·
        refine ⟨228972406068531545047316693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152648270712354363364877795 228972406068531545047316693)
        ·
          refine ⟨5366540767231208087046485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 228972406068531545047316693 5366540767231208087046485)
          ·
            refine ⟨15722287403997679942519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5366540767231208087046485 15722287403997679942519)
            ·
              rfl

theorem cell21_1860107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 10].length) (baseStart_1860107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1860107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1860107 prefixEnd_1860107 := by exact prefixLift 1860107
  have htrace : WordTrace (prefixWord ++ tailWord_1860107) baseStart_1860107 baseEnd_1860107 := by
    simpa [prefixWord, tailWord_1860107, baseEnd_1860107] using wordTrace_append hprefix tailTrace_1860107
  have hstable : (prefixWord ++ tailWord_1860107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860107).length < 2 ^ (prefixWord ++ tailWord_1860107).sum := by decide
  have hdescent : baseEnd_1860107 < baseStart_1860107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860110 : List Nat := [4, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_1860110 : Nat := 118140960795 + 1860110 * 2 ^ 59
def prefixEnd_1860110 : Nat := 4983230072969 + 3 ^ 40 * 1860110 * 2
def baseEnd_1860110 : Nat := 424502444548810019898007

theorem tailTrace_1860110 : CollatzResearch.WordTrace tailWord_1860110 prefixEnd_1860110 424502444548810019898007 := by
  unfold tailWord_1860110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8480473161393328292649223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45229190194097750894129189 8480473161393328292649223)
  ·
    refine ⟨12720709742089992438973835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8480473161393328292649223 12720709742089992438973835)
    ·
      refine ⟨19081064613134988658460753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12720709742089992438973835 19081064613134988658460753)
      ·
        refine ⟨14310798459851241493845565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19081064613134988658460753 14310798459851241493845565)
        ·
          refine ⟨5366549422444215560192087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14310798459851241493845565 5366549422444215560192087)
          ·
            refine ⟨8049824133666323340288131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5366549422444215560192087 8049824133666323340288131)
            ·
              refine ⟨12074736200499485010432197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8049824133666323340288131 12074736200499485010432197)
              ·
                refine ⟨2264013037593653439456037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12074736200499485010432197 2264013037593653439456037)
                ·
                  refine ⟨424502444548810019898007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2264013037593653439456037 424502444548810019898007)
                  ·
                    rfl

theorem cell21_1860110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_1860110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1860110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1860110 prefixEnd_1860110 := by exact prefixLift 1860110
  have htrace : WordTrace (prefixWord ++ tailWord_1860110) baseStart_1860110 baseEnd_1860110 := by
    simpa [prefixWord, tailWord_1860110, baseEnd_1860110] using wordTrace_append hprefix tailTrace_1860110
  have hstable : (prefixWord ++ tailWord_1860110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860110).length < 2 ^ (prefixWord ++ tailWord_1860110).sum := by decide
  have hdescent : baseEnd_1860110 < baseStart_1860110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860124 : List Nat := [2, 2, 3, 1, 2, 2, 3, 6]
def baseStart_1860124 : Nat := 118140960795 + 1860124 * 2 ^ 59
def prefixEnd_1860124 : Nat := 4983230072969 + 3 ^ 40 * 1860124 * 2
def baseEnd_1860124 : Nat := 141501879846516368888215

theorem tailTrace_1860124 : CollatzResearch.WordTrace tailWord_1860124 prefixEnd_1860124 141501879846516368888215 := by
  unfold tailWord_1860124
  simp only [CollatzResearch.WordTrace]
  refine ⟨33922147956547953366101713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45229530608730604488135617 33922147956547953366101713)
  ·
    refine ⟨25441610967410965024576285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33922147956547953366101713 25441610967410965024576285)
    ·
      refine ⟨9540604112779111884216107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25441610967410965024576285 9540604112779111884216107)
      ·
        refine ⟨14310906169168667826324161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9540604112779111884216107 14310906169168667826324161)
        ·
          refine ⟨10733179626876500869743121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14310906169168667826324161 10733179626876500869743121)
          ·
            refine ⟨8049884720157375652307341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10733179626876500869743121 8049884720157375652307341)
            ·
              refine ⟨3018706770059015869615253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8049884720157375652307341 3018706770059015869615253)
              ·
                refine ⟨141501879846516368888215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3018706770059015869615253 141501879846516368888215)
                ·
                  rfl

theorem cell21_1860124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 6].length) (baseStart_1860124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1860124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1860124 prefixEnd_1860124 := by exact prefixLift 1860124
  have htrace : WordTrace (prefixWord ++ tailWord_1860124) baseStart_1860124 baseEnd_1860124 := by
    simpa [prefixWord, tailWord_1860124, baseEnd_1860124] using wordTrace_append hprefix tailTrace_1860124
  have hstable : (prefixWord ++ tailWord_1860124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860124).length < 2 ^ (prefixWord ++ tailWord_1860124).sum := by decide
  have hdescent : baseEnd_1860124 < baseStart_1860124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860183 : List Nat := [1, 1, 3, 2, 2, 2, 2, 8]
def baseStart_1860183 : Nat := 118140960795 + 1860183 * 2 ^ 59
def prefixEnd_1860183 : Nat := 4983230072969 + 3 ^ 40 * 1860183 * 2
def baseEnd_1860183 : Nat := 141506368047792705060397

theorem tailTrace_1860183 : CollatzResearch.WordTrace tailWord_1860183 prefixEnd_1860183 141506368047792705060397 := by
  unfold tailWord_1860183
  simp only [CollatzResearch.WordTrace]
  refine ⟨67846447819882159808601203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45230965213254773205734135 67846447819882159808601203)
  ·
    refine ⟨101769671729823239712901805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67846447819882159808601203 101769671729823239712901805)
    ·
      refine ⟨38163626898683714892338177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101769671729823239712901805 38163626898683714892338177)
      ·
        refine ⟨28622720174012786169253633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38163626898683714892338177 28622720174012786169253633)
        ·
          refine ⟨21467040130509589626940225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28622720174012786169253633 21467040130509589626940225)
          ·
            refine ⟨16100280097882192220205169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21467040130509589626940225 16100280097882192220205169)
            ·
              refine ⟨12075210073411644165153877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16100280097882192220205169 12075210073411644165153877)
              ·
                refine ⟨141506368047792705060397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12075210073411644165153877 141506368047792705060397)
                ·
                  rfl

theorem cell21_1860183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 8].length) (baseStart_1860183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1860183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1860183 prefixEnd_1860183 := by exact prefixLift 1860183
  have htrace : WordTrace (prefixWord ++ tailWord_1860183) baseStart_1860183 baseEnd_1860183 := by
    simpa [prefixWord, tailWord_1860183, baseEnd_1860183] using wordTrace_append hprefix tailTrace_1860183
  have hstable : (prefixWord ++ tailWord_1860183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860183).length < 2 ^ (prefixWord ++ tailWord_1860183).sum := by decide
  have hdescent : baseEnd_1860183 < baseStart_1860183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860324 : List Nat := [2, 3, 1, 1, 1, 5, 2, 3, 3]
def baseStart_1860324 : Nat := 118140960795 + 1860324 * 2 ^ 59
def prefixEnd_1860324 : Nat := 4983230072969 + 3 ^ 40 * 1860324 * 2
def baseEnd_1860324 : Nat := 424551282264393203330903

theorem tailTrace_1860324 : CollatzResearch.WordTrace tailWord_1860324 prefixEnd_1860324 424551282264393203330903 := by
  unfold tailWord_1860324
  simp only [CollatzResearch.WordTrace]
  refine ⟨33925795256185670444742013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45234393674914227259656017 33925795256185670444742013)
  ·
    refine ⟨12722173221069626416778255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33925795256185670444742013 12722173221069626416778255)
    ·
      refine ⟨19083259831604439625167383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12722173221069626416778255 19083259831604439625167383)
      ·
        refine ⟨28624889747406659437751075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19083259831604439625167383 28624889747406659437751075)
        ·
          refine ⟨42937334621109989156626613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28624889747406659437751075 42937334621109989156626613)
          ·
            refine ⟨4025375120729061483433745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42937334621109989156626613 4025375120729061483433745)
            ·
              refine ⟨3019031340546796112575309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4025375120729061483433745 3019031340546796112575309)
              ·
                refine ⟨1132136752705048542215741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3019031340546796112575309 1132136752705048542215741)
                ·
                  refine ⟨424551282264393203330903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1132136752705048542215741 424551282264393203330903)
                  ·
                    rfl

theorem cell21_1860324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_1860324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1860324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1860324 prefixEnd_1860324 := by exact prefixLift 1860324
  have htrace : WordTrace (prefixWord ++ tailWord_1860324) baseStart_1860324 baseEnd_1860324 := by
    simpa [prefixWord, tailWord_1860324, baseEnd_1860324] using wordTrace_append hprefix tailTrace_1860324
  have hstable : (prefixWord ++ tailWord_1860324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860324).length < 2 ^ (prefixWord ++ tailWord_1860324).sum := by decide
  have hdescent : baseEnd_1860324 < baseStart_1860324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860335 : List Nat := [1, 1, 2, 1, 5, 3, 8]
def baseStart_1860335 : Nat := 118140960795 + 1860335 * 2 ^ 59
def prefixEnd_1860335 : Nat := 4983230072969 + 3 ^ 40 * 1860335 * 2
def baseEnd_1860335 : Nat := 47172643623806625405283

theorem tailTrace_1860335 : CollatzResearch.WordTrace tailWord_1860335 prefixEnd_1860335 47172643623806625405283 := by
  unfold tailWord_1860335
  simp only [CollatzResearch.WordTrace]
  refine ⟨67851991715331489768134459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45234661143554326512089639 67851991715331489768134459)
  ·
    refine ⟨101777987572997234652201689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67851991715331489768134459 101777987572997234652201689)
    ·
      refine ⟨76333490679747925989151267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101777987572997234652201689 76333490679747925989151267)
      ·
        refine ⟨114500236019621888983726901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76333490679747925989151267 114500236019621888983726901)
        ·
          refine ⟨10734397126839552092224397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114500236019621888983726901 10734397126839552092224397)
          ·
            refine ⟨4025398922564832034584149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10734397126839552092224397 4025398922564832034584149)
            ·
              refine ⟨47172643623806625405283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4025398922564832034584149 47172643623806625405283)
              ·
                rfl

theorem cell21_1860335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 8].length) (baseStart_1860335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1860335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1860335 prefixEnd_1860335 := by exact prefixLift 1860335
  have htrace : WordTrace (prefixWord ++ tailWord_1860335) baseStart_1860335 baseEnd_1860335 := by
    simpa [prefixWord, tailWord_1860335, baseEnd_1860335] using wordTrace_append hprefix tailTrace_1860335
  have hstable : (prefixWord ++ tailWord_1860335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860335).length < 2 ^ (prefixWord ++ tailWord_1860335).sum := by decide
  have hdescent : baseEnd_1860335 < baseStart_1860335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860338 : List Nat := [3, 2, 1, 3, 1, 2, 3, 2, 4]
def baseStart_1860338 : Nat := 118140960795 + 1860338 * 2 ^ 59
def prefixEnd_1860338 : Nat := 4983230072969 + 3 ^ 40 * 1860338 * 2
def baseEnd_1860338 : Nat := 424554477255132290097541

theorem tailTrace_1860338 : CollatzResearch.WordTrace tailWord_1860338 prefixEnd_1860338 424554477255132290097541 := by
  unfold tailWord_1860338
  simp only [CollatzResearch.WordTrace]
  refine ⟨16963025283580155320123417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45234734089547080853662445 16963025283580155320123417)
  ·
    refine ⟨12722268962685116490092563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16963025283580155320123417 12722268962685116490092563)
    ·
      refine ⟨19083403444027674735138845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12722268962685116490092563 19083403444027674735138845)
      ·
        refine ⟨7156276291510378025677067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19083403444027674735138845 7156276291510378025677067)
        ·
          refine ⟨10734414437265567038515601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7156276291510378025677067 10734414437265567038515601)
          ·
            refine ⟨8050810827949175278886701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10734414437265567038515601 8050810827949175278886701)
            ·
              refine ⟨3019054060480940729582513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8050810827949175278886701 3019054060480940729582513)
              ·
                refine ⟨2264290545360705547186885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3019054060480940729582513 2264290545360705547186885)
                ·
                  refine ⟨424554477255132290097541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2264290545360705547186885 424554477255132290097541)
                  ·
                    rfl

theorem cell21_1860338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_1860338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1860338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1860338 prefixEnd_1860338 := by exact prefixLift 1860338
  have htrace : WordTrace (prefixWord ++ tailWord_1860338) baseStart_1860338 baseEnd_1860338 := by
    simpa [prefixWord, tailWord_1860338, baseEnd_1860338] using wordTrace_append hprefix tailTrace_1860338
  have hstable : (prefixWord ++ tailWord_1860338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860338).length < 2 ^ (prefixWord ++ tailWord_1860338).sum := by decide
  have hdescent : baseEnd_1860338 < baseStart_1860338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860462 : List Nat := [4, 1, 2, 3, 3, 1, 1, 6]
def baseStart_1860462 : Nat := 118140960795 + 1860462 * 2 ^ 59
def prefixEnd_1860462 : Nat := 4983230072969 + 3 ^ 40 * 1860462 * 2
def baseEnd_1860462 : Nat := 141527591914845210010207

theorem tailTrace_1860462 : CollatzResearch.WordTrace tailWord_1860462 prefixEnd_1860462 141527591914845210010207 := by
  unfold tailWord_1860462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8482077973233923807250955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45237749190580926972005093 8482077973233923807250955)
  ·
    refine ⟨12723116959850885710876433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8482077973233923807250955 12723116959850885710876433)
    ·
      refine ⟨9542337719888164283157325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12723116959850885710876433 9542337719888164283157325)
      ·
        refine ⟨3578376644958061606183997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9542337719888164283157325 3578376644958061606183997)
        ·
          refine ⟨1341891241859273102318999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3578376644958061606183997 1341891241859273102318999)
          ·
            refine ⟨2012836862788909653478499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341891241859273102318999 2012836862788909653478499)
            ·
              refine ⟨3019255294183364480217749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012836862788909653478499 3019255294183364480217749)
              ·
                refine ⟨141527591914845210010207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3019255294183364480217749 141527591914845210010207)
                ·
                  rfl

theorem cell21_1860462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_1860462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1860462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1860462 prefixEnd_1860462 := by exact prefixLift 1860462
  have htrace : WordTrace (prefixWord ++ tailWord_1860462) baseStart_1860462 baseEnd_1860462 := by
    simpa [prefixWord, tailWord_1860462, baseEnd_1860462] using wordTrace_append hprefix tailTrace_1860462
  have hstable : (prefixWord ++ tailWord_1860462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860462).length < 2 ^ (prefixWord ++ tailWord_1860462).sum := by decide
  have hdescent : baseEnd_1860462 < baseStart_1860462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860473 : List Nat := [1, 2, 1, 3, 2, 3, 2, 3, 4]
def baseStart_1860473 : Nat := 118140960795 + 1860473 * 2 ^ 59
def prefixEnd_1860473 : Nat := 4983230072969 + 3 ^ 40 * 1860473 * 2
def baseEnd_1860473 : Nat := 424585286094402055347265

theorem tailTrace_1860473 : CollatzResearch.WordTrace tailWord_1860473 prefixEnd_1860473 424585286094402055347265 := by
  unfold tailWord_1860473
  simp only [CollatzResearch.WordTrace]
  refine ⟨67857024988831539336658073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45238016659221026224438715 67857024988831539336658073)
  ·
    refine ⟨50892768741623654502493555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67857024988831539336658073 50892768741623654502493555)
    ·
      refine ⟨76339153112435481753740333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50892768741623654502493555 76339153112435481753740333)
      ·
        refine ⟨28627182417163305657652625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76339153112435481753740333 28627182417163305657652625)
        ·
          refine ⟨21470386812872479243239469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28627182417163305657652625 21470386812872479243239469)
          ·
            refine ⟨8051395054827179716214801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21470386812872479243239469 8051395054827179716214801)
            ·
              refine ⟨6038546291120384787161101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8051395054827179716214801 6038546291120384787161101)
              ·
                refine ⟨2264454859170144295185413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6038546291120384787161101 2264454859170144295185413)
                ·
                  refine ⟨424585286094402055347265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2264454859170144295185413 424585286094402055347265)
                  ·
                    rfl

theorem cell21_1860473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_1860473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1860473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1860473 prefixEnd_1860473 := by exact prefixLift 1860473
  have htrace : WordTrace (prefixWord ++ tailWord_1860473) baseStart_1860473 baseEnd_1860473 := by
    simpa [prefixWord, tailWord_1860473, baseEnd_1860473] using wordTrace_append hprefix tailTrace_1860473
  have hstable : (prefixWord ++ tailWord_1860473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860473).length < 2 ^ (prefixWord ++ tailWord_1860473).sum := by decide
  have hdescent : baseEnd_1860473 < baseStart_1860473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860566 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1860566 : Nat := 118140960795 + 1860566 * 2 ^ 59
def prefixEnd_1860566 : Nat := 4983230072969 + 3 ^ 40 * 1860566 * 2
def baseEnd_1860566 : Nat := 424606509961454560297075

theorem tailTrace_1860566 : CollatzResearch.WordTrace tailWord_1860566 prefixEnd_1860566 424606509961454560297075 := by
  unfold tailWord_1860566
  simp only [CollatzResearch.WordTrace]
  refine ⟨4241276061093413513737097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45240277984996410813195701 4241276061093413513737097)
  ·
    refine ⟨3180957045820060135302823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4241276061093413513737097 3180957045820060135302823)
    ·
      refine ⟨4771435568730090202954235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3180957045820060135302823 4771435568730090202954235)
      ·
        refine ⟨7157153353095135304431353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4771435568730090202954235 7157153353095135304431353)
        ·
          refine ⟨5367865014821351478323515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7157153353095135304431353 5367865014821351478323515)
          ·
            refine ⟨8051797522232027217485273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5367865014821351478323515 8051797522232027217485273)
            ·
              refine ⟨6038848141674020413113955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8051797522232027217485273 6038848141674020413113955)
              ·
                refine ⟨9058272212511030619670933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6038848141674020413113955 9058272212511030619670933)
                ·
                  refine ⟨424606509961454560297075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9058272212511030619670933 424606509961454560297075)
                  ·
                    rfl

theorem cell21_1860566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1860566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1860566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1860566 prefixEnd_1860566 := by exact prefixLift 1860566
  have htrace : WordTrace (prefixWord ++ tailWord_1860566) baseStart_1860566 baseEnd_1860566 := by
    simpa [prefixWord, tailWord_1860566, baseEnd_1860566] using wordTrace_append hprefix tailTrace_1860566
  have hstable : (prefixWord ++ tailWord_1860566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860566).length < 2 ^ (prefixWord ++ tailWord_1860566).sum := by decide
  have hdescent : baseEnd_1860566 < baseStart_1860566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860583 : List Nat := [1, 1, 5, 2, 2, 3, 2, 1, 4]
def baseStart_1860583 : Nat := 118140960795 + 1860583 * 2 ^ 59
def prefixEnd_1860583 : Nat := 4983230072969 + 3 ^ 40 * 1860583 * 2
def baseEnd_1860583 : Nat := 424610389593066308513707

theorem tailTrace_1860583 : CollatzResearch.WordTrace tailWord_1860583 prefixEnd_1860583 424610389593066308513707 := by
  unfold tailWord_1860583
  simp only [CollatzResearch.WordTrace]
  refine ⟨67861037018433028123162403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45240691345622018748774935 67861037018433028123162403)
  ·
    refine ⟨101791555527649542184743605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67861037018433028123162403 101791555527649542184743605)
    ·
      refine ⟨9542958330717144579819713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101791555527649542184743605 9542958330717144579819713)
      ·
        refine ⟨7157218748037858434864785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9542958330717144579819713 7157218748037858434864785)
        ·
          refine ⟨5367914061028393826148589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7157218748037858434864785 5367914061028393826148589)
          ·
            refine ⟨2012967772885647684805721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5367914061028393826148589 2012967772885647684805721)
            ·
              refine ⟨1509725829664235763604291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2012967772885647684805721 1509725829664235763604291)
              ·
                refine ⟨2264588744496353645406437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1509725829664235763604291 2264588744496353645406437)
                ·
                  refine ⟨424610389593066308513707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2264588744496353645406437 424610389593066308513707)
                  ·
                    rfl

theorem cell21_1860583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 4].length) (baseStart_1860583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1860583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1860583 prefixEnd_1860583 := by exact prefixLift 1860583
  have htrace : WordTrace (prefixWord ++ tailWord_1860583) baseStart_1860583 baseEnd_1860583 := by
    simpa [prefixWord, tailWord_1860583, baseEnd_1860583] using wordTrace_append hprefix tailTrace_1860583
  have hstable : (prefixWord ++ tailWord_1860583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860583).length < 2 ^ (prefixWord ++ tailWord_1860583).sum := by decide
  have hdescent : baseEnd_1860583 < baseStart_1860583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860639 : List Nat := [1, 1, 2, 4, 1, 3, 3, 6]
def baseStart_1860639 : Nat := 118140960795 + 1860639 * 2 ^ 59
def prefixEnd_1860639 : Nat := 4983230072969 + 3 ^ 40 * 1860639 * 2
def baseEnd_1860639 : Nat := 141541056518674218526753

theorem tailTrace_1860639 : CollatzResearch.WordTrace tailWord_1860639 prefixEnd_1860639 141541056518674218526753 := by
  unfold tailWord_1860639
  simp only [CollatzResearch.WordTrace]
  refine ⟨67863079506230149687200971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45242053004153433124800647 67863079506230149687200971)
  ·
    refine ⟨101794619259345224530801457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67863079506230149687200971 101794619259345224530801457)
    ·
      refine ⟨76345964444508918398101093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101794619259345224530801457 76345964444508918398101093)
      ·
        refine ⟨14314868333345422199643955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76345964444508918398101093 14314868333345422199643955)
        ·
          refine ⟨21472302500018133299465933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14314868333345422199643955 21472302500018133299465933)
          ·
            refine ⟨8052113437506799987299725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21472302500018133299465933 8052113437506799987299725)
            ·
              refine ⟨3019542539065049995237397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8052113437506799987299725 3019542539065049995237397)
              ·
                refine ⟨141541056518674218526753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3019542539065049995237397 141541056518674218526753)
                ·
                  rfl

theorem cell21_1860639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 6].length) (baseStart_1860639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1860639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1860639 prefixEnd_1860639 := by exact prefixLift 1860639
  have htrace : WordTrace (prefixWord ++ tailWord_1860639) baseStart_1860639 baseEnd_1860639 := by
    simpa [prefixWord, tailWord_1860639, baseEnd_1860639] using wordTrace_append hprefix tailTrace_1860639
  have hstable : (prefixWord ++ tailWord_1860639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860639).length < 2 ^ (prefixWord ++ tailWord_1860639).sum := by decide
  have hdescent : baseEnd_1860639 < baseStart_1860639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860805 : List Nat := [1, 3, 1, 1, 1, 1, 3, 5, 5]
def baseStart_1860805 : Nat := 118140960795 + 1860805 * 2 ^ 59
def prefixEnd_1860805 : Nat := 4983230072969 + 3 ^ 40 * 1860805 * 2
def baseEnd_1860805 : Nat := 424661053017643255813253

theorem tailTrace_1860805 : CollatzResearch.WordTrace tailWord_1860805 prefixEnd_1860805 424661053017643255813253 := by
  unfold tailWord_1860805
  simp only [CollatzResearch.WordTrace]
  refine ⟨67869134023628760037743869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45246089349085840025162579 67869134023628760037743869)
  ·
    refine ⟨25450925258860785014153951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67869134023628760037743869 25450925258860785014153951)
    ·
      refine ⟨38176387888291177521230927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25450925258860785014153951 38176387888291177521230927)
      ·
        refine ⟨57264581832436766281846391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38176387888291177521230927 57264581832436766281846391)
        ·
          refine ⟨85896872748655149422769587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57264581832436766281846391 85896872748655149422769587)
          ·
            refine ⟨128845309122982724134154381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85896872748655149422769587 128845309122982724134154381)
            ·
              refine ⟨48316990921118521550307893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128845309122982724134154381 48316990921118521550307893)
              ·
                refine ⟨4529717898854861395341365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48316990921118521550307893 4529717898854861395341365)
                ·
                  refine ⟨424661053017643255813253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4529717898854861395341365 424661053017643255813253)
                  ·
                    rfl

theorem cell21_1860805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_1860805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1860805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1860805 prefixEnd_1860805 := by exact prefixLift 1860805
  have htrace : WordTrace (prefixWord ++ tailWord_1860805) baseStart_1860805 baseEnd_1860805 := by
    simpa [prefixWord, tailWord_1860805, baseEnd_1860805] using wordTrace_append hprefix tailTrace_1860805
  have hstable : (prefixWord ++ tailWord_1860805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860805).length < 2 ^ (prefixWord ++ tailWord_1860805).sum := by decide
  have hdescent : baseEnd_1860805 < baseStart_1860805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860881 : List Nat := [1, 2, 2, 1, 1, 4, 1, 4, 5]
def baseStart_1860881 : Nat := 118140960795 + 1860881 * 2 ^ 59
def prefixEnd_1860881 : Nat := 4983230072969 + 3 ^ 40 * 1860881 * 2
def baseEnd_1860881 : Nat := 424678397253084012546431

theorem tailTrace_1860881 : CollatzResearch.WordTrace tailWord_1860881 prefixEnd_1860881 424678397253084012546431 := by
  unfold tailWord_1860881
  simp only [CollatzResearch.WordTrace]
  refine ⟨67871905971353425017510497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45247937314235616678340331 67871905971353425017510497)
  ·
    refine ⟨50903929478515068763132873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67871905971353425017510497 50903929478515068763132873)
    ·
      refine ⟨38177947108886301572349655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50903929478515068763132873 38177947108886301572349655)
      ·
        refine ⟨57266920663329452358524483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38177947108886301572349655 57266920663329452358524483)
        ·
          refine ⟨85900380994994178537786725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57266920663329452358524483 85900380994994178537786725)
          ·
            refine ⟨16106321436561408475835011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85900380994994178537786725 16106321436561408475835011)
            ·
              refine ⟨24159482154842112713752517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16106321436561408475835011 24159482154842112713752517)
              ·
                refine ⟨4529902904032896133828597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24159482154842112713752517 4529902904032896133828597)
                ·
                  refine ⟨424678397253084012546431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4529902904032896133828597 424678397253084012546431)
                  ·
                    rfl

theorem cell21_1860881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_1860881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1860881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1860881 prefixEnd_1860881 := by exact prefixLift 1860881
  have htrace : WordTrace (prefixWord ++ tailWord_1860881) baseStart_1860881 baseEnd_1860881 := by
    simpa [prefixWord, tailWord_1860881, baseEnd_1860881] using wordTrace_append hprefix tailTrace_1860881
  have hstable : (prefixWord ++ tailWord_1860881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860881).length < 2 ^ (prefixWord ++ tailWord_1860881).sum := by decide
  have hdescent : baseEnd_1860881 < baseStart_1860881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860912 : List Nat := [2, 1, 1, 1, 2, 2, 4, 4, 4]
def baseStart_1860912 : Nat := 118140960795 + 1860912 * 2 ^ 59
def prefixEnd_1860912 : Nat := 4983230072969 + 3 ^ 40 * 1860912 * 2
def baseEnd_1860912 : Nat := 424685471875434847529701

theorem tailTrace_1860912 : CollatzResearch.WordTrace tailWord_1860912 prefixEnd_1860912 424685471875434847529701 := by
  unfold tailWord_1860912
  simp only [CollatzResearch.WordTrace]
  refine ⟨33936518317120558655944495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45248691089494078207925993 33936518317120558655944495)
  ·
    refine ⟨50904777475680837983916743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33936518317120558655944495 50904777475680837983916743)
    ·
      refine ⟨76357166213521256975875115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50904777475680837983916743 76357166213521256975875115)
      ·
        refine ⟨114535749320281885463812673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76357166213521256975875115 114535749320281885463812673)
        ·
          refine ⟨85901811990211414097859505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114535749320281885463812673 85901811990211414097859505)
          ·
            refine ⟨64426358992658560573394629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85901811990211414097859505 64426358992658560573394629)
            ·
              refine ⟨12079942311123480107511493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64426358992658560573394629 12079942311123480107511493)
              ·
                refine ⟨2264989183335652520158405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12079942311123480107511493 2264989183335652520158405)
                ·
                  refine ⟨424685471875434847529701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2264989183335652520158405 424685471875434847529701)
                  ·
                    rfl

theorem cell21_1860912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_1860912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1860912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1860912 prefixEnd_1860912 := by exact prefixLift 1860912
  have htrace : WordTrace (prefixWord ++ tailWord_1860912) baseStart_1860912 baseEnd_1860912 := by
    simpa [prefixWord, tailWord_1860912, baseEnd_1860912] using wordTrace_append hprefix tailTrace_1860912
  have hstable : (prefixWord ++ tailWord_1860912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860912).length < 2 ^ (prefixWord ++ tailWord_1860912).sum := by decide
  have hdescent : baseEnd_1860912 < baseStart_1860912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1860988 : List Nat := [2, 2, 2, 1, 1, 1, 3, 5, 4]
def baseStart_1860988 : Nat := 118140960795 + 1860988 * 2 ^ 59
def prefixEnd_1860988 : Nat := 4983230072969 + 3 ^ 40 * 1860988 * 2
def baseEnd_1860988 : Nat := 424702816110875604262879

theorem tailTrace_1860988 : CollatzResearch.WordTrace tailWord_1860988 prefixEnd_1860988 424702816110875604262879 := by
  unfold tailWord_1860988
  simp only [CollatzResearch.WordTrace]
  refine ⟨33937904290982891145827809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45250539054643854861103745 33937904290982891145827809)
  ·
    refine ⟨25453428218237168359370857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33937904290982891145827809 25453428218237168359370857)
    ·
      refine ⟨19090071163677876269528143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25453428218237168359370857 19090071163677876269528143)
      ·
        refine ⟨28635106745516814404292215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19090071163677876269528143 28635106745516814404292215)
        ·
          refine ⟨42952660118275221606438323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28635106745516814404292215 42952660118275221606438323)
          ·
            refine ⟨64428990177412832409657485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42952660118275221606438323 64428990177412832409657485)
            ·
              refine ⟨24160871316529812153621557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64428990177412832409657485 24160871316529812153621557)
              ·
                refine ⟨2265081685924669889402021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24160871316529812153621557 2265081685924669889402021)
                ·
                  refine ⟨424702816110875604262879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2265081685924669889402021 424702816110875604262879)
                  ·
                    rfl

theorem cell21_1860988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_1860988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1860988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1860988 prefixEnd_1860988 := by exact prefixLift 1860988
  have htrace : WordTrace (prefixWord ++ tailWord_1860988) baseStart_1860988 baseEnd_1860988 := by
    simpa [prefixWord, tailWord_1860988, baseEnd_1860988] using wordTrace_append hprefix tailTrace_1860988
  have hstable : (prefixWord ++ tailWord_1860988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1860988).length < 2 ^ (prefixWord ++ tailWord_1860988).sum := by decide
  have hdescent : baseEnd_1860988 < baseStart_1860988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1860988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861022 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1861022 : Nat := 118140960795 + 1861022 * 2 ^ 59
def prefixEnd_1861022 : Nat := 4983230072969 + 3 ^ 40 * 1861022 * 2
def baseEnd_1861022 : Nat := 424710575374099100696143

theorem tailTrace_1861022 : CollatzResearch.WordTrace tailWord_1861022 prefixEnd_1861022 424710575374099100696143 := by
  unfold tailWord_1861022
  simp only [CollatzResearch.WordTrace]
  refine ⟨8484631082980325762299165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45251365775895070732262213 8484631082980325762299165)
  ·
    refine ⟨3181736656117622160862187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8484631082980325762299165 3181736656117622160862187)
    ·
      refine ⟨4772604984176433241293281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3181736656117622160862187 4772604984176433241293281)
      ·
        refine ⟨3579453738132324930969961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4772604984176433241293281 3579453738132324930969961)
        ·
          refine ⟨2684590303599243698227471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3579453738132324930969961 2684590303599243698227471)
          ·
            refine ⟨4026885455398865547341207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2684590303599243698227471 4026885455398865547341207)
            ·
              refine ⟨6040328183098298321011811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4026885455398865547341207 6040328183098298321011811)
              ·
                refine ⟨9060492274647447481517717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6040328183098298321011811 9060492274647447481517717)
                ·
                  refine ⟨424710575374099100696143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9060492274647447481517717 424710575374099100696143)
                  ·
                    rfl

theorem cell21_1861022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1861022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861022 prefixEnd_1861022 := by exact prefixLift 1861022
  have htrace : WordTrace (prefixWord ++ tailWord_1861022) baseStart_1861022 baseEnd_1861022 := by
    simpa [prefixWord, tailWord_1861022, baseEnd_1861022] using wordTrace_append hprefix tailTrace_1861022
  have hstable : (prefixWord ++ tailWord_1861022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861022).length < 2 ^ (prefixWord ++ tailWord_1861022).sum := by decide
  have hdescent : baseEnd_1861022 < baseStart_1861022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861095 : List Nat := [1, 1, 5, 2, 1, 3, 2, 6]
def baseStart_1861095 : Nat := 118140960795 + 1861095 * 2 ^ 59
def prefixEnd_1861095 : Nat := 4983230072969 + 3 ^ 40 * 1861095 * 2
def baseEnd_1861095 : Nat := 141575744989555731993109

theorem tailTrace_1861095 : CollatzResearch.WordTrace tailWord_1861095 prefixEnd_1861095 141575744989555731993109 := by
  unfold tailWord_1861095
  simp only [CollatzResearch.WordTrace]
  refine ⟨67879711192578139565800739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45253140795052093043867159 67879711192578139565800739)
  ·
    refine ⟨101819566788867209348701109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67879711192578139565800739 101819566788867209348701109)
    ·
      refine ⟨9545584386456300876440729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 101819566788867209348701109 9545584386456300876440729)
      ·
        refine ⟨7159188289842225657330547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9545584386456300876440729 7159188289842225657330547)
        ·
          refine ⟨10738782434763338485995821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7159188289842225657330547 10738782434763338485995821)
          ·
            refine ⟨4027043413036251932248433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10738782434763338485995821 4027043413036251932248433)
            ·
              refine ⟨3020282559777188949186325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4027043413036251932248433 3020282559777188949186325)
              ·
                refine ⟨141575744989555731993109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3020282559777188949186325 141575744989555731993109)
                ·
                  rfl

theorem cell21_1861095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 6].length) (baseStart_1861095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861095 prefixEnd_1861095 := by exact prefixLift 1861095
  have htrace : WordTrace (prefixWord ++ tailWord_1861095) baseStart_1861095 baseEnd_1861095 := by
    simpa [prefixWord, tailWord_1861095, baseEnd_1861095] using wordTrace_append hprefix tailTrace_1861095
  have hstable : (prefixWord ++ tailWord_1861095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861095).length < 2 ^ (prefixWord ++ tailWord_1861095).sum := by decide
  have hdescent : baseEnd_1861095 < baseStart_1861095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861123 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 6]
def baseStart_1861123 : Nat := 118140960795 + 1861123 * 2 ^ 59
def prefixEnd_1861123 : Nat := 4983230072969 + 3 ^ 40 * 1861123 * 2
def baseEnd_1861123 : Nat := 424733624950145369512603

theorem tailTrace_1861123 : CollatzResearch.WordTrace tailWord_1861123 prefixEnd_1861123 424733624950145369512603 := by
  unfold tailWord_1861123
  simp only [CollatzResearch.WordTrace]
  refine ⟨67880732436476700347820023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45253821624317800231880015 67880732436476700347820023)
  ·
    refine ⟨101821098654715050521730035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67880732436476700347820023 101821098654715050521730035)
    ·
      refine ⟨152731647982072575782595053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101821098654715050521730035 152731647982072575782595053)
      ·
        refine ⟨57274367993277215918473145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152731647982072575782595053 57274367993277215918473145)
        ·
          refine ⟨42955775994957911938854859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57274367993277215918473145 42955775994957911938854859)
          ·
            refine ⟨64433663992436867908282289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42955775994957911938854859 64433663992436867908282289)
            ·
              refine ⟨48325247994327650931211717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64433663992436867908282289 48325247994327650931211717)
              ·
                refine ⟨9060983998936434549602197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48325247994327650931211717 9060983998936434549602197)
                ·
                  refine ⟨424733624950145369512603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9060983998936434549602197 424733624950145369512603)
                  ·
                    rfl

theorem cell21_1861123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 6].length) (baseStart_1861123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861123 prefixEnd_1861123 := by exact prefixLift 1861123
  have htrace : WordTrace (prefixWord ++ tailWord_1861123) baseStart_1861123 baseEnd_1861123 := by
    simpa [prefixWord, tailWord_1861123, baseEnd_1861123] using wordTrace_append hprefix tailTrace_1861123
  have hstable : (prefixWord ++ tailWord_1861123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861123).length < 2 ^ (prefixWord ++ tailWord_1861123).sum := by decide
  have hdescent : baseEnd_1861123 < baseStart_1861123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861171 : List Nat := [1, 1, 1, 2, 4, 4, 3, 5]
def baseStart_1861171 : Nat := 118140960795 + 1861171 * 2 ^ 59
def prefixEnd_1861171 : Nat := 4983230072969 + 3 ^ 40 * 1861171 * 2
def baseEnd_1861171 : Nat := 141581526401369317570835

theorem tailTrace_1861171 : CollatzResearch.WordTrace tailWord_1861171 prefixEnd_1861171 141581526401369317570835 := by
  unfold tailWord_1861171
  simp only [CollatzResearch.WordTrace]
  refine ⟨67882483140302804545567367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45254988760201869697044911 67882483140302804545567367)
  ·
    refine ⟨101823724710454206818351051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67882483140302804545567367 101823724710454206818351051)
    ·
      refine ⟨152735587065681310227526577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101823724710454206818351051 152735587065681310227526577)
      ·
        refine ⟨114551690299260982670644933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152735587065681310227526577 114551690299260982670644933)
        ·
          refine ⟨21478441931111434250745925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114551690299260982670644933 21478441931111434250745925)
          ·
            refine ⟨4027207862083393922014861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21478441931111434250745925 4027207862083393922014861)
            ·
              refine ⟨1510202948281272720755573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4027207862083393922014861 1510202948281272720755573)
              ·
                refine ⟨141581526401369317570835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1510202948281272720755573 141581526401369317570835)
                ·
                  rfl

theorem cell21_1861171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 5].length) (baseStart_1861171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861171 prefixEnd_1861171 := by exact prefixLift 1861171
  have htrace : WordTrace (prefixWord ++ tailWord_1861171) baseStart_1861171 baseEnd_1861171 := by
    simpa [prefixWord, tailWord_1861171, baseEnd_1861171] using wordTrace_append hprefix tailTrace_1861171
  have hstable : (prefixWord ++ tailWord_1861171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861171).length < 2 ^ (prefixWord ++ tailWord_1861171).sum := by decide
  have hdescent : baseEnd_1861171 < baseStart_1861171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861185 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 7]
def baseStart_1861185 : Nat := 118140960795 + 1861185 * 2 ^ 59
def prefixEnd_1861185 : Nat := 4983230072969 + 3 ^ 40 * 1861185 * 2
def baseEnd_1861185 : Nat := 424747774194847039479143

theorem tailTrace_1861185 : CollatzResearch.WordTrace tailWord_1861185 prefixEnd_1861185 424747774194847039479143 := by
  unfold tailWord_1861185
  simp only [CollatzResearch.WordTrace]
  refine ⟨67882993762252084936577009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45255329174834723291051339 67882993762252084936577009)
  ·
    refine ⟨50912245321689063702432757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67882993762252084936577009 50912245321689063702432757)
    ·
      refine ⟨4773022998908349722103071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50912245321689063702432757 4773022998908349722103071)
      ·
        refine ⟨7159534498362524583154607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4773022998908349722103071 7159534498362524583154607)
        ·
          refine ⟨10739301747543786874731911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7159534498362524583154607 10739301747543786874731911)
          ·
            refine ⟨16108952621315680312097867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10739301747543786874731911 16108952621315680312097867)
            ·
              refine ⟨24163428931973520468146801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16108952621315680312097867 24163428931973520468146801)
              ·
                refine ⟨18122571698980140351110101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24163428931973520468146801 18122571698980140351110101)
                ·
                  refine ⟨424747774194847039479143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18122571698980140351110101 424747774194847039479143)
                  ·
                    rfl

theorem cell21_1861185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_1861185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861185 prefixEnd_1861185 := by exact prefixLift 1861185
  have htrace : WordTrace (prefixWord ++ tailWord_1861185) baseStart_1861185 baseEnd_1861185 := by
    simpa [prefixWord, tailWord_1861185, baseEnd_1861185] using wordTrace_append hprefix tailTrace_1861185
  have hstable : (prefixWord ++ tailWord_1861185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861185).length < 2 ^ (prefixWord ++ tailWord_1861185).sum := by decide
  have hdescent : baseEnd_1861185 < baseStart_1861185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861202 : List Nat := [3, 2, 2, 1, 2, 3, 2, 1, 5]
def baseStart_1861202 : Nat := 118140960795 + 1861202 * 2 ^ 59
def prefixEnd_1861202 : Nat := 4983230072969 + 3 ^ 40 * 1861202 * 2
def baseEnd_1861202 : Nat := 424751653826458787695775

theorem tailTrace_1861202 : CollatzResearch.WordTrace tailWord_1861202 prefixEnd_1861202 424751653826458787695775 := by
  unfold tailWord_1861202
  simp only [CollatzResearch.WordTrace]
  refine ⟨16970903450797624209986465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45255742535460331226630573 16970903450797624209986465)
  ·
    refine ⟨12728177588098218157489849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16970903450797624209986465 12728177588098218157489849)
    ·
      refine ⟨9546133191073663618117387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12728177588098218157489849 9546133191073663618117387)
      ·
        refine ⟨14319199786610495427176081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9546133191073663618117387 14319199786610495427176081)
        ·
          refine ⟨10739399839957871570382061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14319199786610495427176081 10739399839957871570382061)
          ·
            refine ⟨4027274939984201838893273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10739399839957871570382061 4027274939984201838893273)
            ·
              refine ⟨3020456204988151379169955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4027274939984201838893273 3020456204988151379169955)
              ·
                refine ⟨4530684307482227068754933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3020456204988151379169955 4530684307482227068754933)
                ·
                  refine ⟨424751653826458787695775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4530684307482227068754933 424751653826458787695775)
                  ·
                    rfl

theorem cell21_1861202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_1861202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861202 prefixEnd_1861202 := by exact prefixLift 1861202
  have htrace : WordTrace (prefixWord ++ tailWord_1861202) baseStart_1861202 baseEnd_1861202 := by
    simpa [prefixWord, tailWord_1861202, baseEnd_1861202] using wordTrace_append hprefix tailTrace_1861202
  have hstable : (prefixWord ++ tailWord_1861202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861202).length < 2 ^ (prefixWord ++ tailWord_1861202).sum := by decide
  have hdescent : baseEnd_1861202 < baseStart_1861202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861337 : List Nat := [1, 2, 1, 2, 3, 4, 1, 2, 5]
def baseStart_1861337 : Nat := 118140960795 + 1861337 * 2 ^ 59
def prefixEnd_1861337 : Nat := 4983230072969 + 3 ^ 40 * 1861337 * 2
def baseEnd_1861337 : Nat := 424782462665728552945499

theorem tailTrace_1861337 : CollatzResearch.WordTrace tailWord_1861337 prefixEnd_1861337 424782462665728552945499 := by
  unfold tailWord_1861337
  simp only [CollatzResearch.WordTrace]
  refine ⟨67888537657701414896110265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45259025105134276597406843 67888537657701414896110265)
  ·
    refine ⟨50916403243276061172082699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67888537657701414896110265 50916403243276061172082699)
    ·
      refine ⟨76374604864914091758124049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50916403243276061172082699 76374604864914091758124049)
      ·
        refine ⟨57280953648685568818593037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76374604864914091758124049 57280953648685568818593037)
        ·
          refine ⟨21480357618257088306972389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57280953648685568818593037 21480357618257088306972389)
          ·
            refine ⟨4027567053423204057557323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21480357618257088306972389 4027567053423204057557323)
            ·
              refine ⟨6041350580134806086335985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4027567053423204057557323 6041350580134806086335985)
              ·
                refine ⟨4531012935101104564751989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6041350580134806086335985 4531012935101104564751989)
                ·
                  refine ⟨424782462665728552945499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4531012935101104564751989 424782462665728552945499)
                  ·
                    rfl

theorem cell21_1861337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_1861337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861337 prefixEnd_1861337 := by exact prefixLift 1861337
  have htrace : WordTrace (prefixWord ++ tailWord_1861337) baseStart_1861337 baseEnd_1861337 := by
    simpa [prefixWord, tailWord_1861337, baseEnd_1861337] using wordTrace_append hprefix tailTrace_1861337
  have hstable : (prefixWord ++ tailWord_1861337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861337).length < 2 ^ (prefixWord ++ tailWord_1861337).sum := by decide
  have hdescent : baseEnd_1861337 < baseStart_1861337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861354 : List Nat := [3, 1, 3, 1, 1, 1, 3, 5, 3]
def baseStart_1861354 : Nat := 118140960795 + 1861354 * 2 ^ 59
def prefixEnd_1861354 : Nat := 4983230072969 + 3 ^ 40 * 1861354 * 2
def baseEnd_1861354 : Nat := 424786342297340301162131

theorem tailTrace_1861354 : CollatzResearch.WordTrace tailWord_1861354 prefixEnd_1861354 424786342297340301162131 := by
  unfold tailWord_1861354
  simp only [CollatzResearch.WordTrace]
  refine ⟨16972289424659956699869779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45259438465759884532986077 16972289424659956699869779)
  ·
    refine ⟨25458434136989935049804669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16972289424659956699869779 25458434136989935049804669)
    ·
      refine ⟨9546912801371225643676751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25458434136989935049804669 9546912801371225643676751)
      ·
        refine ⟨14320369202056838465515127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9546912801371225643676751 14320369202056838465515127)
        ·
          refine ⟨21480553803085257698272691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14320369202056838465515127 21480553803085257698272691)
          ·
            refine ⟨32220830704627886547409037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21480553803085257698272691 32220830704627886547409037)
            ·
              refine ⟨12082811514235457455278389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32220830704627886547409037 12082811514235457455278389)
              ·
                refine ⟨1132763579459574136432349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12082811514235457455278389 1132763579459574136432349)
                ·
                  refine ⟨424786342297340301162131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1132763579459574136432349 424786342297340301162131)
                  ·
                    rfl

theorem cell21_1861354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 3].length) (baseStart_1861354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861354 prefixEnd_1861354 := by exact prefixLift 1861354
  have htrace : WordTrace (prefixWord ++ tailWord_1861354) baseStart_1861354 baseEnd_1861354 := by
    simpa [prefixWord, tailWord_1861354, baseEnd_1861354] using wordTrace_append hprefix tailTrace_1861354
  have hstable : (prefixWord ++ tailWord_1861354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861354).length < 2 ^ (prefixWord ++ tailWord_1861354).sum := by decide
  have hdescent : baseEnd_1861354 < baseStart_1861354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861399 : List Nat := [1, 1, 3, 4, 2, 1, 4, 5]
def baseStart_1861399 : Nat := 118140960795 + 1861399 * 2 ^ 59
def prefixEnd_1861399 : Nat := 4983230072969 + 3 ^ 40 * 1861399 * 2
def baseEnd_1861399 : Nat := 141598870636810074304013

theorem tailTrace_1861399 : CollatzResearch.WordTrace tailWord_1861399 prefixEnd_1861399 141598870636810074304013 := by
  unfold tailWord_1861399
  simp only [CollatzResearch.WordTrace]
  refine ⟨67890798983476799484867251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45260532655651199656578167 67890798983476799484867251)
  ·
    refine ⟨101836198475215199227300877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67890798983476799484867251 101836198475215199227300877)
    ·
      refine ⟨38188574428205699710237829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101836198475215199227300877 38188574428205699710237829)
      ·
        refine ⟨7160357705288568695669593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38188574428205699710237829 7160357705288568695669593)
        ·
          refine ⟨5370268278966426521752195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7160357705288568695669593 5370268278966426521752195)
          ·
            refine ⟨8055402418449639782628293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5370268278966426521752195 8055402418449639782628293)
            ·
              refine ⟨1510387953459307459242805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8055402418449639782628293 1510387953459307459242805)
              ·
                refine ⟨141598870636810074304013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1510387953459307459242805 141598870636810074304013)
                ·
                  rfl

theorem cell21_1861399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 5].length) (baseStart_1861399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861399 prefixEnd_1861399 := by exact prefixLift 1861399
  have htrace : WordTrace (prefixWord ++ tailWord_1861399) baseStart_1861399 baseEnd_1861399 := by
    simpa [prefixWord, tailWord_1861399, baseEnd_1861399] using wordTrace_append hprefix tailTrace_1861399
  have hstable : (prefixWord ++ tailWord_1861399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861399).length < 2 ^ (prefixWord ++ tailWord_1861399).sum := by decide
  have hdescent : baseEnd_1861399 < baseStart_1861399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861458 : List Nat := [3, 2, 2, 1, 1, 3, 2, 7]
def baseStart_1861458 : Nat := 118140960795 + 1861458 * 2 ^ 59
def prefixEnd_1861458 : Nat := 4983230072969 + 3 ^ 40 * 1861458 * 2
def baseEnd_1861458 : Nat := 141603358838086410476195

theorem tailTrace_1861458 : CollatzResearch.WordTrace tailWord_1861458 prefixEnd_1861458 141603358838086410476195 := by
  unfold tailWord_1861458
  simp only [CollatzResearch.WordTrace]
  refine ⟨16973237722565763140316257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45261967260175368374176685 16973237722565763140316257)
  ·
    refine ⟨12729928291924322355237193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16973237722565763140316257 12729928291924322355237193)
    ·
      refine ⟨9547446218943241766427895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12729928291924322355237193 9547446218943241766427895)
      ·
        refine ⟨14321169328414862649641843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9547446218943241766427895 14321169328414862649641843)
        ·
          refine ⟨21481753992622293974462765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14321169328414862649641843 21481753992622293974462765)
          ·
            refine ⟨8055657747233360240423537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21481753992622293974462765 8055657747233360240423537)
            ·
              refine ⟨6041743310425020180317653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8055657747233360240423537 6041743310425020180317653)
              ·
                refine ⟨141603358838086410476195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6041743310425020180317653 141603358838086410476195)
                ·
                  rfl

theorem cell21_1861458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_1861458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861458 prefixEnd_1861458 := by exact prefixLift 1861458
  have htrace : WordTrace (prefixWord ++ tailWord_1861458) baseStart_1861458 baseEnd_1861458 := by
    simpa [prefixWord, tailWord_1861458, baseEnd_1861458] using wordTrace_append hprefix tailTrace_1861458
  have hstable : (prefixWord ++ tailWord_1861458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861458).length < 2 ^ (prefixWord ++ tailWord_1861458).sum := by decide
  have hdescent : baseEnd_1861458 < baseStart_1861458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861565 : List Nat := [1, 4, 1, 2, 3, 1, 2, 2, 5]
def baseStart_1861565 : Nat := 118140960795 + 1861565 * 2 ^ 59
def prefixEnd_1861565 : Nat := 4983230072969 + 3 ^ 40 * 1861565 * 2
def baseEnd_1861565 : Nat := 424834495372050823145033

theorem tailTrace_1861565 : CollatzResearch.WordTrace tailWord_1861565 prefixEnd_1861565 424834495372050823145033 := by
  unfold tailWord_1861565
  simp only [CollatzResearch.WordTrace]
  refine ⟨67896853500875409835410149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45264569000583606556940099 67896853500875409835410149)
  ·
    refine ⟨12730660031414139344139403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67896853500875409835410149 12730660031414139344139403)
    ·
      refine ⟨19095990047121209016209105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12730660031414139344139403 19095990047121209016209105)
      ·
        refine ⟨14321992535340906762156829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19095990047121209016209105 14321992535340906762156829)
        ·
          refine ⟨5370747200752840035808811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14321992535340906762156829 5370747200752840035808811)
          ·
            refine ⟨8056120801129260053713217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5370747200752840035808811 8056120801129260053713217)
            ·
              refine ⟨6042090600846945040284913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8056120801129260053713217 6042090600846945040284913)
              ·
                refine ⟨4531567950635208780213685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6042090600846945040284913 4531567950635208780213685)
                ·
                  refine ⟨424834495372050823145033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4531567950635208780213685 424834495372050823145033)
                  ·
                    rfl

theorem cell21_1861565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_1861565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861565 prefixEnd_1861565 := by exact prefixLift 1861565
  have htrace : WordTrace (prefixWord ++ tailWord_1861565) baseStart_1861565 baseEnd_1861565 := by
    simpa [prefixWord, tailWord_1861565, baseEnd_1861565] using wordTrace_append hprefix tailTrace_1861565
  have hstable : (prefixWord ++ tailWord_1861565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861565).length < 2 ^ (prefixWord ++ tailWord_1861565).sum := by decide
  have hdescent : baseEnd_1861565 < baseStart_1861565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861599 : List Nat := [1, 1, 2, 3, 4, 2, 3, 2, 3]
def baseStart_1861599 : Nat := 118140960795 + 1861599 * 2 ^ 59
def prefixEnd_1861599 : Nat := 4983230072969 + 3 ^ 40 * 1861599 * 2
def baseEnd_1861599 : Nat := 424842254635274319578297

theorem tailTrace_1861599 : CollatzResearch.WordTrace tailWord_1861599 prefixEnd_1861599 424842254635274319578297 := by
  unfold tailWord_1861599
  simp only [CollatzResearch.WordTrace]
  refine ⟨67898093582752233642147851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45265395721834822428098567 67898093582752233642147851)
  ·
    refine ⟨101847140374128350463221777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67898093582752233642147851 101847140374128350463221777)
    ·
      refine ⟨76385355280596262847416333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101847140374128350463221777 76385355280596262847416333)
      ·
        refine ⟨28644508230223598567781125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76385355280596262847416333 28644508230223598567781125)
        ·
          refine ⟨5370845293166924731458961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28644508230223598567781125 5370845293166924731458961)
          ·
            refine ⟨4028133969875193548594221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5370845293166924731458961 4028133969875193548594221)
            ·
              refine ⟨1510550238703197580722833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4028133969875193548594221 1510550238703197580722833)
              ·
                refine ⟨1132912679027398185542125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1510550238703197580722833 1132912679027398185542125)
                ·
                  refine ⟨424842254635274319578297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1132912679027398185542125 424842254635274319578297)
                  ·
                    rfl

theorem cell21_1861599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 3].length) (baseStart_1861599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861599 prefixEnd_1861599 := by exact prefixLift 1861599
  have htrace : WordTrace (prefixWord ++ tailWord_1861599) baseStart_1861599 baseEnd_1861599 := by
    simpa [prefixWord, tailWord_1861599, baseEnd_1861599] using wordTrace_append hprefix tailTrace_1861599
  have hstable : (prefixWord ++ tailWord_1861599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861599).length < 2 ^ (prefixWord ++ tailWord_1861599).sum := by decide
  have hdescent : baseEnd_1861599 < baseStart_1861599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861610 : List Nat := [3, 1, 3, 1, 2, 1, 4, 6]
def baseStart_1861610 : Nat := 118140960795 + 1861610 * 2 ^ 59
def prefixEnd_1861610 : Nat := 4983230072969 + 3 ^ 40 * 1861610 * 2
def baseEnd_1861610 : Nat := 141614921661713581631647

theorem tailTrace_1861610 : CollatzResearch.WordTrace tailWord_1861610 prefixEnd_1861610 141614921661713581631647 := by
  unfold tailWord_1861610
  simp only [CollatzResearch.WordTrace]
  refine ⟨16974623696428095630199571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45265663190474921680532189 16974623696428095630199571)
  ·
    refine ⟨25461935544642143445299357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16974623696428095630199571 25461935544642143445299357)
    ·
      refine ⟨9548225829240803791987259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25461935544642143445299357 9548225829240803791987259)
      ·
        refine ⟨14322338743861205687980889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9548225829240803791987259 14322338743861205687980889)
        ·
          refine ⟨10741754057895904265985667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14322338743861205687980889 10741754057895904265985667)
          ·
            refine ⟨16112631086843856398978501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10741754057895904265985667 16112631086843856398978501)
            ·
              refine ⟨3021118328783223074808469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16112631086843856398978501 3021118328783223074808469)
              ·
                refine ⟨141614921661713581631647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3021118328783223074808469 141614921661713581631647)
                ·
                  rfl

theorem cell21_1861610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_1861610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861610 prefixEnd_1861610 := by exact prefixLift 1861610
  have htrace : WordTrace (prefixWord ++ tailWord_1861610) baseStart_1861610 baseEnd_1861610 := by
    simpa [prefixWord, tailWord_1861610, baseEnd_1861610] using wordTrace_append hprefix tailTrace_1861610
  have hstable : (prefixWord ++ tailWord_1861610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861610).length < 2 ^ (prefixWord ++ tailWord_1861610).sum := by decide
  have hdescent : baseEnd_1861610 < baseStart_1861610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861624 : List Nat := [2, 1, 2, 1, 1, 3, 2, 4, 5]
def baseStart_1861624 : Nat := 118140960795 + 1861624 * 2 ^ 59
def prefixEnd_1861624 : Nat := 4983230072969 + 3 ^ 40 * 1861624 * 2
def baseEnd_1861624 : Nat := 424847959975879831661579

theorem tailTrace_1861624 : CollatzResearch.WordTrace tailWord_1861624 prefixEnd_1861624 424847959975879831661579 := by
  unfold tailWord_1861624
  simp only [CollatzResearch.WordTrace]
  refine ⟨33949502703830831455903963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45266003605107775274538617 33949502703830831455903963)
  ·
    refine ⟨50924254055746247183855945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33949502703830831455903963 50924254055746247183855945)
    ·
      refine ⟨38193190541809685387891959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50924254055746247183855945 38193190541809685387891959)
      ·
        refine ⟨57289785812714528081837939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38193190541809685387891959 57289785812714528081837939)
        ·
          refine ⟨85934678719071792122756909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57289785812714528081837939 85934678719071792122756909)
          ·
            refine ⟨32225504519651922046033841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85934678719071792122756909 32225504519651922046033841)
            ·
              refine ⟨24169128389738941534525381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32225504519651922046033841 24169128389738941534525381)
              ·
                refine ⟨4531711573076051537723509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24169128389738941534525381 4531711573076051537723509)
                ·
                  refine ⟨424847959975879831661579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4531711573076051537723509 424847959975879831661579)
                  ·
                    rfl

theorem cell21_1861624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_1861624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861624 prefixEnd_1861624 := by exact prefixLift 1861624
  have htrace : WordTrace (prefixWord ++ tailWord_1861624) baseStart_1861624 baseEnd_1861624 := by
    simpa [prefixWord, tailWord_1861624, baseEnd_1861624] using wordTrace_append hprefix tailTrace_1861624
  have hstable : (prefixWord ++ tailWord_1861624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861624).length < 2 ^ (prefixWord ++ tailWord_1861624).sum := by decide
  have hdescent : baseEnd_1861624 < baseStart_1861624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861658 : List Nat := [3, 1, 1, 3, 1, 4, 1, 4, 3]
def baseStart_1861658 : Nat := 118140960795 + 1861658 * 2 ^ 59
def prefixEnd_1861658 : Nat := 4983230072969 + 3 ^ 40 * 1861658 * 2
def baseEnd_1861658 : Nat := 424855719239103328094843

theorem tailTrace_1861658 : CollatzResearch.WordTrace tailWord_1861658 prefixEnd_1861658 424855719239103328094843 := by
  unfold tailWord_1861658
  simp only [CollatzResearch.WordTrace]
  refine ⟨16975061372384621679636407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45266830326358991145697085 16975061372384621679636407)
  ·
    refine ⟨25462592058576932519454611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16975061372384621679636407 25462592058576932519454611)
    ·
      refine ⟨38193888087865398779181917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25462592058576932519454611 38193888087865398779181917)
      ·
        refine ⟨14322708032949524542193219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38193888087865398779181917 14322708032949524542193219)
        ·
          refine ⟨21484062049424286813289829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14322708032949524542193219 21484062049424286813289829)
          ·
            refine ⟨4028261634267053777491843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21484062049424286813289829 4028261634267053777491843)
            ·
              refine ⟨6042392451400580666237765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4028261634267053777491843 6042392451400580666237765)
              ·
                refine ⟨1132948584637608874919581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6042392451400580666237765 1132948584637608874919581)
                ·
                  refine ⟨424855719239103328094843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1132948584637608874919581 424855719239103328094843)
                  ·
                    rfl

theorem cell21_1861658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_1861658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861658 prefixEnd_1861658 := by exact prefixLift 1861658
  have htrace : WordTrace (prefixWord ++ tailWord_1861658) baseStart_1861658 baseEnd_1861658 := by
    simpa [prefixWord, tailWord_1861658, baseEnd_1861658] using wordTrace_append hprefix tailTrace_1861658
  have hstable : (prefixWord ++ tailWord_1861658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861658).length < 2 ^ (prefixWord ++ tailWord_1861658).sum := by decide
  have hdescent : baseEnd_1861658 < baseStart_1861658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861717 : List Nat := [1, 3, 2, 2, 1, 4, 2, 1, 5]
def baseStart_1861717 : Nat := 118140960795 + 1861717 * 2 ^ 59
def prefixEnd_1861717 : Nat := 4983230072969 + 3 ^ 40 * 1861717 * 2
def baseEnd_1861717 : Nat := 424869183842932336611389

theorem tailTrace_1861717 : CollatzResearch.WordTrace tailWord_1861717 prefixEnd_1861717 424869183842932336611389 := by
  unfold tailWord_1861717
  simp only [CollatzResearch.WordTrace]
  refine ⟨67902397396324739794943405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45268264930883159863295603 67902397396324739794943405)
  ·
    refine ⟨25463399023621777423103777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67902397396324739794943405 25463399023621777423103777)
    ·
      refine ⟨19097549267716333067327833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25463399023621777423103777 19097549267716333067327833)
      ·
        refine ⟨14323161950787249800495875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19097549267716333067327833 14323161950787249800495875)
        ·
          refine ⟨21484742926180874700743813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14323161950787249800495875 21484742926180874700743813)
          ·
            refine ⟨4028389298658914006389465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21484742926180874700743813 4028389298658914006389465)
            ·
              refine ⟨3021291973994185504792099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4028389298658914006389465 3021291973994185504792099)
              ·
                refine ⟨4531937960991278257188149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3021291973994185504792099 4531937960991278257188149)
                ·
                  refine ⟨424869183842932336611389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4531937960991278257188149 424869183842932336611389)
                  ·
                    rfl

theorem cell21_1861717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_1861717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861717 prefixEnd_1861717 := by exact prefixLift 1861717
  have htrace : WordTrace (prefixWord ++ tailWord_1861717) baseStart_1861717 baseEnd_1861717 := by
    simpa [prefixWord, tailWord_1861717, baseEnd_1861717] using wordTrace_append hprefix tailTrace_1861717
  have hstable : (prefixWord ++ tailWord_1861717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861717).length < 2 ^ (prefixWord ++ tailWord_1861717).sum := by decide
  have hdescent : baseEnd_1861717 < baseStart_1861717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861731 : List Nat := [1, 1, 1, 5, 1, 1, 2, 5, 4]
def baseStart_1861731 : Nat := 118140960795 + 1861731 * 2 ^ 59
def prefixEnd_1861731 : Nat := 4983230072969 + 3 ^ 40 * 1861731 * 2
def baseEnd_1861731 : Nat := 424872378833671423378027

theorem tailTrace_1861731 : CollatzResearch.WordTrace tailWord_1861731 prefixEnd_1861731 424872378833671423378027 := by
  unfold tailWord_1861731
  simp only [CollatzResearch.WordTrace]
  refine ⟨67902908018274020185953047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45268605345516013457302031 67902908018274020185953047)
  ·
    refine ⟨101854362027411030278929571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67902908018274020185953047 101854362027411030278929571)
    ·
      refine ⟨152781543041116545418394357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101854362027411030278929571 152781543041116545418394357)
      ·
        refine ⟨14323269660104676132974471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152781543041116545418394357 14323269660104676132974471)
        ·
          refine ⟨21484904490157014199461707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14323269660104676132974471 21484904490157014199461707)
          ·
            refine ⟨32227356735235521299192561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21484904490157014199461707 32227356735235521299192561)
            ·
              refine ⟨24170517551426640974394421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32227356735235521299192561 24170517551426640974394421)
              ·
                refine ⟨2265986020446247591349477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24170517551426640974394421 2265986020446247591349477)
                ·
                  refine ⟨424872378833671423378027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2265986020446247591349477 424872378833671423378027)
                  ·
                    rfl

theorem cell21_1861731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 4].length) (baseStart_1861731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861731 prefixEnd_1861731 := by exact prefixLift 1861731
  have htrace : WordTrace (prefixWord ++ tailWord_1861731) baseStart_1861731 baseEnd_1861731 := by
    simpa [prefixWord, tailWord_1861731, baseEnd_1861731] using wordTrace_append hprefix tailTrace_1861731
  have hstable : (prefixWord ++ tailWord_1861731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861731).length < 2 ^ (prefixWord ++ tailWord_1861731).sum := by decide
  have hdescent : baseEnd_1861731 < baseStart_1861731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861745 : List Nat := [1, 2, 2, 2, 1, 1, 5, 7]
def baseStart_1861745 : Nat := 118140960795 + 1861745 * 2 ^ 59
def prefixEnd_1861745 : Nat := 4983230072969 + 3 ^ 40 * 1861745 * 2
def baseEnd_1861745 : Nat := 141625191274803503381555

theorem tailTrace_1861745 : CollatzResearch.WordTrace tailWord_1861745 prefixEnd_1861745 141625191274803503381555 := by
  unfold tailWord_1861745
  simp only [CollatzResearch.WordTrace]
  refine ⟨67903418640223300576962689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45268945760148867051308459 67903418640223300576962689)
  ·
    refine ⟨50927563980167475432722017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67903418640223300576962689 50927563980167475432722017)
    ·
      refine ⟨38195672985125606574541513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50927563980167475432722017 38195672985125606574541513)
      ·
        refine ⟨28646754738844204930906135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38195672985125606574541513 28646754738844204930906135)
        ·
          refine ⟨42970132108266307396359203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28646754738844204930906135 42970132108266307396359203)
          ·
            refine ⟨64455198162399461094538805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42970132108266307396359203 64455198162399461094538805)
            ·
              refine ⟨6042674827724949477613013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64455198162399461094538805 6042674827724949477613013)
              ·
                refine ⟨141625191274803503381555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6042674827724949477613013 141625191274803503381555)
                ·
                  rfl

theorem cell21_1861745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 7].length) (baseStart_1861745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861745 prefixEnd_1861745 := by exact prefixLift 1861745
  have htrace : WordTrace (prefixWord ++ tailWord_1861745) baseStart_1861745 baseEnd_1861745 := by
    simpa [prefixWord, tailWord_1861745, baseEnd_1861745] using wordTrace_append hprefix tailTrace_1861745
  have hstable : (prefixWord ++ tailWord_1861745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861745).length < 2 ^ (prefixWord ++ tailWord_1861745).sum := by decide
  have hdescent : baseEnd_1861745 < baseStart_1861745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861824 : List Nat := [2, 1, 1, 2, 5, 2, 2, 2, 4]
def baseStart_1861824 : Nat := 118140960795 + 1861824 * 2 ^ 59
def prefixEnd_1861824 : Nat := 4983230072969 + 3 ^ 40 * 1861824 * 2
def baseEnd_1861824 : Nat := 424893602700723928327837

theorem tailTrace_1861824 : CollatzResearch.WordTrace tailWord_1861824 prefixEnd_1861824 424893602700723928327837 := by
  unfold tailWord_1861824
  simp only [CollatzResearch.WordTrace]
  refine ⟨33953150003468548534544263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45270866671291398046059017 33953150003468548534544263)
  ·
    refine ⟨50929725005202822801816395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33953150003468548534544263 50929725005202822801816395)
    ·
      refine ⟨76394587507804234202724593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50929725005202822801816395 76394587507804234202724593)
      ·
        refine ⟨57295940630853175652043445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76394587507804234202724593 57295940630853175652043445)
        ·
          refine ⟨5371494434142485217379073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57295940630853175652043445 5371494434142485217379073)
          ·
            refine ⟨4028620825606863913034305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5371494434142485217379073 4028620825606863913034305)
            ·
              refine ⟨3021465619205147934775729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4028620825606863913034305 3021465619205147934775729)
              ·
                refine ⟨2266099214403860951081797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3021465619205147934775729 2266099214403860951081797)
                ·
                  refine ⟨424893602700723928327837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2266099214403860951081797 424893602700723928327837)
                  ·
                    rfl

theorem cell21_1861824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_1861824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861824 prefixEnd_1861824 := by exact prefixLift 1861824
  have htrace : WordTrace (prefixWord ++ tailWord_1861824) baseStart_1861824 baseEnd_1861824 := by
    simpa [prefixWord, tailWord_1861824, baseEnd_1861824] using wordTrace_append hprefix tailTrace_1861824
  have hstable : (prefixWord ++ tailWord_1861824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861824).length < 2 ^ (prefixWord ++ tailWord_1861824).sum := by decide
  have hdescent : baseEnd_1861824 < baseStart_1861824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861838 : List Nat := [4, 1, 1, 1, 4, 1, 3, 6]
def baseStart_1861838 : Nat := 118140960795 + 1861838 * 2 ^ 59
def prefixEnd_1861838 : Nat := 4983230072969 + 3 ^ 40 * 1861838 * 2
def baseEnd_1861838 : Nat := 141632265897154338364825

theorem tailTrace_1861838 : CollatzResearch.WordTrace tailWord_1861838 prefixEnd_1861838 141632265897154338364825 := by
  unfold tailWord_1861838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8488351328610797182512271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45271207085924251640065445 8488351328610797182512271)
  ·
    refine ⟨12732526992916195773768407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8488351328610797182512271 12732526992916195773768407)
    ·
      refine ⟨19098790489374293660652611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12732526992916195773768407 19098790489374293660652611)
      ·
        refine ⟨28648185734061440490978917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19098790489374293660652611 28648185734061440490978917)
        ·
          refine ⟨5371534825136520092058547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28648185734061440490978917 5371534825136520092058547)
          ·
            refine ⟨8057302237704780138087821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5371534825136520092058547 8057302237704780138087821)
            ·
              refine ⟨3021488339139292551782933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8057302237704780138087821 3021488339139292551782933)
              ·
                refine ⟨141632265897154338364825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3021488339139292551782933 141632265897154338364825)
                ·
                  rfl

theorem cell21_1861838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_1861838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861838 prefixEnd_1861838 := by exact prefixLift 1861838
  have htrace : WordTrace (prefixWord ++ tailWord_1861838) baseStart_1861838 baseEnd_1861838 := by
    simpa [prefixWord, tailWord_1861838, baseEnd_1861838] using wordTrace_append hprefix tailTrace_1861838
  have hstable : (prefixWord ++ tailWord_1861838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861838).length < 2 ^ (prefixWord ++ tailWord_1861838).sum := by decide
  have hdescent : baseEnd_1861838 < baseStart_1861838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861886 : List Nat := [4, 2, 2, 1, 1, 1, 1, 6, 3]
def baseStart_1861886 : Nat := 118140960795 + 1861886 * 2 ^ 59
def prefixEnd_1861886 : Nat := 4983230072969 + 3 ^ 40 * 1861886 * 2
def baseEnd_1861886 : Nat := 424907751945425598294377

theorem tailTrace_1861886 : CollatzResearch.WordTrace tailWord_1861886 prefixEnd_1861886 424907751945425598294377 := by
  unfold tailWord_1861886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8488570166589060207230689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45272374221808321105230341 8488570166589060207230689)
  ·
    refine ⟨6366427624941795155423017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8488570166589060207230689 6366427624941795155423017)
    ·
      refine ⟨4774820718706346366567263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6366427624941795155423017 4774820718706346366567263)
      ·
        refine ⟨7162231078059519549850895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4774820718706346366567263 7162231078059519549850895)
        ·
          refine ⟨10743346617089279324776343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7162231078059519549850895 10743346617089279324776343)
          ·
            refine ⟨16115019925633918987164515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10743346617089279324776343 16115019925633918987164515)
            ·
              refine ⟨24172529888450878480746773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16115019925633918987164515 24172529888450878480746773)
              ·
                refine ⟨1133087338521134928785005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24172529888450878480746773 1133087338521134928785005)
                ·
                  refine ⟨424907751945425598294377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1133087338521134928785005 424907751945425598294377)
                  ·
                    rfl

theorem cell21_1861886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_1861886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861886 prefixEnd_1861886 := by exact prefixLift 1861886
  have htrace : WordTrace (prefixWord ++ tailWord_1861886) baseStart_1861886 baseEnd_1861886 := by
    simpa [prefixWord, tailWord_1861886, baseEnd_1861886] using wordTrace_append hprefix tailTrace_1861886
  have hstable : (prefixWord ++ tailWord_1861886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861886).length < 2 ^ (prefixWord ++ tailWord_1861886).sum := by decide
  have hdescent : baseEnd_1861886 < baseStart_1861886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861900 : List Nat := [2, 2, 1, 2, 2, 2, 5, 1, 4]
def baseStart_1861900 : Nat := 118140960795 + 1861900 * 2 ^ 59
def prefixEnd_1861900 : Nat := 4983230072969 + 3 ^ 40 * 1861900 * 2
def baseEnd_1861900 : Nat := 424910946936164685061015

theorem tailTrace_1861900 : CollatzResearch.WordTrace tailWord_1861900 prefixEnd_1861900 424910946936164685061015 := by
  unfold tailWord_1861900
  simp only [CollatzResearch.WordTrace]
  refine ⟨33954535977330881024427577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45272714636441174699236769 33954535977330881024427577)
  ·
    refine ⟨25465901982998160768320683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33954535977330881024427577 25465901982998160768320683)
    ·
      refine ⟨38198852974497241152481025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25465901982998160768320683 38198852974497241152481025)
      ·
        refine ⟨28649139730872930864360769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38198852974497241152481025 28649139730872930864360769)
        ·
          refine ⟨21486854798154698148270577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28649139730872930864360769 21486854798154698148270577)
          ·
            refine ⟨16115141098616023611202933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21486854798154698148270577 16115141098616023611202933)
            ·
              refine ⟨1510794477995252213550275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16115141098616023611202933 1510794477995252213550275)
              ·
                refine ⟨2266191716992878320325413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1510794477995252213550275 2266191716992878320325413)
                ·
                  refine ⟨424910946936164685061015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2266191716992878320325413 424910946936164685061015)
                  ·
                    rfl

theorem cell21_1861900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_1861900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861900 prefixEnd_1861900 := by exact prefixLift 1861900
  have htrace : WordTrace (prefixWord ++ tailWord_1861900) baseStart_1861900 baseEnd_1861900 := by
    simpa [prefixWord, tailWord_1861900, baseEnd_1861900] using wordTrace_append hprefix tailTrace_1861900
  have hstable : (prefixWord ++ tailWord_1861900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861900).length < 2 ^ (prefixWord ++ tailWord_1861900).sum := by decide
  have hdescent : baseEnd_1861900 < baseStart_1861900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861914 : List Nat := [3, 1, 1, 3, 4, 1, 1, 7]
def baseStart_1861914 : Nat := 118140960795 + 1861914 * 2 ^ 59
def prefixEnd_1861914 : Nat := 4983230072969 + 3 ^ 40 * 1861914 * 2
def baseEnd_1861914 : Nat := 141638047308967923942551

theorem tailTrace_1861914 : CollatzResearch.WordTrace tailWord_1861914 prefixEnd_1861914 141638047308967923942551 := by
  unfold tailWord_1861914
  simp only [CollatzResearch.WordTrace]
  refine ⟨16977395644152760609966199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45273055051074028293243197 16977395644152760609966199)
  ·
    refine ⟨25466093466229140914949299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16977395644152760609966199 25466093466229140914949299)
    ·
      refine ⟨38199140199343711372423949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25466093466229140914949299 38199140199343711372423949)
      ·
        refine ⟨14324677574753891764658981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38199140199343711372423949 14324677574753891764658981)
        ·
          refine ⟨2685877045266354705873559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14324677574753891764658981 2685877045266354705873559)
          ·
            refine ⟨4028815567899532058810339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2685877045266354705873559 4028815567899532058810339)
            ·
              refine ⟨6043223351849298088215509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4028815567899532058810339 6043223351849298088215509)
              ·
                refine ⟨141638047308967923942551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6043223351849298088215509 141638047308967923942551)
                ·
                  rfl

theorem cell21_1861914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_1861914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861914 prefixEnd_1861914 := by exact prefixLift 1861914
  have htrace : WordTrace (prefixWord ++ tailWord_1861914) baseStart_1861914 baseEnd_1861914 := by
    simpa [prefixWord, tailWord_1861914, baseEnd_1861914] using wordTrace_append hprefix tailTrace_1861914
  have hstable : (prefixWord ++ tailWord_1861914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861914).length < 2 ^ (prefixWord ++ tailWord_1861914).sum := by decide
  have hdescent : baseEnd_1861914 < baseStart_1861914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861945 : List Nat := [1, 2, 1, 6, 1, 1, 3, 1, 5]
def baseStart_1861945 : Nat := 118140960795 + 1861945 * 2 ^ 59
def prefixEnd_1861945 : Nat := 4983230072969 + 3 ^ 40 * 1861945 * 2
def baseEnd_1861945 : Nat := 424921216549254606810923

theorem tailTrace_1861945 : CollatzResearch.WordTrace tailWord_1861945 prefixEnd_1861945 424921216549254606810923 := by
  unfold tailWord_1861945
  simp only [CollatzResearch.WordTrace]
  refine ⟨67910713239498734734243289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45273808826332489822828859 67910713239498734734243289)
  ·
    refine ⟨50933034929624051050682467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67910713239498734734243289 50933034929624051050682467)
    ·
      refine ⟨76399552394436076576023701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50933034929624051050682467 76399552394436076576023701)
      ·
        refine ⟨3581229018489191089501111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76399552394436076576023701 3581229018489191089501111)
        ·
          refine ⟨5371843527733786634251667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3581229018489191089501111 5371843527733786634251667)
          ·
            refine ⟨8057765291600679951377501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5371843527733786634251667 8057765291600679951377501)
            ·
              refine ⟨3021661984350254981766563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8057765291600679951377501 3021661984350254981766563)
              ·
                refine ⟨4532492976525382472649845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3021661984350254981766563 4532492976525382472649845)
                ·
                  refine ⟨424921216549254606810923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4532492976525382472649845 424921216549254606810923)
                  ·
                    rfl

theorem cell21_1861945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_1861945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861945 prefixEnd_1861945 := by exact prefixLift 1861945
  have htrace : WordTrace (prefixWord ++ tailWord_1861945) baseStart_1861945 baseEnd_1861945 := by
    simpa [prefixWord, tailWord_1861945, baseEnd_1861945] using wordTrace_append hprefix tailTrace_1861945
  have hstable : (prefixWord ++ tailWord_1861945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861945).length < 2 ^ (prefixWord ++ tailWord_1861945).sum := by decide
  have hdescent : baseEnd_1861945 < baseStart_1861945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861959 : List Nat := [1, 1, 4, 1, 2, 2, 3, 3, 4]
def baseStart_1861959 : Nat := 118140960795 + 1861959 * 2 ^ 59
def prefixEnd_1861959 : Nat := 4983230072969 + 3 ^ 40 * 1861959 * 2
def baseEnd_1861959 : Nat := 424924411539993693577561

theorem tailTrace_1861959 : CollatzResearch.WordTrace tailWord_1861959 prefixEnd_1861959 424924411539993693577561 := by
  unfold tailWord_1861959
  simp only [CollatzResearch.WordTrace]
  refine ⟨67911223861448015125252931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45274149240965343416835287 67911223861448015125252931)
  ·
    refine ⟨101866835792172022687879397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67911223861448015125252931 101866835792172022687879397)
    ·
      refine ⟨19100031711032254253977387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101866835792172022687879397 19100031711032254253977387)
      ·
        refine ⟨28650047566548381380966081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19100031711032254253977387 28650047566548381380966081)
        ·
          refine ⟨21487535674911286035724561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28650047566548381380966081 21487535674911286035724561)
          ·
            refine ⟨16115651756183464526793421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21487535674911286035724561 16115651756183464526793421)
            ·
              refine ⟨6043369408568799197547533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16115651756183464526793421 6043369408568799197547533)
              ·
                refine ⟨2266263528213299699080325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6043369408568799197547533 2266263528213299699080325)
                ·
                  refine ⟨424924411539993693577561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2266263528213299699080325 424924411539993693577561)
                  ·
                    rfl

theorem cell21_1861959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 4].length) (baseStart_1861959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861959 prefixEnd_1861959 := by exact prefixLift 1861959
  have htrace : WordTrace (prefixWord ++ tailWord_1861959) baseStart_1861959 baseEnd_1861959 := by
    simpa [prefixWord, tailWord_1861959, baseEnd_1861959] using wordTrace_append hprefix tailTrace_1861959
  have hstable : (prefixWord ++ tailWord_1861959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861959).length < 2 ^ (prefixWord ++ tailWord_1861959).sum := by decide
  have hdescent : baseEnd_1861959 < baseStart_1861959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1861996 : List Nat := [2, 2, 1, 1, 7, 1, 2, 2, 3]
def baseStart_1861996 : Nat := 118140960795 + 1861996 * 2 ^ 59
def prefixEnd_1861996 : Nat := 4983230072969 + 3 ^ 40 * 1861996 * 2
def baseEnd_1861996 : Nat := 424932855444089851460819

theorem tailTrace_1861996 : CollatzResearch.WordTrace tailWord_1861996 prefixEnd_1861996 424932855444089851460819 := by
  unfold tailWord_1861996
  simp only [CollatzResearch.WordTrace]
  refine ⟨33956286681156985222174921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45275048908209313629566561 33956286681156985222174921)
  ·
    refine ⟨25467215010867738916631191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33956286681156985222174921 25467215010867738916631191)
    ·
      refine ⟨38200822516301608374946787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25467215010867738916631191 38200822516301608374946787)
      ·
        refine ⟨57301233774452412562420181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38200822516301608374946787 57301233774452412562420181)
        ·
          refine ⟨1342997666588728419431723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 57301233774452412562420181 1342997666588728419431723)
          ·
            refine ⟨2014496499883092629147585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1342997666588728419431723 2014496499883092629147585)
            ·
              refine ⟨1510872374912319471860689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2014496499883092629147585 1510872374912319471860689)
              ·
                refine ⟨1133154281184239603895517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1510872374912319471860689 1133154281184239603895517)
                ·
                  refine ⟨424932855444089851460819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1133154281184239603895517 424932855444089851460819)
                  ·
                    rfl

theorem cell21_1861996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_1861996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1861996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1861996 prefixEnd_1861996 := by exact prefixLift 1861996
  have htrace : WordTrace (prefixWord ++ tailWord_1861996) baseStart_1861996 baseEnd_1861996 := by
    simpa [prefixWord, tailWord_1861996, baseEnd_1861996] using wordTrace_append hprefix tailTrace_1861996
  have hstable : (prefixWord ++ tailWord_1861996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1861996).length < 2 ^ (prefixWord ++ tailWord_1861996).sum := by decide
  have hdescent : baseEnd_1861996 < baseStart_1861996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1861996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862069 : List Nat := [1, 3, 3, 2, 3, 1, 3, 1, 4]
def baseStart_1862069 : Nat := 118140960795 + 1862069 * 2 ^ 59
def prefixEnd_1862069 : Nat := 4983230072969 + 3 ^ 40 * 1862069 * 2
def baseEnd_1862069 : Nat := 424949515038657946744003

theorem tailTrace_1862069 : CollatzResearch.WordTrace tailWord_1862069 prefixEnd_1862069 424949515038657946744003 := by
  unfold tailWord_1862069
  simp only [CollatzResearch.WordTrace]
  refine ⟨67915235891049503911757261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45276823927366335941171507 67915235891049503911757261)
  ·
    refine ⟨25468213459143563966908973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67915235891049503911757261 25468213459143563966908973)
    ·
      refine ⟨9550580047178836487590865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25468213459143563966908973 9550580047178836487590865)
      ·
        refine ⟨7162935035384127365693149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9550580047178836487590865 7162935035384127365693149)
        ·
          refine ⟨2686100638269047762134931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7162935035384127365693149 2686100638269047762134931)
          ·
            refine ⟨4029150957403571643202397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2686100638269047762134931 4029150957403571643202397)
            ·
              refine ⟨1510931609026339366200899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4029150957403571643202397 1510931609026339366200899)
              ·
                refine ⟨2266397413539509049301349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1510931609026339366200899 2266397413539509049301349)
                ·
                  refine ⟨424949515038657946744003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2266397413539509049301349 424949515038657946744003)
                  ·
                    rfl

theorem cell21_1862069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_1862069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1862069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1862069 prefixEnd_1862069 := by exact prefixLift 1862069
  have htrace : WordTrace (prefixWord ++ tailWord_1862069) baseStart_1862069 baseEnd_1862069 := by
    simpa [prefixWord, tailWord_1862069, baseEnd_1862069] using wordTrace_append hprefix tailTrace_1862069
  have hstable : (prefixWord ++ tailWord_1862069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862069).length < 2 ^ (prefixWord ++ tailWord_1862069).sum := by decide
  have hdescent : baseEnd_1862069 < baseStart_1862069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862170 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 6]
def baseStart_1862170 : Nat := 118140960795 + 1862170 * 2 ^ 59
def prefixEnd_1862170 : Nat := 4983230072969 + 3 ^ 40 * 1862170 * 2
def baseEnd_1862170 : Nat := 424972564614704215560463

theorem tailTrace_1862170 : CollatzResearch.WordTrace tailWord_1862170 prefixEnd_1862170 424972564614704215560463 := by
  unfold tailWord_1862170
  simp only [CollatzResearch.WordTrace]
  refine ⟨16979729915920899540295991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45279279775789065440789309 16979729915920899540295991)
  ·
    refine ⟨25469594873881349310443987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16979729915920899540295991 25469594873881349310443987)
    ·
      refine ⟨38204392310822023965665981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25469594873881349310443987 38204392310822023965665981)
      ·
        refine ⟨14326647116558258987124743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38204392310822023965665981 14326647116558258987124743)
        ·
          refine ⟨21489970674837388480687115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14326647116558258987124743 21489970674837388480687115)
          ·
            refine ⟨32234956012256082721030673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21489970674837388480687115 32234956012256082721030673)
            ·
              refine ⟨24176217009192062040773005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32234956012256082721030673 24176217009192062040773005)
              ·
                refine ⟨9066081378447023265289877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24176217009192062040773005 9066081378447023265289877)
                ·
                  refine ⟨424972564614704215560463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9066081378447023265289877 424972564614704215560463)
                  ·
                    rfl

theorem cell21_1862170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_1862170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1862170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1862170 prefixEnd_1862170 := by exact prefixLift 1862170
  have htrace : WordTrace (prefixWord ++ tailWord_1862170) baseStart_1862170 baseEnd_1862170 := by
    simpa [prefixWord, tailWord_1862170, baseEnd_1862170] using wordTrace_append hprefix tailTrace_1862170
  have hstable : (prefixWord ++ tailWord_1862170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862170).length < 2 ^ (prefixWord ++ tailWord_1862170).sum := by decide
  have hdescent : baseEnd_1862170 < baseStart_1862170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862221 : List Nat := [1, 6, 1, 1, 2, 3, 1, 2, 4]
def baseStart_1862221 : Nat := 118140960795 + 1862221 * 2 ^ 59
def prefixEnd_1862221 : Nat := 4983230072969 + 3 ^ 40 * 1862221 * 2
def baseEnd_1862221 : Nat := 424984203509539460210359

theorem tailTrace_1862221 : CollatzResearch.WordTrace tailWord_1862221 prefixEnd_1862221 424984203509539460210359 := by
  unfold tailWord_1862221
  simp only [CollatzResearch.WordTrace]
  refine ⟨67920779786498833871290517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45280519857665889247527011 67920779786498833871290517)
  ·
    refine ⟨3183786552492132837716743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67920779786498833871290517 3183786552492132837716743)
    ·
      refine ⟨4775679828738199256575115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3183786552492132837716743 4775679828738199256575115)
      ·
        refine ⟨7163519743107298884862673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4775679828738199256575115 7163519743107298884862673)
        ·
          refine ⟨5372639807330474163647005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7163519743107298884862673 5372639807330474163647005)
          ·
            refine ⟨2014739927748927811367627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5372639807330474163647005 2014739927748927811367627)
            ·
              refine ⟨3022109891623391717051441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2014739927748927811367627 3022109891623391717051441)
              ·
                refine ⟨2266582418717543787788581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3022109891623391717051441 2266582418717543787788581)
                ·
                  refine ⟨424984203509539460210359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2266582418717543787788581 424984203509539460210359)
                  ·
                    rfl

theorem cell21_1862221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_1862221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1862221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1862221 prefixEnd_1862221 := by exact prefixLift 1862221
  have htrace : WordTrace (prefixWord ++ tailWord_1862221) baseStart_1862221 baseEnd_1862221 := by
    simpa [prefixWord, tailWord_1862221, baseEnd_1862221] using wordTrace_append hprefix tailTrace_1862221
  have hstable : (prefixWord ++ tailWord_1862221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862221).length < 2 ^ (prefixWord ++ tailWord_1862221).sum := by decide
  have hdescent : baseEnd_1862221 < baseStart_1862221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862277 : List Nat := [1, 3, 1, 1, 4, 4, 7]
def baseStart_1862277 : Nat := 118140960795 + 1862277 * 2 ^ 59
def prefixEnd_1862277 : Nat := 4983230072969 + 3 ^ 40 * 1862277 * 2
def baseEnd_1862277 : Nat := 47221887052499534141879

theorem tailTrace_1862277 : CollatzResearch.WordTrace tailWord_1862277 prefixEnd_1862277 47221887052499534141879 := by
  unfold tailWord_1862277
  simp only [CollatzResearch.WordTrace]
  refine ⟨67922822274295955435329085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45281881516197303623552723 67922822274295955435329085)
  ·
    refine ⟨25471058352860983288248407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67922822274295955435329085 25471058352860983288248407)
    ·
      refine ⟨38206587529291474932372611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25471058352860983288248407 38206587529291474932372611)
      ·
        refine ⟨57309881293937212398558917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38206587529291474932372611 57309881293937212398558917)
        ·
          refine ⟨10745602742613227324729797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57309881293937212398558917 10745602742613227324729797)
          ·
            refine ⟨2014800514239980123386837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10745602742613227324729797 2014800514239980123386837)
            ·
              refine ⟨47221887052499534141879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2014800514239980123386837 47221887052499534141879)
              ·
                rfl

theorem cell21_1862277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 7].length) (baseStart_1862277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1862277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1862277 prefixEnd_1862277 := by exact prefixLift 1862277
  have htrace : WordTrace (prefixWord ++ tailWord_1862277) baseStart_1862277 baseEnd_1862277 := by
    simpa [prefixWord, tailWord_1862277, baseEnd_1862277] using wordTrace_append hprefix tailTrace_1862277
  have hstable : (prefixWord ++ tailWord_1862277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862277).length < 2 ^ (prefixWord ++ tailWord_1862277).sum := by decide
  have hdescent : baseEnd_1862277 < baseStart_1862277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862336 : List Nat := [2, 1, 1, 2, 4, 11]
def baseStart_1862336 : Nat := 118140960795 + 1862336 * 2 ^ 59
def prefixEnd_1862336 : Nat := 4983230072969 + 3 ^ 40 * 1862336 * 2
def baseEnd_1862336 : Nat := 15741127706530548733091

theorem tailTrace_1862336 : CollatzResearch.WordTrace tailWord_1862336 prefixEnd_1862336 15741127706530548733091 := by
  unfold tailWord_1862336
  simp only [CollatzResearch.WordTrace]
  refine ⟨33962487090541104255863431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45283316120721472341151241 33962487090541104255863431)
  ·
    refine ⟨50943730635811656383795147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33962487090541104255863431 50943730635811656383795147)
    ·
      refine ⟨76415595953717484575692721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50943730635811656383795147 76415595953717484575692721)
      ·
        refine ⟨57311696965288113431769541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76415595953717484575692721 57311696965288113431769541)
        ·
          refine ⟨10745943180991521268456789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57311696965288113431769541 10745943180991521268456789)
          ·
            refine ⟨15741127706530548733091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10745943180991521268456789 15741127706530548733091)
            ·
              rfl

theorem cell21_1862336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 11].length) (baseStart_1862336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1862336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1862336 prefixEnd_1862336 := by exact prefixLift 1862336
  have htrace : WordTrace (prefixWord ++ tailWord_1862336) baseStart_1862336 baseEnd_1862336 := by
    simpa [prefixWord, tailWord_1862336, baseEnd_1862336] using wordTrace_append hprefix tailTrace_1862336
  have hstable : (prefixWord ++ tailWord_1862336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862336).length < 2 ^ (prefixWord ++ tailWord_1862336).sum := by decide
  have hdescent : baseEnd_1862336 < baseStart_1862336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862367 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 7]
def baseStart_1862367 : Nat := 118140960795 + 1862367 * 2 ^ 59
def prefixEnd_1862367 : Nat := 4983230072969 + 3 ^ 40 * 1862367 * 2
def baseEnd_1862367 : Nat := 425017522698675650776727

theorem tailTrace_1862367 : CollatzResearch.WordTrace tailWord_1862367 prefixEnd_1862367 425017522698675650776727 := by
  unfold tailWord_1862367
  simp only [CollatzResearch.WordTrace]
  refine ⟨67926104843969900806105355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45284069895979933870736903 67926104843969900806105355)
  ·
    refine ⟨101889157265954851209158033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67926104843969900806105355 101889157265954851209158033)
    ·
      refine ⟨76416867949466138406868525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101889157265954851209158033 76416867949466138406868525)
      ·
        refine ⟨28656325481049801902575697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76416867949466138406868525 28656325481049801902575697)
        ·
          refine ⟨21492244110787351426931773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28656325481049801902575697 21492244110787351426931773)
          ·
            refine ⟨8059591541545256785099415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21492244110787351426931773 8059591541545256785099415)
            ·
              refine ⟨12089387312317885177649123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8059591541545256785099415 12089387312317885177649123)
              ·
                refine ⟨18134080968476827766473685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12089387312317885177649123 18134080968476827766473685)
                ·
                  refine ⟨425017522698675650776727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18134080968476827766473685 425017522698675650776727)
                  ·
                    rfl

theorem cell21_1862367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 7].length) (baseStart_1862367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1862367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1862367 prefixEnd_1862367 := by exact prefixLift 1862367
  have htrace : WordTrace (prefixWord ++ tailWord_1862367) baseStart_1862367 baseEnd_1862367 := by
    simpa [prefixWord, tailWord_1862367, baseEnd_1862367] using wordTrace_append hprefix tailTrace_1862367
  have hstable : (prefixWord ++ tailWord_1862367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862367).length < 2 ^ (prefixWord ++ tailWord_1862367).sum := by decide
  have hdescent : baseEnd_1862367 < baseStart_1862367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862412 : List Nat := [2, 2, 1, 2, 2, 1, 1, 10]
def baseStart_1862412 : Nat := 118140960795 + 1862412 * 2 ^ 59
def prefixEnd_1862412 : Nat := 4983230072969 + 3 ^ 40 * 1862412 * 2
def baseEnd_1862412 : Nat := 141675930770588524175545

theorem tailTrace_1862412 : CollatzResearch.WordTrace tailWord_1862412 prefixEnd_1862412 141675930770588524175545 := by
  unfold tailWord_1862412
  simp only [CollatzResearch.WordTrace]
  refine ⟨33963873064403436745746745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45285164085871248994328993 33963873064403436745746745)
  ·
    refine ⟨25472904798302577559310059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33963873064403436745746745 25472904798302577559310059)
    ·
      refine ⟨38209357197453866338965089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25472904798302577559310059 38209357197453866338965089)
      ·
        refine ⟨28657017898090399754223817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38209357197453866338965089 28657017898090399754223817)
        ·
          refine ⟨21492763423567799815667863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28657017898090399754223817 21492763423567799815667863)
          ·
            refine ⟨32239145135351699723501795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21492763423567799815667863 32239145135351699723501795)
            ·
              refine ⟨48358717703027549585252693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32239145135351699723501795 48358717703027549585252693)
              ·
                refine ⟨141675930770588524175545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48358717703027549585252693 141675930770588524175545)
                ·
                  rfl

theorem cell21_1862412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 10].length) (baseStart_1862412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1862412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1862412 prefixEnd_1862412 := by exact prefixLift 1862412
  have htrace : WordTrace (prefixWord ++ tailWord_1862412) baseStart_1862412 baseEnd_1862412 := by
    simpa [prefixWord, tailWord_1862412, baseEnd_1862412] using wordTrace_append hprefix tailTrace_1862412
  have hstable : (prefixWord ++ tailWord_1862412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862412).length < 2 ^ (prefixWord ++ tailWord_1862412).sum := by decide
  have hdescent : baseEnd_1862412 < baseStart_1862412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862415 : List Nat := [1, 1, 2, 1, 1, 1, 9, 1, 4]
def baseStart_1862415 : Nat := 118140960795 + 1862415 * 2 ^ 59
def prefixEnd_1862415 : Nat := 4983230072969 + 3 ^ 40 * 1862415 * 2
def baseEnd_1862415 : Nat := 425028476952638233976629

theorem tailTrace_1862415 : CollatzResearch.WordTrace tailWord_1862415 prefixEnd_1862415 425028476952638233976629 := by
  unfold tailWord_1862415
  simp only [CollatzResearch.WordTrace]
  refine ⟨67927855547796005003852699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45285237031864003335901799 67927855547796005003852699)
  ·
    refine ⟨101891783321694007505779049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67927855547796005003852699 101891783321694007505779049)
    ·
      refine ⟨76418837491270505629334287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101891783321694007505779049 76418837491270505629334287)
      ·
        refine ⟨114628256236905758444001431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76418837491270505629334287 114628256236905758444001431)
        ·
          refine ⟨171942384355358637666002147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114628256236905758444001431 171942384355358637666002147)
          ·
            refine ⟨257913576533037956499003221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171942384355358637666002147 257913576533037956499003221)
            ·
              refine ⟨1511212362498269276361347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 257913576533037956499003221 1511212362498269276361347)
              ·
                refine ⟨2266818543747403914542021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511212362498269276361347 2266818543747403914542021)
                ·
                  refine ⟨425028476952638233976629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2266818543747403914542021 425028476952638233976629)
                  ·
                    rfl

theorem cell21_1862415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 4].length) (baseStart_1862415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1862415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1862415 prefixEnd_1862415 := by exact prefixLift 1862415
  have htrace : WordTrace (prefixWord ++ tailWord_1862415) baseStart_1862415 baseEnd_1862415 := by
    simpa [prefixWord, tailWord_1862415, baseEnd_1862415] using wordTrace_append hprefix tailTrace_1862415
  have hstable : (prefixWord ++ tailWord_1862415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862415).length < 2 ^ (prefixWord ++ tailWord_1862415).sum := by decide
  have hdescent : baseEnd_1862415 < baseStart_1862415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862446 : List Nat := [4, 1, 3, 2, 1, 3, 7]
def baseStart_1862446 : Nat := 118140960795 + 1862446 * 2 ^ 59
def prefixEnd_1862446 : Nat := 4983230072969 + 3 ^ 40 * 1862446 * 2
def baseEnd_1862446 : Nat := 47226172397221007662211

theorem tailTrace_1862446 : CollatzResearch.WordTrace tailWord_1862446 prefixEnd_1862446 47226172397221007662211 := by
  unfold tailWord_1862446
  simp only [CollatzResearch.WordTrace]
  refine ⟨8491123276335462162278899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45285990807122464865487461 8491123276335462162278899)
  ·
    refine ⟨12736684914503193243418349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8491123276335462162278899 12736684914503193243418349)
    ·
      refine ⟨4776256842938697466281881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12736684914503193243418349 4776256842938697466281881)
      ·
        refine ⟨3582192632204023099711411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4776256842938697466281881 3582192632204023099711411)
        ·
          refine ⟨5373288948306034649567117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3582192632204023099711411 5373288948306034649567117)
          ·
            refine ⟨2014983355614762993587669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5373288948306034649567117 2014983355614762993587669)
            ·
              refine ⟨47226172397221007662211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2014983355614762993587669 47226172397221007662211)
              ·
                rfl

theorem cell21_1862446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 7].length) (baseStart_1862446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1862446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1862446 prefixEnd_1862446 := by exact prefixLift 1862446
  have htrace : WordTrace (prefixWord ++ tailWord_1862446) baseStart_1862446 baseEnd_1862446 := by
    simpa [prefixWord, tailWord_1862446, baseEnd_1862446] using wordTrace_append hprefix tailTrace_1862446
  have hstable : (prefixWord ++ tailWord_1862446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862446).length < 2 ^ (prefixWord ++ tailWord_1862446).sum := by decide
  have hdescent : baseEnd_1862446 < baseStart_1862446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862536 : List Nat := [2, 1, 3, 3, 2, 2, 1, 2, 5]
def baseStart_1862536 : Nat := 118140960795 + 1862536 * 2 ^ 59
def prefixEnd_1862536 : Nat := 4983230072969 + 3 ^ 40 * 1862536 * 2
def baseEnd_1862536 : Nat := 425056090801168912459715

theorem tailTrace_1862536 : CollatzResearch.WordTrace tailWord_1862536 prefixEnd_1862536 425056090801168912459715 := by
  unfold tailWord_1862536
  simp only [CollatzResearch.WordTrace]
  refine ⟨33966134390178821334503731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45288179186905095112671641 33966134390178821334503731)
  ·
    refine ⟨50949201585268232001755597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33966134390178821334503731 50949201585268232001755597)
    ·
      refine ⟨19105950594475587000658349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50949201585268232001755597 19105950594475587000658349)
      ·
        refine ⟨7164731472928345125246881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19105950594475587000658349 7164731472928345125246881)
        ·
          refine ⟨5373548604696258843935161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7164731472928345125246881 5373548604696258843935161)
          ·
            refine ⟨4030161453522194132951371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5373548604696258843935161 4030161453522194132951371)
            ·
              refine ⟨6045242180283291199427057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4030161453522194132951371 6045242180283291199427057)
              ·
                refine ⟨4533931635212468399570293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6045242180283291199427057 4533931635212468399570293)
                ·
                  refine ⟨425056090801168912459715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4533931635212468399570293 425056090801168912459715)
                  ·
                    rfl

theorem cell21_1862536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_1862536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1862536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1862536 prefixEnd_1862536 := by exact prefixLift 1862536
  have htrace : WordTrace (prefixWord ++ tailWord_1862536) baseStart_1862536 baseEnd_1862536 := by
    simpa [prefixWord, tailWord_1862536, baseEnd_1862536] using wordTrace_append hprefix tailTrace_1862536
  have hstable : (prefixWord ++ tailWord_1862536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862536).length < 2 ^ (prefixWord ++ tailWord_1862536).sum := by decide
  have hdescent : baseEnd_1862536 < baseStart_1862536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862564 : List Nat := [2, 3, 1, 2, 1, 2, 10]
def baseStart_1862564 : Nat := 118140960795 + 1862564 * 2 ^ 59
def prefixEnd_1862564 : Nat := 4983230072969 + 3 ^ 40 * 1862564 * 2
def baseEnd_1862564 : Nat := 47229164531405231776999

theorem tailTrace_1862564 : CollatzResearch.WordTrace tailWord_1862564 prefixEnd_1862564 47229164531405231776999 := by
  unfold tailWord_1862564
  simp only [CollatzResearch.WordTrace]
  refine ⟨33966645012128101725513373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45288860016170802300684497 33966645012128101725513373)
  ·
    refine ⟨12737491879548038147067515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33966645012128101725513373 12737491879548038147067515)
    ·
      refine ⟨19106237819322057220601273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12737491879548038147067515 19106237819322057220601273)
      ·
        refine ⟨14329678364491542915450955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19106237819322057220601273 14329678364491542915450955)
        ·
          refine ⟨21494517546737314373176433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14329678364491542915450955 21494517546737314373176433)
          ·
            refine ⟨16120888160052985779882325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21494517546737314373176433 16120888160052985779882325)
            ·
              refine ⟨47229164531405231776999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16120888160052985779882325 47229164531405231776999)
              ·
                rfl

theorem cell21_1862564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 10].length) (baseStart_1862564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1862564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1862564 prefixEnd_1862564 := by exact prefixLift 1862564
  have htrace : WordTrace (prefixWord ++ tailWord_1862564) baseStart_1862564 baseEnd_1862564 := by
    simpa [prefixWord, tailWord_1862564, baseEnd_1862564] using wordTrace_append hprefix tailTrace_1862564
  have hstable : (prefixWord ++ tailWord_1862564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862564).length < 2 ^ (prefixWord ++ tailWord_1862564).sum := by decide
  have hdescent : baseEnd_1862564 < baseStart_1862564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862567 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 6]
def baseStart_1862567 : Nat := 118140960795 + 1862567 * 2 ^ 59
def prefixEnd_1862567 : Nat := 4983230072969 + 3 ^ 40 * 1862567 * 2
def baseEnd_1862567 : Nat := 425063165423519747442985

theorem tailTrace_1862567 : CollatzResearch.WordTrace tailWord_1862567 prefixEnd_1862567 425063165423519747442985 := by
  unfold tailWord_1862567
  simp only [CollatzResearch.WordTrace]
  refine ⟨67933399443245334963385955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45288932962163556642257303 67933399443245334963385955)
  ·
    refine ⟨101900099164868002445078933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67933399443245334963385955 101900099164868002445078933)
    ·
      refine ⟨4776567148353187614613075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 101900099164868002445078933 4776567148353187614613075)
      ·
        refine ⟨7164850722529781421919613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4776567148353187614613075 7164850722529781421919613)
        ·
          refine ⟨2686819020948668033219855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7164850722529781421919613 2686819020948668033219855)
          ·
            refine ⟨4030228531423002049829783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2686819020948668033219855 4030228531423002049829783)
            ·
              refine ⟨6045342797134503074744675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4030228531423002049829783 6045342797134503074744675)
              ·
                refine ⟨9068014195701754612117013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6045342797134503074744675 9068014195701754612117013)
                ·
                  refine ⟨425063165423519747442985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9068014195701754612117013 425063165423519747442985)
                  ·
                    rfl

theorem cell21_1862567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 6].length) (baseStart_1862567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1862567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1862567 prefixEnd_1862567 := by exact prefixLift 1862567
  have htrace : WordTrace (prefixWord ++ tailWord_1862567) baseStart_1862567 baseEnd_1862567 := by
    simpa [prefixWord, tailWord_1862567, baseEnd_1862567] using wordTrace_append hprefix tailTrace_1862567
  have hstable : (prefixWord ++ tailWord_1862567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862567).length < 2 ^ (prefixWord ++ tailWord_1862567).sum := by decide
  have hdescent : baseEnd_1862567 < baseStart_1862567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862609 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 8]
def baseStart_1862609 : Nat := 118140960795 + 1862609 * 2 ^ 59
def prefixEnd_1862609 : Nat := 4983230072969 + 3 ^ 40 * 1862609 * 2
def baseEnd_1862609 : Nat := 425072750395737007742899

theorem tailTrace_1862609 : CollatzResearch.WordTrace tailWord_1862609 prefixEnd_1862609 425072750395737007742899 := by
  unfold tailWord_1862609
  simp only [CollatzResearch.WordTrace]
  refine ⟨67934931309093176136414881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45289954206062117424276587 67934931309093176136414881)
  ·
    refine ⟨50951198481819882102311161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67934931309093176136414881 50951198481819882102311161)
    ·
      refine ⟨38213398861364911576733371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50951198481819882102311161 38213398861364911576733371)
      ·
        refine ⟨57320098292047367365100057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38213398861364911576733371 57320098292047367365100057)
        ·
          refine ⟨42990073719035525523825043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57320098292047367365100057 42990073719035525523825043)
          ·
            refine ⟨64485110578553288285737565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42990073719035525523825043 64485110578553288285737565)
            ·
              refine ⟨24181916466957483107151587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64485110578553288285737565 24181916466957483107151587)
              ·
                refine ⟨36272874700436224660727381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24181916466957483107151587 36272874700436224660727381)
                ·
                  refine ⟨425072750395737007742899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36272874700436224660727381 425072750395737007742899)
                  ·
                    rfl

theorem cell21_1862609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_1862609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1862609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1862609 prefixEnd_1862609 := by exact prefixLift 1862609
  have htrace : WordTrace (prefixWord ++ tailWord_1862609) baseStart_1862609 baseEnd_1862609 := by
    simpa [prefixWord, tailWord_1862609, baseEnd_1862609] using wordTrace_append hprefix tailTrace_1862609
  have hstable : (prefixWord ++ tailWord_1862609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862609).length < 2 ^ (prefixWord ++ tailWord_1862609).sum := by decide
  have hdescent : baseEnd_1862609 < baseStart_1862609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862674 : List Nat := [3, 2, 5, 1, 10]
def baseStart_1862674 : Nat := 118140960795 + 1862674 * 2 ^ 59
def prefixEnd_1862674 : Nat := 4983230072969 + 3 ^ 40 * 1862674 * 2
def baseEnd_1862674 : Nat := 5247994867670510359993

theorem tailTrace_1862674 : CollatzResearch.WordTrace tailWord_1862674 prefixEnd_1862674 5247994867670510359993 := by
  unfold tailWord_1862674
  simp only [CollatzResearch.WordTrace]
  refine ⟨16984325513464423059382769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45291534702571794825020717 16984325513464423059382769)
  ·
    refine ⟨12738244135098317294537077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16984325513464423059382769 12738244135098317294537077)
    ·
      refine ⟨1194210387665467246362851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12738244135098317294537077 1194210387665467246362851)
      ·
        refine ⟨1791315581498200869544277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1194210387665467246362851 1791315581498200869544277)
        ·
          refine ⟨5247994867670510359993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1791315581498200869544277 5247994867670510359993)
          ·
            rfl

theorem cell21_1862674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 10].length) (baseStart_1862674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1862674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1862674 prefixEnd_1862674 := by exact prefixLift 1862674
  have htrace : WordTrace (prefixWord ++ tailWord_1862674) baseStart_1862674 baseEnd_1862674 := by
    simpa [prefixWord, tailWord_1862674, baseEnd_1862674] using wordTrace_append hprefix tailTrace_1862674
  have hstable : (prefixWord ++ tailWord_1862674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862674).length < 2 ^ (prefixWord ++ tailWord_1862674).sum := by decide
  have hdescent : baseEnd_1862674 < baseStart_1862674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862733 : List Nat := [1, 6, 1, 1, 1, 3, 8]
def baseStart_1862733 : Nat := 118140960795 + 1862733 * 2 ^ 59
def prefixEnd_1862733 : Nat := 4983230072969 + 3 ^ 40 * 1862733 * 2
def baseEnd_1862733 : Nat := 47233449876126705297331

theorem tailTrace_1862733 : CollatzResearch.WordTrace tailWord_1862733 prefixEnd_1862733 47233449876126705297331 := by
  unfold tailWord_1862733
  simp only [CollatzResearch.WordTrace]
  refine ⟨67939453960643945313928853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45292969307095963542619235 67939453960643945313928853)
  ·
    refine ⟨3184661904405184936590415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67939453960643945313928853 3184661904405184936590415)
    ·
      refine ⟨4776992856607777404885623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3184661904405184936590415 4776992856607777404885623)
      ·
        refine ⟨7165489284911666107328435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4776992856607777404885623 7165489284911666107328435)
        ·
          refine ⟨10748233927367499160992653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7165489284911666107328435 10748233927367499160992653)
          ·
            refine ⟨4030587722762812185372245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10748233927367499160992653 4030587722762812185372245)
            ·
              refine ⟨47233449876126705297331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4030587722762812185372245 47233449876126705297331)
              ·
                rfl

theorem cell21_1862733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 8].length) (baseStart_1862733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1862733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1862733 prefixEnd_1862733 := by exact prefixLift 1862733
  have htrace : WordTrace (prefixWord ++ tailWord_1862733) baseStart_1862733 baseEnd_1862733 := by
    simpa [prefixWord, tailWord_1862733, baseEnd_1862733] using wordTrace_append hprefix tailTrace_1862733
  have hstable : (prefixWord ++ tailWord_1862733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862733).length < 2 ^ (prefixWord ++ tailWord_1862733).sum := by decide
  have hdescent : baseEnd_1862733 < baseStart_1862733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862798 : List Nat := [4, 1, 1, 3, 2, 2, 3, 2, 3]
def baseStart_1862798 : Nat := 118140960795 + 1862798 * 2 ^ 59
def prefixEnd_1862798 : Nat := 4983230072969 + 3 ^ 40 * 1862798 * 2
def baseEnd_1862798 : Nat := 425115882770714679092513

theorem tailTrace_1862798 : CollatzResearch.WordTrace tailWord_1862798 prefixEnd_1862798 425115882770714679092513 := by
  unfold tailWord_1862798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8492728088176057676880631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45294549803605640943363365 8492728088176057676880631)
  ·
    refine ⟨12739092132264086515320947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8492728088176057676880631 12739092132264086515320947)
    ·
      refine ⟨19108638198396129772981421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12739092132264086515320947 19108638198396129772981421)
      ·
        refine ⟨7165739324398548664868033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19108638198396129772981421 7165739324398548664868033)
        ·
          refine ⟨5374304493298911498651025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7165739324398548664868033 5374304493298911498651025)
          ·
            refine ⟨4030728369974183623988269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5374304493298911498651025 4030728369974183623988269)
            ·
              refine ⟨1511523138740318858995601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4030728369974183623988269 1511523138740318858995601)
              ·
                refine ⟨1133642354055239144246701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1511523138740318858995601 1133642354055239144246701)
                ·
                  refine ⟨425115882770714679092513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1133642354055239144246701 425115882770714679092513)
                  ·
                    rfl

theorem cell21_1862798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_1862798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1862798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1862798 prefixEnd_1862798 := by exact prefixLift 1862798
  have htrace : WordTrace (prefixWord ++ tailWord_1862798) baseStart_1862798 baseEnd_1862798 := by
    simpa [prefixWord, tailWord_1862798, baseEnd_1862798] using wordTrace_append hprefix tailTrace_1862798
  have hstable : (prefixWord ++ tailWord_1862798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862798).length < 2 ^ (prefixWord ++ tailWord_1862798).sum := by decide
  have hdescent : baseEnd_1862798 < baseStart_1862798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862812 : List Nat := [2, 2, 3, 2, 1, 4, 2, 1, 4]
def baseStart_1862812 : Nat := 118140960795 + 1862812 * 2 ^ 59
def prefixEnd_1862812 : Nat := 4983230072969 + 3 ^ 40 * 1862812 * 2
def baseEnd_1862812 : Nat := 425119077761453765859151

theorem tailTrace_1862812 : CollatzResearch.WordTrace tailWord_1862812 prefixEnd_1862812 425119077761453765859151 := by
  unfold tailWord_1862812
  simp only [CollatzResearch.WordTrace]
  refine ⟨33971167663678870903027345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45294890218238494537369793 33971167663678870903027345)
  ·
    refine ⟨25478375747759153177270509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33971167663678870903027345 25478375747759153177270509)
    ·
      refine ⟨9554390905409682441476441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25478375747759153177270509 9554390905409682441476441)
      ·
        refine ⟨7165793179057261831107331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9554390905409682441476441 7165793179057261831107331)
        ·
          refine ⟨10748689768585892746660997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7165793179057261831107331 10748689768585892746660997)
          ·
            refine ⟨2015379331609854889998937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10748689768585892746660997 2015379331609854889998937)
            ·
              refine ⟨1511534498707391167499203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2015379331609854889998937 1511534498707391167499203)
              ·
                refine ⟨2267301748061086751248805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1511534498707391167499203 2267301748061086751248805)
                ·
                  refine ⟨425119077761453765859151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2267301748061086751248805 425119077761453765859151)
                  ·
                    rfl

theorem cell21_1862812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_1862812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1862812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1862812 prefixEnd_1862812 := by exact prefixLift 1862812
  have htrace : WordTrace (prefixWord ++ tailWord_1862812) baseStart_1862812 baseEnd_1862812 := by
    simpa [prefixWord, tailWord_1862812, baseEnd_1862812] using wordTrace_append hprefix tailTrace_1862812
  have hstable : (prefixWord ++ tailWord_1862812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862812).length < 2 ^ (prefixWord ++ tailWord_1862812).sum := by decide
  have hdescent : baseEnd_1862812 < baseStart_1862812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862916 : List Nat := [2, 3, 2, 2, 2, 2, 2, 1, 5]
def baseStart_1862916 : Nat := 118140960795 + 1862916 * 2 ^ 59
def prefixEnd_1862916 : Nat := 4983230072969 + 3 ^ 40 * 1862916 * 2
def baseEnd_1862916 : Nat := 425142811978372696125605

theorem tailTrace_1862916 : CollatzResearch.WordTrace tailWord_1862916 prefixEnd_1862916 425142811978372696125605 := by
  unfold tailWord_1862916
  simp only [CollatzResearch.WordTrace]
  refine ⟨33973064259490483783920301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45297419012653978378560401 33973064259490483783920301)
  ·
    refine ⟨12739899097308931418970113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33973064259490483783920301 12739899097308931418970113)
    ·
      refine ⟨9554924322981698564227585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12739899097308931418970113 9554924322981698564227585)
      ·
        refine ⟨7166193242236273923170689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9554924322981698564227585 7166193242236273923170689)
        ·
          refine ⟨5374644931677205442378017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7166193242236273923170689 5374644931677205442378017)
          ·
            refine ⟨4030983698757904081783513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5374644931677205442378017 4030983698757904081783513)
            ·
              refine ⟨3023237774068428061337635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4030983698757904081783513 3023237774068428061337635)
              ·
                refine ⟨4534856661102642092006453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3023237774068428061337635 4534856661102642092006453)
                ·
                  refine ⟨425142811978372696125605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4534856661102642092006453 425142811978372696125605)
                  ·
                    rfl

theorem cell21_1862916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_1862916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1862916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1862916 prefixEnd_1862916 := by exact prefixLift 1862916
  have htrace : WordTrace (prefixWord ++ tailWord_1862916) baseStart_1862916 baseEnd_1862916 := by
    simpa [prefixWord, tailWord_1862916, baseEnd_1862916] using wordTrace_append hprefix tailTrace_1862916
  have hstable : (prefixWord ++ tailWord_1862916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862916).length < 2 ^ (prefixWord ++ tailWord_1862916).sum := by decide
  have hdescent : baseEnd_1862916 < baseStart_1862916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1862975 : List Nat := [1, 1, 2, 2, 4, 2, 3, 1, 5]
def baseStart_1862975 : Nat := 118140960795 + 1862975 * 2 ^ 59
def prefixEnd_1862975 : Nat := 4983230072969 + 3 ^ 40 * 1862975 * 2
def baseEnd_1862975 : Nat := 425156276582201704642151

theorem tailTrace_1862975 : CollatzResearch.WordTrace tailWord_1862975 prefixEnd_1862975 425156276582201704642151 := by
  unfold tailWord_1862975
  simp only [CollatzResearch.WordTrace]
  refine ⟨67948280425767220644238379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45298853617178147096158919 67948280425767220644238379)
  ·
    refine ⟨101922420638650830966357569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67948280425767220644238379 101922420638650830966357569)
    ·
      refine ⟨76441815478988123224768177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101922420638650830966357569 76441815478988123224768177)
      ·
        refine ⟨57331361609241092418576133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76441815478988123224768177 57331361609241092418576133)
        ·
          refine ⟨10749630301732704828483025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57331361609241092418576133 10749630301732704828483025)
          ·
            refine ⟨8062222726299528621362269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10749630301732704828483025 8062222726299528621362269)
            ·
              refine ⟨3023333522362323233010851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8062222726299528621362269 3023333522362323233010851)
              ·
                refine ⟨4535000283543484849516277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3023333522362323233010851 4535000283543484849516277)
                ·
                  refine ⟨425156276582201704642151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4535000283543484849516277 425156276582201704642151)
                  ·
                    rfl

theorem cell21_1862975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 5].length) (baseStart_1862975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1862975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1862975 prefixEnd_1862975 := by exact prefixLift 1862975
  have htrace : WordTrace (prefixWord ++ tailWord_1862975) baseStart_1862975 baseEnd_1862975 := by
    simpa [prefixWord, tailWord_1862975, baseEnd_1862975] using wordTrace_append hprefix tailTrace_1862975
  have hstable : (prefixWord ++ tailWord_1862975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1862975).length < 2 ^ (prefixWord ++ tailWord_1862975).sum := by decide
  have hdescent : baseEnd_1862975 < baseStart_1862975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1862975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863054 : List Nat := [4, 1, 1, 4, 2, 1, 3, 5]
def baseStart_1863054 : Nat := 118140960795 + 1863054 * 2 ^ 59
def prefixEnd_1863054 : Nat := 4983230072969 + 3 ^ 40 * 1863054 * 2
def baseEnd_1863054 : Nat := 141724768486171707608441

theorem tailTrace_1863054 : CollatzResearch.WordTrace tailWord_1863054 prefixEnd_1863054 141724768486171707608441 := by
  unfold tailWord_1863054
  simp only [CollatzResearch.WordTrace]
  refine ⟨8493895224060127142045527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45300774528320678090909477 8493895224060127142045527)
  ·
    refine ⟨12740842836090190713068291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8493895224060127142045527 12740842836090190713068291)
    ·
      refine ⟨19111264254135286069602437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12740842836090190713068291 19111264254135286069602437)
      ·
        refine ⟨3583362047650366138050457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19111264254135286069602437 3583362047650366138050457)
        ·
          refine ⟨2687521535737774603537843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3583362047650366138050457 2687521535737774603537843)
          ·
            refine ⟨4031282303606661905306765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2687521535737774603537843 4031282303606661905306765)
            ·
              refine ⟨1511730863852498214490037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4031282303606661905306765 1511730863852498214490037)
              ·
                refine ⟨141724768486171707608441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1511730863852498214490037 141724768486171707608441)
                ·
                  rfl

theorem cell21_1863054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_1863054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1863054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1863054 prefixEnd_1863054 := by exact prefixLift 1863054
  have htrace : WordTrace (prefixWord ++ tailWord_1863054) baseStart_1863054 baseEnd_1863054 := by
    simpa [prefixWord, tailWord_1863054, baseEnd_1863054] using wordTrace_append hprefix tailTrace_1863054
  have hstable : (prefixWord ++ tailWord_1863054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863054).length < 2 ^ (prefixWord ++ tailWord_1863054).sum := by decide
  have hdescent : baseEnd_1863054 < baseStart_1863054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863085 : List Nat := [1, 5, 2, 2, 1, 1, 2, 4, 3]
def baseStart_1863085 : Nat := 118140960795 + 1863085 * 2 ^ 59
def prefixEnd_1863085 : Nat := 4983230072969 + 3 ^ 40 * 1863085 * 2
def baseEnd_1863085 : Nat := 425181380080865957808593

theorem tailTrace_1863085 : CollatzResearch.WordTrace tailWord_1863085 prefixEnd_1863085 425181380080865957808593 := by
  unfold tailWord_1863085
  simp only [CollatzResearch.WordTrace]
  refine ⟨67952292455368709430742709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45301528303579139620495139 67952292455368709430742709)
  ·
    refine ⟨6370527417690816509132129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67952292455368709430742709 6370527417690816509132129)
    ·
      refine ⟨4777895563268112381849097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6370527417690816509132129 4777895563268112381849097)
      ·
        refine ⟨3583421672451084286386823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4777895563268112381849097 3583421672451084286386823)
        ·
          refine ⟨5375132508676626429580235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3583421672451084286386823 5375132508676626429580235)
          ·
            refine ⟨8062698763014939644370353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5375132508676626429580235 8062698763014939644370353)
            ·
              refine ⟨6047024072261204733277765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8062698763014939644370353 6047024072261204733277765)
              ·
                refine ⟨1133817013548975887489581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6047024072261204733277765 1133817013548975887489581)
                ·
                  refine ⟨425181380080865957808593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1133817013548975887489581 425181380080865957808593)
                  ·
                    rfl

theorem cell21_1863085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_1863085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1863085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1863085 prefixEnd_1863085 := by exact prefixLift 1863085
  have htrace : WordTrace (prefixWord ++ tailWord_1863085) baseStart_1863085 baseEnd_1863085 := by
    simpa [prefixWord, tailWord_1863085, baseEnd_1863085] using wordTrace_append hprefix tailTrace_1863085
  have hstable : (prefixWord ++ tailWord_1863085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863085).length < 2 ^ (prefixWord ++ tailWord_1863085).sum := by decide
  have hdescent : baseEnd_1863085 < baseStart_1863085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863254 : List Nat := [5, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_1863254 : Nat := 118140960795 + 1863254 * 2 ^ 59
def prefixEnd_1863254 : Nat := 4983230072969 + 3 ^ 40 * 1863254 * 2
def baseEnd_1863254 : Nat := 425219948183359219491581

theorem tailTrace_1863254 : CollatzResearch.WordTrace tailWord_1863254 prefixEnd_1863254 425219948183359219491581 := by
  unfold tailWord_1863254
  simp only [CollatzResearch.WordTrace]
  refine ⟨4247403524484778205852801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45305637594504300862429877 4247403524484778205852801)
  ·
    refine ⟨3185552643363583654389601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4247403524484778205852801 3185552643363583654389601)
    ·
      refine ⟨2389164482522687740792201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3185552643363583654389601 2389164482522687740792201)
      ·
        refine ⟨1791873361892015805594151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2389164482522687740792201 1791873361892015805594151)
        ·
          refine ⟨2687810042838023708391227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1791873361892015805594151 2687810042838023708391227)
          ·
            refine ⟨4031715064257035562586841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2687810042838023708391227 4031715064257035562586841)
            ·
              refine ⟨3023786298192776671940131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4031715064257035562586841 3023786298192776671940131)
              ·
                refine ⟨4535679447289165007910197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3023786298192776671940131 4535679447289165007910197)
                ·
                  refine ⟨425219948183359219491581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4535679447289165007910197 425219948183359219491581)
                  ·
                    rfl

theorem cell21_1863254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_1863254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1863254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1863254 prefixEnd_1863254 := by exact prefixLift 1863254
  have htrace : WordTrace (prefixWord ++ tailWord_1863254) baseStart_1863254 baseEnd_1863254 := by
    simpa [prefixWord, tailWord_1863254, baseEnd_1863254] using wordTrace_append hprefix tailTrace_1863254
  have hstable : (prefixWord ++ tailWord_1863254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863254).length < 2 ^ (prefixWord ++ tailWord_1863254).sum := by decide
  have hdescent : baseEnd_1863254 < baseStart_1863254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863293 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 6]
def baseStart_1863293 : Nat := 118140960795 + 1863293 * 2 ^ 59
def prefixEnd_1863293 : Nat := 4983230072969 + 3 ^ 40 * 1863293 * 2
def baseEnd_1863293 : Nat := 425228848514703818341501

theorem tailTrace_1863293 : CollatzResearch.WordTrace tailWord_1863293 prefixEnd_1863293 425228848514703818341501 := by
  unfold tailWord_1863293
  simp only [CollatzResearch.WordTrace]
  refine ⟨67959878838615160954314533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45306585892410107302876355 67959878838615160954314533)
  ·
    refine ⟨12742477282240342678933975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67959878838615160954314533 12742477282240342678933975)
    ·
      refine ⟨19113715923360514018400963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12742477282240342678933975 19113715923360514018400963)
      ·
        refine ⟨28670573885040771027601445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19113715923360514018400963 28670573885040771027601445)
        ·
          refine ⟨5375732603445144567675271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28670573885040771027601445 5375732603445144567675271)
          ·
            refine ⟨8063598905167716851512907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5375732603445144567675271 8063598905167716851512907)
            ·
              refine ⟨12095398357751575277269361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8063598905167716851512907 12095398357751575277269361)
              ·
                refine ⟨9071548768313681457952021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12095398357751575277269361 9071548768313681457952021)
                ·
                  refine ⟨425228848514703818341501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9071548768313681457952021 425228848514703818341501)
                  ·
                    rfl

theorem cell21_1863293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_1863293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1863293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1863293 prefixEnd_1863293 := by exact prefixLift 1863293
  have htrace : WordTrace (prefixWord ++ tailWord_1863293) baseStart_1863293 baseEnd_1863293 := by
    simpa [prefixWord, tailWord_1863293, baseEnd_1863293] using wordTrace_append hprefix tailTrace_1863293
  have hstable : (prefixWord ++ tailWord_1863293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863293).length < 2 ^ (prefixWord ++ tailWord_1863293).sum := by decide
  have hdescent : baseEnd_1863293 < baseStart_1863293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863327 : List Nat := [1, 1, 2, 7, 1, 1, 1, 3, 4]
def baseStart_1863327 : Nat := 118140960795 + 1863327 * 2 ^ 59
def prefixEnd_1863327 : Nat := 4983230072969 + 3 ^ 40 * 1863327 * 2
def baseEnd_1863327 : Nat := 425236607777927314774765

theorem tailTrace_1863327 : CollatzResearch.WordTrace tailWord_1863327 prefixEnd_1863327 425236607777927314774765 := by
  unfold tailWord_1863327
  simp only [CollatzResearch.WordTrace]
  refine ⟨67961118920491984761052235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45307412613661323174034823 67961118920491984761052235)
  ·
    refine ⟨101941678380737977141578353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67961118920491984761052235 101941678380737977141578353)
    ·
      refine ⟨76456258785553482856183765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101941678380737977141578353 76456258785553482856183765)
      ·
        refine ⟨1791943565286409754441807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 76456258785553482856183765 1791943565286409754441807)
        ·
          refine ⟨2687915347929614631662711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1791943565286409754441807 2687915347929614631662711)
          ·
            refine ⟨4031873021894421947494067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2687915347929614631662711 4031873021894421947494067)
            ·
              refine ⟨6047809532841632921241101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4031873021894421947494067 6047809532841632921241101)
              ·
                refine ⟨2267928574815612345465413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6047809532841632921241101 2267928574815612345465413)
                ·
                  refine ⟨425236607777927314774765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2267928574815612345465413 425236607777927314774765)
                  ·
                    rfl

theorem cell21_1863327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 4].length) (baseStart_1863327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1863327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1863327 prefixEnd_1863327 := by exact prefixLift 1863327
  have htrace : WordTrace (prefixWord ++ tailWord_1863327) baseStart_1863327 baseEnd_1863327 := by
    simpa [prefixWord, tailWord_1863327, baseEnd_1863327] using wordTrace_append hprefix tailTrace_1863327
  have hstable : (prefixWord ++ tailWord_1863327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863327).length < 2 ^ (prefixWord ++ tailWord_1863327).sum := by decide
  have hdescent : baseEnd_1863327 < baseStart_1863327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863352 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 8]
def baseStart_1863352 : Nat := 118140960795 + 1863352 * 2 ^ 59
def prefixEnd_1863352 : Nat := 4983230072969 + 3 ^ 40 * 1863352 * 2
def baseEnd_1863352 : Nat := 425242313118532826858047

theorem tailTrace_1863352 : CollatzResearch.WordTrace tailWord_1863352 prefixEnd_1863352 425242313118532826858047 := by
  unfold tailWord_1863352
  simp only [CollatzResearch.WordTrace]
  refine ⟨33981015372700707015356155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45308020496934276020474873 33981015372700707015356155)
  ·
    refine ⟨50971523059051060523034233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33981015372700707015356155 50971523059051060523034233)
    ·
      refine ⟨38228642294288295392275675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50971523059051060523034233 38228642294288295392275675)
      ·
        refine ⟨57342963441432443088413513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38228642294288295392275675 57342963441432443088413513)
        ·
          refine ⟨43007222581074332316310135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57342963441432443088413513 43007222581074332316310135)
          ·
            refine ⟨64510833871611498474465203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43007222581074332316310135 64510833871611498474465203)
            ·
              refine ⟨96766250807417247711697805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64510833871611498474465203 96766250807417247711697805)
              ·
                refine ⟨36287344052781467891886677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96766250807417247711697805 36287344052781467891886677)
                ·
                  refine ⟨425242313118532826858047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36287344052781467891886677 425242313118532826858047)
                  ·
                    rfl

theorem cell21_1863352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_1863352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1863352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1863352 prefixEnd_1863352 := by exact prefixLift 1863352
  have htrace : WordTrace (prefixWord ++ tailWord_1863352) baseStart_1863352 baseEnd_1863352 := by
    simpa [prefixWord, tailWord_1863352, baseEnd_1863352] using wordTrace_append hprefix tailTrace_1863352
  have hstable : (prefixWord ++ tailWord_1863352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863352).length < 2 ^ (prefixWord ++ tailWord_1863352).sum := by decide
  have hdescent : baseEnd_1863352 < baseStart_1863352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863476 : List Nat := [2, 5, 1, 1, 2, 1, 9]
def baseStart_1863476 : Nat := 118140960795 + 1863476 * 2 ^ 59
def prefixEnd_1863476 : Nat := 4983230072969 + 3 ^ 40 * 1863476 * 2
def baseEnd_1863476 : Nat := 47252290178659574087903

theorem tailTrace_1863476 : CollatzResearch.WordTrace tailWord_1863476 prefixEnd_1863476 47252290178659574087903 := by
  unfold tailWord_1863476
  simp only [CollatzResearch.WordTrace]
  refine ⟨33983276698476091604113141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45311035597968122138817521 33983276698476091604113141)
  ·
    refine ⟨3185932190482133587885607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33983276698476091604113141 3185932190482133587885607)
    ·
      refine ⟨4778898285723200381828411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3185932190482133587885607 4778898285723200381828411)
      ·
        refine ⟨7168347428584800572742617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4778898285723200381828411 7168347428584800572742617)
        ·
          refine ⟨5376260571438600429556963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7168347428584800572742617 5376260571438600429556963)
          ·
            refine ⟨8064390857157900644335445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5376260571438600429556963 8064390857157900644335445)
            ·
              refine ⟨47252290178659574087903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8064390857157900644335445 47252290178659574087903)
              ·
                rfl

theorem cell21_1863476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 9].length) (baseStart_1863476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1863476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1863476 prefixEnd_1863476 := by exact prefixLift 1863476
  have htrace : WordTrace (prefixWord ++ tailWord_1863476) baseStart_1863476 baseEnd_1863476 := by
    simpa [prefixWord, tailWord_1863476, baseEnd_1863476] using wordTrace_append hprefix tailTrace_1863476
  have hstable : (prefixWord ++ tailWord_1863476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863476).length < 2 ^ (prefixWord ++ tailWord_1863476).sum := by decide
  have hdescent : baseEnd_1863476 < baseStart_1863476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863628 : List Nat := [2, 2, 1, 4, 1, 2, 4, 5]
def baseStart_1863628 : Nat := 118140960795 + 1863628 * 2 ^ 59
def prefixEnd_1863628 : Nat := 4983230072969 + 3 ^ 40 * 1863628 * 2
def baseEnd_1863628 : Nat := 141768433359605893419161

theorem tailTrace_1863628 : CollatzResearch.WordTrace tailWord_1863628 prefixEnd_1863628 141768433359605893419161 := by
  unfold tailWord_1863628
  simp only [CollatzResearch.WordTrace]
  refine ⟨33986048646200756583879769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45314731528267675445173025 33986048646200756583879769)
  ·
    refine ⟨25489536484650567437909827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33986048646200756583879769 25489536484650567437909827)
    ·
      refine ⟨38234304726975851156864741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25489536484650567437909827 38234304726975851156864741)
      ·
        refine ⟨7168932136307972091912139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38234304726975851156864741 7168932136307972091912139)
        ·
          refine ⟨10753398204461958137868209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7168932136307972091912139 10753398204461958137868209)
          ·
            refine ⟨8065048653346468603401157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10753398204461958137868209 8065048653346468603401157)
            ·
              refine ⟨1512196622502462863137717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8065048653346468603401157 1512196622502462863137717)
              ·
                refine ⟨141768433359605893419161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1512196622502462863137717 141768433359605893419161)
                ·
                  rfl

theorem cell21_1863628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 5].length) (baseStart_1863628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1863628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1863628 prefixEnd_1863628 := by exact prefixLift 1863628
  have htrace : WordTrace (prefixWord ++ tailWord_1863628) baseStart_1863628 baseEnd_1863628 := by
    simpa [prefixWord, tailWord_1863628, baseEnd_1863628] using wordTrace_append hprefix tailTrace_1863628
  have hstable : (prefixWord ++ tailWord_1863628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863628).length < 2 ^ (prefixWord ++ tailWord_1863628).sum := by decide
  have hdescent : baseEnd_1863628 < baseStart_1863628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863634 : List Nat := [3, 2, 2, 3, 3, 1, 1, 3, 3]
def baseStart_1863634 : Nat := 118140960795 + 1863634 * 2 ^ 59
def prefixEnd_1863634 : Nat := 4983230072969 + 3 ^ 40 * 1863634 * 2
def baseEnd_1863634 : Nat := 425306669360563003157471

theorem tailTrace_1863634 : CollatzResearch.WordTrace tailWord_1863634 prefixEnd_1863634 425306669360563003157471 := by
  unfold tailWord_1863634
  simp only [CollatzResearch.WordTrace]
  refine ⟨16993079032594944048119489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45314877420253184128318637 16993079032594944048119489)
  ·
    refine ⟨12744809274446208036089617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16993079032594944048119489 12744809274446208036089617)
    ·
      refine ⟨9558606955834656027067213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12744809274446208036089617 9558606955834656027067213)
      ·
        refine ⟨3584477608437996010150205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9558606955834656027067213 3584477608437996010150205)
        ·
          refine ⟨1344179103164248503806327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3584477608437996010150205 1344179103164248503806327)
          ·
            refine ⟨2016268654746372755709491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1344179103164248503806327 2016268654746372755709491)
            ·
              refine ⟨3024402982119559133564237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2016268654746372755709491 3024402982119559133564237)
              ·
                refine ⟨1134151118294834675086589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3024402982119559133564237 1134151118294834675086589)
                ·
                  refine ⟨425306669360563003157471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1134151118294834675086589 425306669360563003157471)
                  ·
                    rfl

theorem cell21_1863634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_1863634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1863634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1863634 prefixEnd_1863634 := by exact prefixLift 1863634
  have htrace : WordTrace (prefixWord ++ tailWord_1863634) baseStart_1863634 baseEnd_1863634 := by
    simpa [prefixWord, tailWord_1863634, baseEnd_1863634] using wordTrace_append hprefix tailTrace_1863634
  have hstable : (prefixWord ++ tailWord_1863634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863634).length < 2 ^ (prefixWord ++ tailWord_1863634).sum := by decide
  have hdescent : baseEnd_1863634 < baseStart_1863634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863645 : List Nat := [1, 4, 3, 1, 4, 1, 7]
def baseStart_1863645 : Nat := 118140960795 + 1863645 * 2 ^ 59
def prefixEnd_1863645 : Nat := 4983230072969 + 3 ^ 40 * 1863645 * 2
def baseEnd_1863645 : Nat := 47256575523381047608235

theorem tailTrace_1863645 : CollatzResearch.WordTrace tailWord_1863645 prefixEnd_1863645 47256575523381047608235 := by
  unfold tailWord_1863645
  simp only [CollatzResearch.WordTrace]
  refine ⟨67972717333339925071128389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45315144888893283380752259 67972717333339925071128389)
  ·
    refine ⟨12744884500001235950836573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67972717333339925071128389 12744884500001235950836573)
    ·
      refine ⟨4779331687500463481563715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12744884500001235950836573 4779331687500463481563715)
      ·
        refine ⟨7168997531250695222345573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4779331687500463481563715 7168997531250695222345573)
        ·
          refine ⟨1344187037109505354189795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7168997531250695222345573 1344187037109505354189795)
          ·
            refine ⟨2016280555664258031284693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1344187037109505354189795 2016280555664258031284693)
            ·
              refine ⟨47256575523381047608235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2016280555664258031284693 47256575523381047608235)
              ·
                rfl

theorem cell21_1863645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 7].length) (baseStart_1863645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1863645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1863645 prefixEnd_1863645 := by exact prefixLift 1863645
  have htrace : WordTrace (prefixWord ++ tailWord_1863645) baseStart_1863645 baseEnd_1863645 := by
    simpa [prefixWord, tailWord_1863645, baseEnd_1863645] using wordTrace_append hprefix tailTrace_1863645
  have hstable : (prefixWord ++ tailWord_1863645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863645).length < 2 ^ (prefixWord ++ tailWord_1863645).sum := by decide
  have hdescent : baseEnd_1863645 < baseStart_1863645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863673 : List Nat := [1, 2, 1, 3, 1, 5, 1, 3, 4]
def baseStart_1863673 : Nat := 118140960795 + 1863673 * 2 ^ 59
def prefixEnd_1863673 : Nat := 4983230072969 + 3 ^ 40 * 1863673 * 2
def baseEnd_1863673 : Nat := 425315569691907602007391

theorem tailTrace_1863673 : CollatzResearch.WordTrace tailWord_1863673 prefixEnd_1863673 425315569691907602007391 := by
  unfold tailWord_1863673
  simp only [CollatzResearch.WordTrace]
  refine ⟨67973738577238485853147673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45315825718158990568765115 67973738577238485853147673)
  ·
    refine ⟨50980303932928864389860755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67973738577238485853147673 50980303932928864389860755)
    ·
      refine ⟨76470455899393296584791133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50980303932928864389860755 76470455899393296584791133)
      ·
        refine ⟨28676420962272486219296675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76470455899393296584791133 28676420962272486219296675)
        ·
          refine ⟨43014631443408729328945013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28676420962272486219296675 43014631443408729328945013)
          ·
            refine ⟨4032621697819568374588595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43014631443408729328945013 4032621697819568374588595)
            ·
              refine ⟨6048932546729352561882893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4032621697819568374588595 6048932546729352561882893)
              ·
                refine ⟨2268349705023507210706085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6048932546729352561882893 2268349705023507210706085)
                ·
                  refine ⟨425315569691907602007391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2268349705023507210706085 425315569691907602007391)
                  ·
                    rfl

theorem cell21_1863673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_1863673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1863673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1863673 prefixEnd_1863673 := by exact prefixLift 1863673
  have htrace : WordTrace (prefixWord ++ tailWord_1863673) baseStart_1863673 baseEnd_1863673 := by
    simpa [prefixWord, tailWord_1863673, baseEnd_1863673] using wordTrace_append hprefix tailTrace_1863673
  have hstable : (prefixWord ++ tailWord_1863673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863673).length < 2 ^ (prefixWord ++ tailWord_1863673).sum := by decide
  have hdescent : baseEnd_1863673 < baseStart_1863673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863687 : List Nat := [1, 1, 4, 3, 1, 2, 2, 7]
def baseStart_1863687 : Nat := 118140960795 + 1863687 * 2 ^ 59
def prefixEnd_1863687 : Nat := 4983230072969 + 3 ^ 40 * 1863687 * 2
def baseEnd_1863687 : Nat := 141772921560882229591343

theorem tailTrace_1863687 : CollatzResearch.WordTrace tailWord_1863687 prefixEnd_1863687 141772921560882229591343 := by
  unfold tailWord_1863687
  simp only [CollatzResearch.WordTrace]
  refine ⟨67974249199187766244157315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45316166132791844162771543 67974249199187766244157315)
  ·
    refine ⟨101961373798781649366235973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67974249199187766244157315 101961373798781649366235973)
    ·
      refine ⟨19117757587271559256169245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101961373798781649366235973 19117757587271559256169245)
      ·
        refine ⟨7169159095226834721063467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19117757587271559256169245 7169159095226834721063467)
        ·
          refine ⟨10753738642840252081595201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7169159095226834721063467 10753738642840252081595201)
          ·
            refine ⟨8065303982130189061196401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10753738642840252081595201 8065303982130189061196401)
            ·
              refine ⟨6048977986597641795897301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8065303982130189061196401 6048977986597641795897301)
              ·
                refine ⟨141772921560882229591343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6048977986597641795897301 141772921560882229591343)
                ·
                  rfl

theorem cell21_1863687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 7].length) (baseStart_1863687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1863687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1863687 prefixEnd_1863687 := by exact prefixLift 1863687
  have htrace : WordTrace (prefixWord ++ tailWord_1863687) baseStart_1863687 baseEnd_1863687 := by
    simpa [prefixWord, tailWord_1863687, baseEnd_1863687] using wordTrace_append hprefix tailTrace_1863687
  have hstable : (prefixWord ++ tailWord_1863687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863687).length < 2 ^ (prefixWord ++ tailWord_1863687).sum := by decide
  have hdescent : baseEnd_1863687 < baseStart_1863687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863794 : List Nat := [3, 2, 1, 2, 2, 2, 2, 2, 5]
def baseStart_1863794 : Nat := 118140960795 + 1863794 * 2 ^ 59
def prefixEnd_1863794 : Nat := 4983230072969 + 3 ^ 40 * 1863794 * 2
def baseEnd_1863794 : Nat := 425343183540438280490477

theorem tailTrace_1863794 : CollatzResearch.WordTrace tailWord_1863794 prefixEnd_1863794 425343183540438280490477 := by
  unfold tailWord_1863794
  simp only [CollatzResearch.WordTrace]
  refine ⟨16994537952450030879575609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45318767873200082345534957 16994537952450030879575609)
  ·
    refine ⟨12745903464337523159681707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16994537952450030879575609 12745903464337523159681707)
    ·
      refine ⟨19118855196506284739522561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12745903464337523159681707 19118855196506284739522561)
      ·
        refine ⟨14339141397379713554641921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19118855196506284739522561 14339141397379713554641921)
        ·
          refine ⟨10754356048034785165981441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14339141397379713554641921 10754356048034785165981441)
          ·
            refine ⟨8065767036026088874486081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10754356048034785165981441 8065767036026088874486081)
            ·
              refine ⟨6049325277019566655864561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8065767036026088874486081 6049325277019566655864561)
              ·
                refine ⟨4536993957764674991898421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6049325277019566655864561 4536993957764674991898421)
                ·
                  refine ⟨425343183540438280490477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4536993957764674991898421 425343183540438280490477)
                  ·
                    rfl

theorem cell21_1863794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_1863794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1863794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1863794 prefixEnd_1863794 := by exact prefixLift 1863794
  have htrace : WordTrace (prefixWord ++ tailWord_1863794) baseStart_1863794 baseEnd_1863794 := by
    simpa [prefixWord, tailWord_1863794, baseEnd_1863794] using wordTrace_append hprefix tailTrace_1863794
  have hstable : (prefixWord ++ tailWord_1863794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863794).length < 2 ^ (prefixWord ++ tailWord_1863794).sum := by decide
  have hdescent : baseEnd_1863794 < baseStart_1863794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863811 : List Nat := [1, 1, 1, 3, 3, 3, 3, 3, 3]
def baseStart_1863811 : Nat := 118140960795 + 1863811 * 2 ^ 59
def prefixEnd_1863811 : Nat := 4983230072969 + 3 ^ 40 * 1863811 * 2
def baseEnd_1863811 : Nat := 425347063172050028707109

theorem tailTrace_1863811 : CollatzResearch.WordTrace tailWord_1863811 prefixEnd_1863811 425347063172050028707109 := by
  unfold tailWord_1863811
  simp only [CollatzResearch.WordTrace]
  refine ⟨67978771850738535421671287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45319181233825690281114191 67978771850738535421671287)
  ·
    refine ⟨101968157776107803132506931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67978771850738535421671287 101968157776107803132506931)
    ·
      refine ⟨152952236664161704698760397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101968157776107803132506931 152952236664161704698760397)
      ·
        refine ⟨57357088749060639262035149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152952236664161704698760397 57357088749060639262035149)
        ·
          refine ⟨21508908280897739723263181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57357088749060639262035149 21508908280897739723263181)
          ·
            refine ⟨8065840605336652396223693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21508908280897739723263181 8065840605336652396223693)
            ·
              refine ⟨3024690227001244648583885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8065840605336652396223693 3024690227001244648583885)
              ·
                refine ⟨1134258835125466743218957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3024690227001244648583885 1134258835125466743218957)
                ·
                  refine ⟨425347063172050028707109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1134258835125466743218957 425347063172050028707109)
                  ·
                    rfl

theorem cell21_1863811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3].length) (baseStart_1863811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1863811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1863811 prefixEnd_1863811 := by exact prefixLift 1863811
  have htrace : WordTrace (prefixWord ++ tailWord_1863811) baseStart_1863811 baseEnd_1863811 := by
    simpa [prefixWord, tailWord_1863811, baseEnd_1863811] using wordTrace_append hprefix tailTrace_1863811
  have hstable : (prefixWord ++ tailWord_1863811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863811).length < 2 ^ (prefixWord ++ tailWord_1863811).sum := by decide
  have hdescent : baseEnd_1863811 < baseStart_1863811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863839 : List Nat := [1, 1, 2, 6, 1, 1, 1, 8]
def baseStart_1863839 : Nat := 118140960795 + 1863839 * 2 ^ 59
def prefixEnd_1863839 : Nat := 4983230072969 + 3 ^ 40 * 1863839 * 2
def baseEnd_1863839 : Nat := 141784484384509400746795

theorem tailTrace_1863839 : CollatzResearch.WordTrace tailWord_1863839 prefixEnd_1863839 141784484384509400746795 := by
  unfold tailWord_1863839
  simp only [CollatzResearch.WordTrace]
  refine ⟨67979793094637096203690571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45319862063091397469127047 67979793094637096203690571)
  ·
    refine ⟨101969689641955644305535857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67979793094637096203690571 101969689641955644305535857)
    ·
      refine ⟨76477267231466733229151893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101969689641955644305535857 76477267231466733229151893)
      ·
        refine ⟨3584871901475003120116495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76477267231466733229151893 3584871901475003120116495)
        ·
          refine ⟨5377307852212504680174743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3584871901475003120116495 5377307852212504680174743)
          ·
            refine ⟨8065961778318757020262115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5377307852212504680174743 8065961778318757020262115)
            ·
              refine ⟨12098942667478135530393173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8065961778318757020262115 12098942667478135530393173)
              ·
                refine ⟨141784484384509400746795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12098942667478135530393173 141784484384509400746795)
                ·
                  rfl

theorem cell21_1863839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 8].length) (baseStart_1863839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1863839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1863839 prefixEnd_1863839 := by exact prefixLift 1863839
  have htrace : WordTrace (prefixWord ++ tailWord_1863839) baseStart_1863839 baseEnd_1863839 := by
    simpa [prefixWord, tailWord_1863839, baseEnd_1863839] using wordTrace_append hprefix tailTrace_1863839
  have hstable : (prefixWord ++ tailWord_1863839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863839).length < 2 ^ (prefixWord ++ tailWord_1863839).sum := by decide
  have hdescent : baseEnd_1863839 < baseStart_1863839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863842 : List Nat := [3, 3, 1, 3, 1, 2, 1, 3, 4]
def baseStart_1863842 : Nat := 118140960795 + 1863842 * 2 ^ 59
def prefixEnd_1863842 : Nat := 4983230072969 + 3 ^ 40 * 1863842 * 2
def baseEnd_1863842 : Nat := 425354137794400863690379

theorem tailTrace_1863842 : CollatzResearch.WordTrace tailWord_1863842 prefixEnd_1863842 425354137794400863690379 := by
  unfold tailWord_1863842
  simp only [CollatzResearch.WordTrace]
  refine ⟨16994975628406556929012445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45319935009084151810699853 16994975628406556929012445)
  ·
    refine ⟨6373115860652458848379667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16994975628406556929012445 6373115860652458848379667)
    ·
      refine ⟨9559673790978688272569501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6373115860652458848379667 9559673790978688272569501)
      ·
        refine ⟨3584877671617008102213563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9559673790978688272569501 3584877671617008102213563)
        ·
          refine ⟨5377316507425512153320345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3584877671617008102213563 5377316507425512153320345)
          ·
            refine ⟨4032987380569134114990259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5377316507425512153320345 4032987380569134114990259)
            ·
              refine ⟨6049481070853701172485389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4032987380569134114990259 6049481070853701172485389)
              ·
                refine ⟨2268555401570137939682021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6049481070853701172485389 2268555401570137939682021)
                ·
                  refine ⟨425354137794400863690379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2268555401570137939682021 425354137794400863690379)
                  ·
                    rfl

theorem cell21_1863842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_1863842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1863842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1863842 prefixEnd_1863842 := by exact prefixLift 1863842
  have htrace : WordTrace (prefixWord ++ tailWord_1863842) baseStart_1863842 baseEnd_1863842 := by
    simpa [prefixWord, tailWord_1863842, baseEnd_1863842] using wordTrace_append hprefix tailTrace_1863842
  have hstable : (prefixWord ++ tailWord_1863842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863842).length < 2 ^ (prefixWord ++ tailWord_1863842).sum := by decide
  have hdescent : baseEnd_1863842 < baseStart_1863842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863915 : List Nat := [1, 1, 1, 1, 2, 5, 5, 5]
def baseStart_1863915 : Nat := 118140960795 + 1863915 * 2 ^ 59
def prefixEnd_1863915 : Nat := 4983230072969 + 3 ^ 40 * 1863915 * 2
def baseEnd_1863915 : Nat := 141790265796322986324521

theorem tailTrace_1863915 : CollatzResearch.WordTrace tailWord_1863915 prefixEnd_1863915 141790265796322986324521 := by
  unfold tailWord_1863915
  simp only [CollatzResearch.WordTrace]
  refine ⟨67982565042361761183457199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45321710028241174122304799 67982565042361761183457199)
  ·
    refine ⟨101973847563542641775185799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67982565042361761183457199 101973847563542641775185799)
    ·
      refine ⟨152960771345313962662778699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101973847563542641775185799 152960771345313962662778699)
      ·
        refine ⟨229441157017970943994168049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152960771345313962662778699 229441157017970943994168049)
        ·
          refine ⟨172080867763478207995626037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229441157017970943994168049 172080867763478207995626037)
          ·
            refine ⟨16132581352826081999589941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172080867763478207995626037 16132581352826081999589941)
            ·
              refine ⟨1512429501827445187461557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16132581352826081999589941 1512429501827445187461557)
              ·
                refine ⟨141790265796322986324521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1512429501827445187461557 141790265796322986324521)
                ·
                  rfl

theorem cell21_1863915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 5].length) (baseStart_1863915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1863915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1863915 prefixEnd_1863915 := by exact prefixLift 1863915
  have htrace : WordTrace (prefixWord ++ tailWord_1863915) baseStart_1863915 baseEnd_1863915 := by
    simpa [prefixWord, tailWord_1863915, baseEnd_1863915] using wordTrace_append hprefix tailTrace_1863915
  have hstable : (prefixWord ++ tailWord_1863915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863915).length < 2 ^ (prefixWord ++ tailWord_1863915).sum := by decide
  have hdescent : baseEnd_1863915 < baseStart_1863915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1863966 : List Nat := [4, 3, 2, 1, 1, 3, 2, 5]
def baseStart_1863966 : Nat := 118140960795 + 1863966 * 2 ^ 59
def prefixEnd_1863966 : Nat := 4983230072969 + 3 ^ 40 * 1863966 * 2
def baseEnd_1863966 : Nat := 141794145427934734541153

theorem tailTrace_1863966 : CollatzResearch.WordTrace tailWord_1863966 prefixEnd_1863966 141794145427934734541153 := by
  unfold tailWord_1863966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8498053145647124611695469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45322950110117997929042501 8498053145647124611695469)
  ·
    refine ⟨3186769929617671729385801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8498053145647124611695469 3186769929617671729385801)
    ·
      refine ⟨2390077447213253797039351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3186769929617671729385801 2390077447213253797039351)
      ·
        refine ⟨3585116170819880695559027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2390077447213253797039351 3585116170819880695559027)
        ·
          refine ⟨5377674256229821043338541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3585116170819880695559027 5377674256229821043338541)
          ·
            refine ⟨2016627846086182891251953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5377674256229821043338541 2016627846086182891251953)
            ·
              refine ⟨1512470884564637168438965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2016627846086182891251953 1512470884564637168438965)
              ·
                refine ⟨141794145427934734541153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1512470884564637168438965 141794145427934734541153)
                ·
                  rfl

theorem cell21_1863966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_1863966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1863966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1863966 prefixEnd_1863966 := by exact prefixLift 1863966
  have htrace : WordTrace (prefixWord ++ tailWord_1863966) baseStart_1863966 baseEnd_1863966 := by
    simpa [prefixWord, tailWord_1863966, baseEnd_1863966] using wordTrace_append hprefix tailTrace_1863966
  have hstable : (prefixWord ++ tailWord_1863966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1863966).length < 2 ^ (prefixWord ++ tailWord_1863966).sum := by decide
  have hdescent : baseEnd_1863966 < baseStart_1863966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1863966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864019 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 8]
def baseStart_1864019 : Nat := 118140960795 + 1864019 * 2 ^ 59
def prefixEnd_1864019 : Nat := 4983230072969 + 3 ^ 40 * 1864019 * 2
def baseEnd_1864019 : Nat := 425394531605887889240017

theorem tailTrace_1864019 : CollatzResearch.WordTrace tailWord_1864019 prefixEnd_1864019 425394531605887889240017 := by
  unfold tailWord_1864019
  simp only [CollatzResearch.WordTrace]
  refine ⟨67986358233984986945243111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45324238822656657963495407 67986358233984986945243111)
  ·
    refine ⟨101979537350977480417864667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67986358233984986945243111 101979537350977480417864667)
    ·
      refine ⟨152969306026466220626797001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101979537350977480417864667 152969306026466220626797001)
      ·
        refine ⟨114726979519849665470097751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152969306026466220626797001 114726979519849665470097751)
        ·
          refine ⟨172090469279774498205146627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114726979519849665470097751 172090469279774498205146627)
          ·
            refine ⟨258135703919661747307719941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172090469279774498205146627 258135703919661747307719941)
            ·
              refine ⟨48400444484936577620197489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 258135703919661747307719941 48400444484936577620197489)
              ·
                refine ⟨36300333363702433215148117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48400444484936577620197489 36300333363702433215148117)
                ·
                  refine ⟨425394531605887889240017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36300333363702433215148117 425394531605887889240017)
                  ·
                    rfl

theorem cell21_1864019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 8].length) (baseStart_1864019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864019 prefixEnd_1864019 := by exact prefixLift 1864019
  have htrace : WordTrace (prefixWord ++ tailWord_1864019) baseStart_1864019 baseEnd_1864019 := by
    simpa [prefixWord, tailWord_1864019, baseEnd_1864019] using wordTrace_append hprefix tailTrace_1864019
  have hstable : (prefixWord ++ tailWord_1864019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864019).length < 2 ^ (prefixWord ++ tailWord_1864019).sum := by decide
  have hdescent : baseEnd_1864019 < baseStart_1864019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864050 : List Nat := [3, 2, 1, 2, 1, 12]
def baseStart_1864050 : Nat := 118140960795 + 1864050 * 2 ^ 59
def prefixEnd_1864050 : Nat := 4983230072969 + 3 ^ 40 * 1864050 * 2
def baseEnd_1864050 : Nat := 15755615045490323119381

theorem tailTrace_1864050 : CollatzResearch.WordTrace tailWord_1864050 prefixEnd_1864050 15755615045490323119381 := by
  unfold tailWord_1864050
  simp only [CollatzResearch.WordTrace]
  refine ⟨16996872224218169809905401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45324992597915119493081069 16996872224218169809905401)
  ·
    refine ⟨12747654168163627357429051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16996872224218169809905401 12747654168163627357429051)
    ·
      refine ⟨19121481252245441036143577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12747654168163627357429051 19121481252245441036143577)
      ·
        refine ⟨14341110939184080777107683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19121481252245441036143577 14341110939184080777107683)
        ·
          refine ⟨21511666408776121165661525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14341110939184080777107683 21511666408776121165661525)
          ·
            refine ⟨15755615045490323119381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 21511666408776121165661525 15755615045490323119381)
            ·
              rfl

theorem cell21_1864050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 12].length) (baseStart_1864050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864050 prefixEnd_1864050 := by exact prefixLift 1864050
  have htrace : WordTrace (prefixWord ++ tailWord_1864050) baseStart_1864050 baseEnd_1864050 := by
    simpa [prefixWord, tailWord_1864050, baseEnd_1864050] using wordTrace_append hprefix tailTrace_1864050
  have hstable : (prefixWord ++ tailWord_1864050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864050).length < 2 ^ (prefixWord ++ tailWord_1864050).sum := by decide
  have hdescent : baseEnd_1864050 < baseStart_1864050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864053 : List Nat := [1, 3, 4, 1, 2, 1, 1, 4, 4]
def baseStart_1864053 : Nat := 118140960795 + 1864053 * 2 ^ 59
def prefixEnd_1864053 : Nat := 4983230072969 + 3 ^ 40 * 1864053 * 2
def baseEnd_1864053 : Nat := 425402290869111385673281

theorem tailTrace_1864053 : CollatzResearch.WordTrace tailWord_1864053 prefixEnd_1864053 425402290869111385673281 := by
  unfold tailWord_1864053
  simp only [CollatzResearch.WordTrace]
  refine ⟨67987598315861810751980813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45325065543907873834653875 67987598315861810751980813)
  ·
    refine ⟨25495349368448179031992805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67987598315861810751980813 25495349368448179031992805)
    ·
      refine ⟨4780378006584033568498651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25495349368448179031992805 4780378006584033568498651)
      ·
        refine ⟨7170567009876050352747977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4780378006584033568498651 7170567009876050352747977)
        ·
          refine ⟨5377925257407037764560983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7170567009876050352747977 5377925257407037764560983)
          ·
            refine ⟨8066887886110556646841475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5377925257407037764560983 8066887886110556646841475)
            ·
              refine ⟨12100331829165834970262213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8066887886110556646841475 12100331829165834970262213)
              ·
                refine ⟨2268812217968594056924165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12100331829165834970262213 2268812217968594056924165)
                ·
                  refine ⟨425402290869111385673281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2268812217968594056924165 425402290869111385673281)
                  ·
                    rfl

theorem cell21_1864053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_1864053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864053 prefixEnd_1864053 := by exact prefixLift 1864053
  have htrace : WordTrace (prefixWord ++ tailWord_1864053) baseStart_1864053 baseEnd_1864053 := by
    simpa [prefixWord, tailWord_1864053, baseEnd_1864053] using wordTrace_append hprefix tailTrace_1864053
  have hstable : (prefixWord ++ tailWord_1864053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864053).length < 2 ^ (prefixWord ++ tailWord_1864053).sum := by decide
  have hdescent : baseEnd_1864053 < baseStart_1864053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864171 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 6]
def baseStart_1864171 : Nat := 118140960795 + 1864171 * 2 ^ 59
def prefixEnd_1864171 : Nat := 4983230072969 + 3 ^ 40 * 1864171 * 2
def baseEnd_1864171 : Nat := 425429220076769402706373

theorem tailTrace_1864171 : CollatzResearch.WordTrace tailWord_1864171 prefixEnd_1864171 425429220076769402706373 := by
  unfold tailWord_1864171
  simp only [CollatzResearch.WordTrace]
  refine ⟨67991902129434316904776367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45327934752956211269850911 67991902129434316904776367)
  ·
    refine ⟨101987853194151475357164551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67991902129434316904776367 101987853194151475357164551)
    ·
      refine ⟨152981779791227213035746827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101987853194151475357164551 152981779791227213035746827)
      ·
        refine ⟨229472669686840819553620241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152981779791227213035746827 229472669686840819553620241)
        ·
          refine ⟨172104502265130614665215181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 229472669686840819553620241 172104502265130614665215181)
          ·
            refine ⟨64539188349423980499455693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172104502265130614665215181 64539188349423980499455693)
            ·
              refine ⟨24202195631033992687295885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64539188349423980499455693 24202195631033992687295885)
              ·
                refine ⟨9075823361637747257735957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24202195631033992687295885 9075823361637747257735957)
                ·
                  refine ⟨425429220076769402706373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9075823361637747257735957 425429220076769402706373)
                  ·
                    rfl

theorem cell21_1864171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 6].length) (baseStart_1864171 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864171 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864171 prefixEnd_1864171 := by exact prefixLift 1864171
  have htrace : WordTrace (prefixWord ++ tailWord_1864171) baseStart_1864171 baseEnd_1864171 := by
    simpa [prefixWord, tailWord_1864171, baseEnd_1864171] using wordTrace_append hprefix tailTrace_1864171
  have hstable : (prefixWord ++ tailWord_1864171).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864171).length < 2 ^ (prefixWord ++ tailWord_1864171).sum := by decide
  have hdescent : baseEnd_1864171 < baseStart_1864171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864174 : List Nat := [4, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_1864174 : Nat := 118140960795 + 1864174 * 2 ^ 59
def prefixEnd_1864174 : Nat := 4983230072969 + 3 ^ 40 * 1864174 * 2
def baseEnd_1864174 : Nat := 425429904717642064156367

theorem tailTrace_1864174 : CollatzResearch.WordTrace tailWord_1864174 prefixEnd_1864174 425429904717642064156367 := by
  unfold tailWord_1864174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8499001443552931052141947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45328007698948965611423717 8499001443552931052141947)
  ·
    refine ⟨12748502165329396578212921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8499001443552931052141947 12748502165329396578212921)
    ·
      refine ⟨9561376623997047433659691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12748502165329396578212921 9561376623997047433659691)
      ·
        refine ⟨14342064935995571150489537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9561376623997047433659691 14342064935995571150489537)
        ·
          refine ⟨10756548701996678362867153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14342064935995571150489537 10756548701996678362867153)
          ·
            refine ⟨8067411526497508772150365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10756548701996678362867153 8067411526497508772150365)
            ·
              refine ⟨3025279322436565789556387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8067411526497508772150365 3025279322436565789556387)
              ·
                refine ⟨4537918983654848684334581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3025279322436565789556387 4537918983654848684334581)
                ·
                  refine ⟨425429904717642064156367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4537918983654848684334581 425429904717642064156367)
                  ·
                    rfl

theorem cell21_1864174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_1864174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864174 prefixEnd_1864174 := by exact prefixLift 1864174
  have htrace : WordTrace (prefixWord ++ tailWord_1864174) baseStart_1864174 baseEnd_1864174 := by
    simpa [prefixWord, tailWord_1864174, baseEnd_1864174] using wordTrace_append hprefix tailTrace_1864174
  have hstable : (prefixWord ++ tailWord_1864174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864174).length < 2 ^ (prefixWord ++ tailWord_1864174).sum := by decide
  have hdescent : baseEnd_1864174 < baseStart_1864174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864202 : List Nat := [3, 1, 2, 2, 2, 1, 1, 9]
def baseStart_1864202 : Nat := 118140960795 + 1864202 * 2 ^ 59
def prefixEnd_1864202 : Nat := 4983230072969 + 3 ^ 40 * 1864202 * 2
def baseEnd_1864202 : Nat := 141812098233040079229881

theorem tailTrace_1864202 : CollatzResearch.WordTrace tailWord_1864202 prefixEnd_1864202 141812098233040079229881 := by
  unfold tailWord_1864202
  simp only [CollatzResearch.WordTrace]
  refine ⟨16998258198080502299788715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45328688528214672799436573 16998258198080502299788715)
  ·
    refine ⟨25497387297120753449683073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16998258198080502299788715 25497387297120753449683073)
    ·
      refine ⟨19123040472840565087262305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25497387297120753449683073 19123040472840565087262305)
      ·
        refine ⟨14342280354630423815446729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19123040472840565087262305 14342280354630423815446729)
        ·
          refine ⟨10756710265972817861585047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14342280354630423815446729 10756710265972817861585047)
          ·
            refine ⟨16135065398959226792377571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10756710265972817861585047 16135065398959226792377571)
            ·
              refine ⟨24202598098438840188566357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16135065398959226792377571 24202598098438840188566357)
              ·
                refine ⟨141812098233040079229881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24202598098438840188566357 141812098233040079229881)
                ·
                  rfl

theorem cell21_1864202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_1864202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864202 prefixEnd_1864202 := by exact prefixLift 1864202
  have htrace : WordTrace (prefixWord ++ tailWord_1864202) baseStart_1864202 baseEnd_1864202 := by
    simpa [prefixWord, tailWord_1864202, baseEnd_1864202] using wordTrace_append hprefix tailTrace_1864202
  have hstable : (prefixWord ++ tailWord_1864202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864202).length < 2 ^ (prefixWord ++ tailWord_1864202).sum := by decide
  have hdescent : baseEnd_1864202 < baseStart_1864202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864323 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 6]
def baseStart_1864323 : Nat := 118140960795 + 1864323 * 2 ^ 59
def prefixEnd_1864323 : Nat := 4983230072969 + 3 ^ 40 * 1864323 * 2
def baseEnd_1864323 : Nat := 425463908547650916172729

theorem tailTrace_1864323 : CollatzResearch.WordTrace tailWord_1864323 prefixEnd_1864323 425463908547650916172729 := by
  unfold tailWord_1864323
  simp only [CollatzResearch.WordTrace]
  refine ⟨67997446024883646864309623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45331630683255764576206415 67997446024883646864309623)
  ·
    refine ⟨101996169037325470296464435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67997446024883646864309623 101996169037325470296464435)
    ·
      refine ⟨152994253555988205444696653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101996169037325470296464435 152994253555988205444696653)
      ·
        refine ⟨57372845083495577041761245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152994253555988205444696653 57372845083495577041761245)
        ·
          refine ⟨21514816906310841390660467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57372845083495577041761245 21514816906310841390660467)
          ·
            refine ⟨32272225359466262085990701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21514816906310841390660467 32272225359466262085990701)
            ·
              refine ⟨12102084509799848282246513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32272225359466262085990701 12102084509799848282246513)
              ·
                refine ⟨9076563382349886211684885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12102084509799848282246513 9076563382349886211684885)
                ·
                  refine ⟨425463908547650916172729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9076563382349886211684885 425463908547650916172729)
                  ·
                    rfl

theorem cell21_1864323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 6].length) (baseStart_1864323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864323 prefixEnd_1864323 := by exact prefixLift 1864323
  have htrace : WordTrace (prefixWord ++ tailWord_1864323) baseStart_1864323 baseEnd_1864323 := by
    simpa [prefixWord, tailWord_1864323, baseEnd_1864323] using wordTrace_append hprefix tailTrace_1864323
  have hstable : (prefixWord ++ tailWord_1864323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864323).length < 2 ^ (prefixWord ++ tailWord_1864323).sum := by decide
  have hdescent : baseEnd_1864323 < baseStart_1864323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864343 : List Nat := [1, 1, 3, 3, 2, 1, 5, 2, 3]
def baseStart_1864343 : Nat := 118140960795 + 1864343 * 2 ^ 59
def prefixEnd_1864343 : Nat := 4983230072969 + 3 ^ 40 * 1864343 * 2
def baseEnd_1864343 : Nat := 425468472820135325839355

theorem tailTrace_1864343 : CollatzResearch.WordTrace tailWord_1864343 prefixEnd_1864343 425468472820135325839355 := by
  unfold tailWord_1864343
  simp only [CollatzResearch.WordTrace]
  refine ⟨67998175484811190280037683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45332116989874126853358455 67998175484811190280037683)
  ·
    refine ⟨101997263227216785420056525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67998175484811190280037683 101997263227216785420056525)
    ·
      refine ⟨38248973710206294532521197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101997263227216785420056525 38248973710206294532521197)
      ·
        refine ⟨14343365141327360449695449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38248973710206294532521197 14343365141327360449695449)
        ·
          refine ⟨10757523855995520337271587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14343365141327360449695449 10757523855995520337271587)
          ·
            refine ⟨16136285783993280505907381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10757523855995520337271587 16136285783993280505907381)
            ·
              refine ⟨1512776792249370047428817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16136285783993280505907381 1512776792249370047428817)
              ·
                refine ⟨1134582594187027535571613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1512776792249370047428817 1134582594187027535571613)
                ·
                  refine ⟨425468472820135325839355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1134582594187027535571613 425468472820135325839355)
                  ·
                    rfl

theorem cell21_1864343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 3].length) (baseStart_1864343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864343 prefixEnd_1864343 := by exact prefixLift 1864343
  have htrace : WordTrace (prefixWord ++ tailWord_1864343) baseStart_1864343 baseEnd_1864343 := by
    simpa [prefixWord, tailWord_1864343, baseEnd_1864343] using wordTrace_append hprefix tailTrace_1864343
  have hstable : (prefixWord ++ tailWord_1864343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864343).length < 2 ^ (prefixWord ++ tailWord_1864343).sum := by decide
  have hdescent : baseEnd_1864343 < baseStart_1864343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864368 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 7]
def baseStart_1864368 : Nat := 118140960795 + 1864368 * 2 ^ 59
def prefixEnd_1864368 : Nat := 4983230072969 + 3 ^ 40 * 1864368 * 2
def baseEnd_1864368 : Nat := 425474178160740837922637

theorem tailTrace_1864368 : CollatzResearch.WordTrace tailWord_1864368 prefixEnd_1864368 425474178160740837922637 := by
  unfold tailWord_1864368
  simp only [CollatzResearch.WordTrace]
  refine ⟨33999543654860309774848879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45332724873147079699798505 33999543654860309774848879)
  ·
    refine ⟨50999315482290464662273319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33999543654860309774848879 50999315482290464662273319)
    ·
      refine ⟨76498973223435696993409979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50999315482290464662273319 76498973223435696993409979)
      ·
        refine ⟨114748459835153545490114969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76498973223435696993409979 114748459835153545490114969)
        ·
          refine ⟨86061344876365159117586227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114748459835153545490114969 86061344876365159117586227)
          ·
            refine ⟨129092017314547738676379341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86061344876365159117586227 129092017314547738676379341)
            ·
              refine ⟨48409506492955402003642253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129092017314547738676379341 48409506492955402003642253)
              ·
                refine ⟨18153564934858275751365845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48409506492955402003642253 18153564934858275751365845)
                ·
                  refine ⟨425474178160740837922637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18153564934858275751365845 425474178160740837922637)
                  ·
                    rfl

theorem cell21_1864368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_1864368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864368 prefixEnd_1864368 := by exact prefixLift 1864368
  have htrace : WordTrace (prefixWord ++ tailWord_1864368) baseStart_1864368 baseEnd_1864368 := by
    simpa [prefixWord, tailWord_1864368, baseEnd_1864368] using wordTrace_append hprefix tailTrace_1864368
  have hstable : (prefixWord ++ tailWord_1864368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864368).length < 2 ^ (prefixWord ++ tailWord_1864368).sum := by decide
  have hdescent : baseEnd_1864368 < baseStart_1864368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864405 : List Nat := [1, 3, 2, 5, 2, 1, 1, 6]
def baseStart_1864405 : Nat := 118140960795 + 1864405 * 2 ^ 59
def prefixEnd_1864405 : Nat := 4983230072969 + 3 ^ 40 * 1864405 * 2
def baseEnd_1864405 : Nat := 141827540688278998601965

theorem tailTrace_1864405 : CollatzResearch.WordTrace tailWord_1864405 prefixEnd_1864405 141827540688278998601965 := by
  unfold tailWord_1864405
  simp only [CollatzResearch.WordTrace]
  refine ⟨68000436810586574868794669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45333624540391049912529779 68000436810586574868794669)
  ·
    refine ⟨25500163803969965575798001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68000436810586574868794669 25500163803969965575798001)
    ·
      refine ⟨19125122852977474181848501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25500163803969965575798001 19125122852977474181848501)
      ·
        refine ⟨1792980267466638204548297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19125122852977474181848501 1792980267466638204548297)
        ·
          refine ⟨1344735200599978653411223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1792980267466638204548297 1344735200599978653411223)
          ·
            refine ⟨2017102800899967980116835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1344735200599978653411223 2017102800899967980116835)
            ·
              refine ⟨3025654201349951970175253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2017102800899967980116835 3025654201349951970175253)
              ·
                refine ⟨141827540688278998601965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3025654201349951970175253 141827540688278998601965)
                ·
                  rfl

theorem cell21_1864405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 6].length) (baseStart_1864405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864405 prefixEnd_1864405 := by exact prefixLift 1864405
  have htrace : WordTrace (prefixWord ++ tailWord_1864405) baseStart_1864405 baseEnd_1864405 := by
    simpa [prefixWord, tailWord_1864405, baseEnd_1864405] using wordTrace_append hprefix tailTrace_1864405
  have hstable : (prefixWord ++ tailWord_1864405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864405).length < 2 ^ (prefixWord ++ tailWord_1864405).sum := by decide
  have hdescent : baseEnd_1864405 < baseStart_1864405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864450 : List Nat := [3, 4, 1, 1, 1, 4, 1, 2, 4]
def baseStart_1864450 : Nat := 118140960795 + 1864450 * 2 ^ 59
def prefixEnd_1864450 : Nat := 4983230072969 + 3 ^ 40 * 1864450 * 2
def baseEnd_1864450 : Nat := 425492891677926917555803

theorem tailTrace_1864450 : CollatzResearch.WordTrace tailWord_1864450 prefixEnd_1864450 425492891677926917555803 := by
  unfold tailWord_1864450
  simp only [CollatzResearch.WordTrace]
  refine ⟨17000519523855886888545701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45334718730282365036121869 17000519523855886888545701)
  ·
    refine ⟨3187597410722978791602319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17000519523855886888545701 3187597410722978791602319)
    ·
      refine ⟨4781396116084468187403479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3187597410722978791602319 4781396116084468187403479)
      ·
        refine ⟨7172094174126702281105219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4781396116084468187403479 7172094174126702281105219)
        ·
          refine ⟨10758141261190053421657829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7172094174126702281105219 10758141261190053421657829)
          ·
            refine ⟨2017151486473135016560843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10758141261190053421657829 2017151486473135016560843)
            ·
              refine ⟨3025727229709702524841265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2017151486473135016560843 3025727229709702524841265)
              ·
                refine ⟨2269295422282276893630949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3025727229709702524841265 2269295422282276893630949)
                ·
                  refine ⟨425492891677926917555803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2269295422282276893630949 425492891677926917555803)
                  ·
                    rfl

theorem cell21_1864450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_1864450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864450 prefixEnd_1864450 := by exact prefixLift 1864450
  have htrace : WordTrace (prefixWord ++ tailWord_1864450) baseStart_1864450 baseEnd_1864450 := by
    simpa [prefixWord, tailWord_1864450, baseEnd_1864450] using wordTrace_append hprefix tailTrace_1864450
  have hstable : (prefixWord ++ tailWord_1864450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864450).length < 2 ^ (prefixWord ++ tailWord_1864450).sum := by decide
  have hdescent : baseEnd_1864450 < baseStart_1864450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864489 : List Nat := [1, 2, 1, 1, 1, 1, 1, 13]
def baseStart_1864489 : Nat := 118140960795 + 1864489 * 2 ^ 59
def prefixEnd_1864489 : Nat := 4983230072969 + 3 ^ 40 * 1864489 * 2
def baseEnd_1864489 : Nat := 141833930669757172135241

theorem tailTrace_1864489 : CollatzResearch.WordTrace tailWord_1864489 prefixEnd_1864489 141833930669757172135241 := by
  unfold tailWord_1864489
  simp only [CollatzResearch.WordTrace]
  refine ⟨68003500542282257214852521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45335667028188171476568347 68003500542282257214852521)
  ·
    refine ⟨51002625406711692911139391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68003500542282257214852521 51002625406711692911139391)
    ·
      refine ⟨76503938110067539366709087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51002625406711692911139391 76503938110067539366709087)
      ·
        refine ⟨114755907165101309050063631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76503938110067539366709087 114755907165101309050063631)
        ·
          refine ⟨172133860747651963575095447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114755907165101309050063631 172133860747651963575095447)
          ·
            refine ⟨258200791121477945362643171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172133860747651963575095447 258200791121477945362643171)
            ·
              refine ⟨387301186682216918043964757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 258200791121477945362643171 387301186682216918043964757)
              ·
                refine ⟨141833930669757172135241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 387301186682216918043964757 141833930669757172135241)
                ·
                  rfl

theorem cell21_1864489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 13].length) (baseStart_1864489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864489 prefixEnd_1864489 := by exact prefixLift 1864489
  have htrace : WordTrace (prefixWord ++ tailWord_1864489) baseStart_1864489 baseEnd_1864489 := by
    simpa [prefixWord, tailWord_1864489, baseEnd_1864489] using wordTrace_append hprefix tailTrace_1864489
  have hstable : (prefixWord ++ tailWord_1864489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864489).length < 2 ^ (prefixWord ++ tailWord_1864489).sum := by decide
  have hdescent : baseEnd_1864489 < baseStart_1864489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864627 : List Nat := [1, 1, 1, 2, 3, 1, 2, 6, 4]
def baseStart_1864627 : Nat := 118140960795 + 1864627 * 2 ^ 59
def prefixEnd_1864627 : Nat := 4983230072969 + 3 ^ 40 * 1864627 * 2
def baseEnd_1864627 : Nat := 425533285489413943105441

theorem tailTrace_1864627 : CollatzResearch.WordTrace tailWord_1864627 prefixEnd_1864627 425533285489413943105441 := by
  unfold tailWord_1864627
  simp only [CollatzResearch.WordTrace]
  refine ⟨68008533815782306783376135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45339022543854871188917423 68008533815782306783376135)
  ·
    refine ⟨102012800723673460175064203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68008533815782306783376135 102012800723673460175064203)
    ·
      refine ⟨153019201085510190262596305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102012800723673460175064203 153019201085510190262596305)
      ·
        refine ⟨114764400814132642696947229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153019201085510190262596305 114764400814132642696947229)
        ·
          refine ⟨43036650305299741011355211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114764400814132642696947229 43036650305299741011355211)
          ·
            refine ⟨64554975457949611517032817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43036650305299741011355211 64554975457949611517032817)
            ·
              refine ⟨48416231593462208637774613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64554975457949611517032817 48416231593462208637774613)
              ·
                refine ⟨2269510855943541029895685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48416231593462208637774613 2269510855943541029895685)
                ·
                  refine ⟨425533285489413943105441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2269510855943541029895685 425533285489413943105441)
                  ·
                    rfl

theorem cell21_1864627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 6, 4].length) (baseStart_1864627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864627 prefixEnd_1864627 := by exact prefixLift 1864627
  have htrace : WordTrace (prefixWord ++ tailWord_1864627) baseStart_1864627 baseEnd_1864627 := by
    simpa [prefixWord, tailWord_1864627, baseEnd_1864627] using wordTrace_append hprefix tailTrace_1864627
  have hstable : (prefixWord ++ tailWord_1864627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864627).length < 2 ^ (prefixWord ++ tailWord_1864627).sum := by decide
  have hdescent : baseEnd_1864627 < baseStart_1864627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864689 : List Nat := [1, 2, 2, 2, 4, 1, 3, 1, 5]
def baseStart_1864689 : Nat := 118140960795 + 1864689 * 2 ^ 59
def prefixEnd_1864689 : Nat := 4983230072969 + 3 ^ 40 * 1864689 * 2
def baseEnd_1864689 : Nat := 425547434734115613071981

theorem tailTrace_1864689 : CollatzResearch.WordTrace tailWord_1864689 prefixEnd_1864689 425547434734115613071981 := by
  unfold tailWord_1864689
  simp only [CollatzResearch.WordTrace]
  refine ⟨68010795141557691372133121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45340530094371794248088747 68010795141557691372133121)
  ·
    refine ⟨51008096356168268529099841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68010795141557691372133121 51008096356168268529099841)
    ·
      refine ⟨38256072267126201396824881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51008096356168268529099841 38256072267126201396824881)
      ·
        refine ⟨28692054200344651047618661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38256072267126201396824881 28692054200344651047618661)
        ·
          refine ⟨5379760162564622071428499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28692054200344651047618661 5379760162564622071428499)
          ·
            refine ⟨8069640243846933107142749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5379760162564622071428499 8069640243846933107142749)
            ·
              refine ⟨3026115091442599915178531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8069640243846933107142749 3026115091442599915178531)
              ·
                refine ⟨4539172637163899872767797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3026115091442599915178531 4539172637163899872767797)
                ·
                  refine ⟨425547434734115613071981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4539172637163899872767797 425547434734115613071981)
                  ·
                    rfl

theorem cell21_1864689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_1864689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864689 prefixEnd_1864689 := by exact prefixLift 1864689
  have htrace : WordTrace (prefixWord ++ tailWord_1864689) baseStart_1864689 baseEnd_1864689 := by
    simpa [prefixWord, tailWord_1864689, baseEnd_1864689] using wordTrace_append hprefix tailTrace_1864689
  have hstable : (prefixWord ++ tailWord_1864689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864689).length < 2 ^ (prefixWord ++ tailWord_1864689).sum := by decide
  have hdescent : baseEnd_1864689 < baseStart_1864689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864740 : List Nat := [2, 3, 1, 4, 1, 3, 2, 2, 3]
def baseStart_1864740 : Nat := 118140960795 + 1864740 * 2 ^ 59
def prefixEnd_1864740 : Nat := 4983230072969 + 3 ^ 40 * 1864740 * 2
def baseEnd_1864740 : Nat := 425559073628950857721877

theorem tailTrace_1864740 : CollatzResearch.WordTrace tailWord_1864740 prefixEnd_1864740 425559073628950857721877 := by
  unfold tailWord_1864740
  simp only [CollatzResearch.WordTrace]
  refine ⟨34006327632186463541119837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45341770176248618054826449 34006327632186463541119837)
  ·
    refine ⟨12752372862069923827919939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34006327632186463541119837 12752372862069923827919939)
    ·
      refine ⟨19128559293104885741879909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12752372862069923827919939 19128559293104885741879909)
      ·
        refine ⟨3586604867457166076602483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19128559293104885741879909 3586604867457166076602483)
        ·
          refine ⟨5379907301185749114903725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3586604867457166076602483 5379907301185749114903725)
          ·
            refine ⟨2017465237944655918088897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5379907301185749114903725 2017465237944655918088897)
            ·
              refine ⟨1513098928458491938566673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2017465237944655918088897 1513098928458491938566673)
              ·
                refine ⟨1134824196343868953925005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1513098928458491938566673 1134824196343868953925005)
                ·
                  refine ⟨425559073628950857721877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1134824196343868953925005 425559073628950857721877)
                  ·
                    rfl

theorem cell21_1864740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_1864740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864740 prefixEnd_1864740 := by exact prefixLift 1864740
  have htrace : WordTrace (prefixWord ++ tailWord_1864740) baseStart_1864740 baseEnd_1864740 := by
    simpa [prefixWord, tailWord_1864740, baseEnd_1864740] using wordTrace_append hprefix tailTrace_1864740
  have hstable : (prefixWord ++ tailWord_1864740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864740).length < 2 ^ (prefixWord ++ tailWord_1864740).sum := by decide
  have hdescent : baseEnd_1864740 < baseStart_1864740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864748 : List Nat := [2, 2, 1, 1, 1, 2, 4, 3, 5]
def baseStart_1864748 : Nat := 118140960795 + 1864748 * 2 ^ 59
def prefixEnd_1864748 : Nat := 4983230072969 + 3 ^ 40 * 1864748 * 2
def baseEnd_1864748 : Nat := 425560899337944621588527

theorem tailTrace_1864748 : CollatzResearch.WordTrace tailWord_1864748 prefixEnd_1864748 425560899337944621588527 := by
  unfold tailWord_1864748
  simp only [CollatzResearch.WordTrace]
  refine ⟨34006473524171972224265449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45341964698895962965687265 34006473524171972224265449)
  ·
    refine ⟨25504855143128979168199087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34006473524171972224265449 25504855143128979168199087)
    ·
      refine ⟨38257282714693468752298631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25504855143128979168199087 38257282714693468752298631)
      ·
        refine ⟨57385924072040203128447947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38257282714693468752298631 57385924072040203128447947)
        ·
          refine ⟨86078886108060304692671921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57385924072040203128447947 86078886108060304692671921)
          ·
            refine ⟨64559164581045228519503941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86078886108060304692671921 64559164581045228519503941)
            ·
              refine ⟨12104843358945980347406989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64559164581045228519503941 12104843358945980347406989)
              ·
                refine ⟨4539316259604742630277621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12104843358945980347406989 4539316259604742630277621)
                ·
                  refine ⟨425560899337944621588527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4539316259604742630277621 425560899337944621588527)
                  ·
                    rfl

theorem cell21_1864748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_1864748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864748 prefixEnd_1864748 := by exact prefixLift 1864748
  have htrace : WordTrace (prefixWord ++ tailWord_1864748) baseStart_1864748 baseEnd_1864748 := by
    simpa [prefixWord, tailWord_1864748, baseEnd_1864748] using wordTrace_append hprefix tailTrace_1864748
  have hstable : (prefixWord ++ tailWord_1864748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864748).length < 2 ^ (prefixWord ++ tailWord_1864748).sum := by decide
  have hdescent : baseEnd_1864748 < baseStart_1864748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864765 : List Nat := [1, 4, 1, 3, 1, 3, 1, 2, 5]
def baseStart_1864765 : Nat := 118140960795 + 1864765 * 2 ^ 59
def prefixEnd_1864765 : Nat := 4983230072969 + 3 ^ 40 * 1864765 * 2
def baseEnd_1864765 : Nat := 425564778969556369805159

theorem tailTrace_1864765 : CollatzResearch.WordTrace tailWord_1864765 prefixEnd_1864765 425564778969556369805159 := by
  unfold tailWord_1864765
  simp only [CollatzResearch.WordTrace]
  refine ⟨68013567089282356351899749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45342378059521570901266499 68013567089282356351899749)
  ·
    refine ⟨12752543829240441815981203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68013567089282356351899749 12752543829240441815981203)
    ·
      refine ⟨19128815743860662723971805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12752543829240441815981203 19128815743860662723971805)
      ·
        refine ⟨7173305903947748521489427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19128815743860662723971805 7173305903947748521489427)
        ·
          refine ⟨10759958855921622782234141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7173305903947748521489427 10759958855921622782234141)
          ·
            refine ⟨4034984570970608543337803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10759958855921622782234141 4034984570970608543337803)
            ·
              refine ⟨6052476856455912815006705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4034984570970608543337803 6052476856455912815006705)
              ·
                refine ⟨4539357642341934611255029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6052476856455912815006705 4539357642341934611255029)
                ·
                  refine ⟨425564778969556369805159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4539357642341934611255029 425564778969556369805159)
                  ·
                    rfl

theorem cell21_1864765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_1864765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864765 prefixEnd_1864765 := by exact prefixLift 1864765
  have htrace : WordTrace (prefixWord ++ tailWord_1864765) baseStart_1864765 baseEnd_1864765 := by
    simpa [prefixWord, tailWord_1864765, baseEnd_1864765] using wordTrace_append hprefix tailTrace_1864765
  have hstable : (prefixWord ++ tailWord_1864765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864765).length < 2 ^ (prefixWord ++ tailWord_1864765).sum := by decide
  have hdescent : baseEnd_1864765 < baseStart_1864765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864782 : List Nat := [4, 1, 1, 1, 1, 3, 4, 3, 3]
def baseStart_1864782 : Nat := 118140960795 + 1864782 * 2 ^ 59
def prefixEnd_1864782 : Nat := 4983230072969 + 3 ^ 40 * 1864782 * 2
def baseEnd_1864782 : Nat := 425568658601168118021791

theorem tailTrace_1864782 : CollatzResearch.WordTrace tailWord_1864782 prefixEnd_1864782 425568658601168118021791 := by
  unfold tailWord_1864782
  simp only [CollatzResearch.WordTrace]
  refine ⟨8501773391277596031908575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45342791420147178836845733 8501773391277596031908575)
  ·
    refine ⟨12752660086916394047862863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8501773391277596031908575 12752660086916394047862863)
    ·
      refine ⟨19128990130374591071794295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12752660086916394047862863 19128990130374591071794295)
      ·
        refine ⟨28693485195561886607691443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19128990130374591071794295 28693485195561886607691443)
        ·
          refine ⟨43040227793342829911537165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28693485195561886607691443 43040227793342829911537165)
          ·
            refine ⟨16140085422503561216826437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43040227793342829911537165 16140085422503561216826437)
            ·
              refine ⟨3026266016719417728154957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16140085422503561216826437 3026266016719417728154957)
              ·
                refine ⟨1134849756269781648058109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3026266016719417728154957 1134849756269781648058109)
                ·
                  refine ⟨425568658601168118021791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1134849756269781648058109 425568658601168118021791)
                  ·
                    rfl

theorem cell21_1864782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_1864782 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864782 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864782 prefixEnd_1864782 := by exact prefixLift 1864782
  have htrace : WordTrace (prefixWord ++ tailWord_1864782) baseStart_1864782 baseEnd_1864782 := by
    simpa [prefixWord, tailWord_1864782, baseEnd_1864782] using wordTrace_append hprefix tailTrace_1864782
  have hstable : (prefixWord ++ tailWord_1864782).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864782).length < 2 ^ (prefixWord ++ tailWord_1864782).sum := by decide
  have hdescent : baseEnd_1864782 < baseStart_1864782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864813 : List Nat := [1, 5, 1, 1, 2, 3, 3, 1, 4]
def baseStart_1864813 : Nat := 118140960795 + 1864813 * 2 ^ 59
def prefixEnd_1864813 : Nat := 4983230072969 + 3 ^ 40 * 1864813 * 2
def baseEnd_1864813 : Nat := 425575733223518953005061

theorem tailTrace_1864813 : CollatzResearch.WordTrace tailWord_1864813 prefixEnd_1864813 425575733223518953005061 := by
  unfold tailWord_1864813
  simp only [CollatzResearch.WordTrace]
  refine ⟨68015317793108460549647093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45343545195405640366431395 68015317793108460549647093)
  ·
    refine ⟨6376436043103918176529415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68015317793108460549647093 6376436043103918176529415)
    ·
      refine ⟨9564654064655877264794123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6376436043103918176529415 9564654064655877264794123)
      ·
        refine ⟨14346981096983815897191185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9564654064655877264794123 14346981096983815897191185)
        ·
          refine ⟨10760235822737861922893389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14346981096983815897191185 10760235822737861922893389)
          ·
            refine ⟨4035088433526698221085021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10760235822737861922893389 4035088433526698221085021)
            ·
              refine ⟨1513158162572511832906883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4035088433526698221085021 1513158162572511832906883)
              ·
                refine ⟨2269737243858767749360325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1513158162572511832906883 2269737243858767749360325)
                ·
                  refine ⟨425575733223518953005061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2269737243858767749360325 425575733223518953005061)
                  ·
                    rfl

theorem cell21_1864813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_1864813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864813 prefixEnd_1864813 := by exact prefixLift 1864813
  have htrace : WordTrace (prefixWord ++ tailWord_1864813) baseStart_1864813 baseEnd_1864813 := by
    simpa [prefixWord, tailWord_1864813, baseEnd_1864813] using wordTrace_append hprefix tailTrace_1864813
  have hstable : (prefixWord ++ tailWord_1864813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864813).length < 2 ^ (prefixWord ++ tailWord_1864813).sum := by decide
  have hdescent : baseEnd_1864813 < baseStart_1864813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864824 : List Nat := [2, 1, 2, 1, 1, 1, 6, 2, 5]
def baseStart_1864824 : Nat := 118140960795 + 1864824 * 2 ^ 59
def prefixEnd_1864824 : Nat := 4983230072969 + 3 ^ 40 * 1864824 * 2
def baseEnd_1864824 : Nat := 425578243573385378321705

theorem tailTrace_1864824 : CollatzResearch.WordTrace tailWord_1864824 prefixEnd_1864824 425578243573385378321705 := by
  unfold tailWord_1864824
  simp only [CollatzResearch.WordTrace]
  refine ⟨34007859498034304714148763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45343812664045739618865017 34007859498034304714148763)
  ·
    refine ⟨51011789247051457071223145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34007859498034304714148763 51011789247051457071223145)
    ·
      refine ⟨38258841935288592803417359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51011789247051457071223145 38258841935288592803417359)
      ·
        refine ⟨57388262902932889205126039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38258841935288592803417359 57388262902932889205126039)
        ·
          refine ⟨86082394354399333807689059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57388262902932889205126039 86082394354399333807689059)
          ·
            refine ⟨129123591531599000711533589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86082394354399333807689059 129123591531599000711533589)
            ·
              refine ⟨6052668353043703158353137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129123591531599000711533589 6052668353043703158353137)
              ·
                refine ⟨4539501264782777368764853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6052668353043703158353137 4539501264782777368764853)
                ·
                  refine ⟨425578243573385378321705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4539501264782777368764853 425578243573385378321705)
                  ·
                    rfl

theorem cell21_1864824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_1864824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864824 prefixEnd_1864824 := by exact prefixLift 1864824
  have htrace : WordTrace (prefixWord ++ tailWord_1864824) baseStart_1864824 baseEnd_1864824 := by
    simpa [prefixWord, tailWord_1864824, baseEnd_1864824] using wordTrace_append hprefix tailTrace_1864824
  have hstable : (prefixWord ++ tailWord_1864824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864824).length < 2 ^ (prefixWord ++ tailWord_1864824).sum := by decide
  have hdescent : baseEnd_1864824 < baseStart_1864824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864855 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 6]
def baseStart_1864855 : Nat := 118140960795 + 1864855 * 2 ^ 59
def prefixEnd_1864855 : Nat := 4983230072969 + 3 ^ 40 * 1864855 * 2
def baseEnd_1864855 : Nat := 425585318195736213304975

theorem tailTrace_1864855 : CollatzResearch.WordTrace tailWord_1864855 prefixEnd_1864855 425585318195736213304975 := by
  unfold tailWord_1864855
  simp only [CollatzResearch.WordTrace]
  refine ⟨68016849658956301722676019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45344566439304201148450679 68016849658956301722676019)
  ·
    refine ⟨102025274488434452584014029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68016849658956301722676019 102025274488434452584014029)
    ·
      refine ⟨38259477933162919719005261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102025274488434452584014029 38259477933162919719005261)
      ·
        refine ⟨14347304224936094894626973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38259477933162919719005261 14347304224936094894626973)
        ·
          refine ⟨5380239084351035585485115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14347304224936094894626973 5380239084351035585485115)
          ·
            refine ⟨8070358626526553378227673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5380239084351035585485115 8070358626526553378227673)
            ·
              refine ⟨6052768969894915033670755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8070358626526553378227673 6052768969894915033670755)
              ·
                refine ⟨9079153454842372550506133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6052768969894915033670755 9079153454842372550506133)
                ·
                  refine ⟨425585318195736213304975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9079153454842372550506133 425585318195736213304975)
                  ·
                    rfl

theorem cell21_1864855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 6].length) (baseStart_1864855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864855 prefixEnd_1864855 := by exact prefixLift 1864855
  have htrace : WordTrace (prefixWord ++ tailWord_1864855) baseStart_1864855 baseEnd_1864855 := by
    simpa [prefixWord, tailWord_1864855, baseEnd_1864855] using wordTrace_append hprefix tailTrace_1864855
  have hstable : (prefixWord ++ tailWord_1864855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864855).length < 2 ^ (prefixWord ++ tailWord_1864855).sum := by decide
  have hdescent : baseEnd_1864855 < baseStart_1864855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864858 : List Nat := [3, 1, 1, 5, 1, 3, 1, 1, 5]
def baseStart_1864858 : Nat := 118140960795 + 1864858 * 2 ^ 59
def prefixEnd_1864858 : Nat := 4983230072969 + 3 ^ 40 * 1864858 * 2
def baseEnd_1864858 : Nat := 425586002836608874754969

theorem tailTrace_1864858 : CollatzResearch.WordTrace tailWord_1864858 prefixEnd_1864858 425586002836608874754969 := by
  unfold tailWord_1864858
  simp only [CollatzResearch.WordTrace]
  refine ⟨17004239769486358308758807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45344639385296955490023485 17004239769486358308758807)
  ·
    refine ⟨25506359654229537463138211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17004239769486358308758807 25506359654229537463138211)
    ·
      refine ⟨38259539481344306194707317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25506359654229537463138211 38259539481344306194707317)
      ·
        refine ⟨3586831826376028705753811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38259539481344306194707317 3586831826376028705753811)
        ·
          refine ⟨5380247739564043058630717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3586831826376028705753811 5380247739564043058630717)
          ·
            refine ⟨2017592902336516146986519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5380247739564043058630717 2017592902336516146986519)
            ·
              refine ⟨3026389353504774220479779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2017592902336516146986519 3026389353504774220479779)
              ·
                refine ⟨4539584030257161330719669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3026389353504774220479779 4539584030257161330719669)
                ·
                  refine ⟨425586002836608874754969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4539584030257161330719669 425586002836608874754969)
                  ·
                    rfl

theorem cell21_1864858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_1864858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864858 prefixEnd_1864858 := by exact prefixLift 1864858
  have htrace : WordTrace (prefixWord ++ tailWord_1864858) baseStart_1864858 baseEnd_1864858 := by
    simpa [prefixWord, tailWord_1864858, baseEnd_1864858] using wordTrace_append hprefix tailTrace_1864858
  have hstable : (prefixWord ++ tailWord_1864858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864858).length < 2 ^ (prefixWord ++ tailWord_1864858).sum := by decide
  have hdescent : baseEnd_1864858 < baseStart_1864858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1864869 : List Nat := [1, 3, 1, 2, 1, 4, 1, 8]
def baseStart_1864869 : Nat := 118140960795 + 1864869 * 2 ^ 59
def prefixEnd_1864869 : Nat := 4983230072969 + 3 ^ 40 * 1864869 * 2
def baseEnd_1864869 : Nat := 141862837728825100023871

theorem tailTrace_1864869 : CollatzResearch.WordTrace tailWord_1864869 prefixEnd_1864869 141862837728825100023871 := by
  unfold tailWord_1864869
  simp only [CollatzResearch.WordTrace]
  refine ⟨68017360280905582113685661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45344906853937054742457107 68017360280905582113685661)
  ·
    refine ⟨25506510105339593292632123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68017360280905582113685661 25506510105339593292632123)
    ·
      refine ⟨38259765158009389938948185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25506510105339593292632123 38259765158009389938948185)
      ·
        refine ⟨28694823868507042454211139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38259765158009389938948185 28694823868507042454211139)
        ·
          refine ⟨43042235802760563681316709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28694823868507042454211139 43042235802760563681316709)
          ·
            refine ⟨8070419213017605690246883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43042235802760563681316709 8070419213017605690246883)
            ·
              refine ⟨12105628819526408535370325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8070419213017605690246883 12105628819526408535370325)
              ·
                refine ⟨141862837728825100023871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12105628819526408535370325 141862837728825100023871)
                ·
                  rfl

theorem cell21_1864869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 8].length) (baseStart_1864869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1864869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1864869 prefixEnd_1864869 := by exact prefixLift 1864869
  have htrace : WordTrace (prefixWord ++ tailWord_1864869) baseStart_1864869 baseEnd_1864869 := by
    simpa [prefixWord, tailWord_1864869, baseEnd_1864869] using wordTrace_append hprefix tailTrace_1864869
  have hstable : (prefixWord ++ tailWord_1864869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1864869).length < 2 ^ (prefixWord ++ tailWord_1864869).sum := by decide
  have hdescent : baseEnd_1864869 < baseStart_1864869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1864869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865010 : List Nat := [3, 2, 1, 1, 4, 1, 3, 3, 3]
def baseStart_1865010 : Nat := 118140960795 + 1865010 * 2 ^ 59
def prefixEnd_1865010 : Nat := 4983230072969 + 3 ^ 40 * 1865010 * 2
def baseEnd_1865010 : Nat := 425620691307490388221325

theorem tailTrace_1865010 : CollatzResearch.WordTrace tailWord_1865010 prefixEnd_1865010 425620691307490388221325 := by
  unfold tailWord_1865010
  simp only [CollatzResearch.WordTrace]
  refine ⟨17005625743348690798642121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45348335315596508796378989 17005625743348690798642121)
  ·
    refine ⟨12754219307511518098981591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17005625743348690798642121 12754219307511518098981591)
    ·
      refine ⟨19131328961267277148472387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12754219307511518098981591 19131328961267277148472387)
      ·
        refine ⟨28696993441900915722708581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19131328961267277148472387 28696993441900915722708581)
        ·
          refine ⟨5380686270356421698007859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28696993441900915722708581 5380686270356421698007859)
          ·
            refine ⟨8071029405534632547011789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5380686270356421698007859 8071029405534632547011789)
            ·
              refine ⟨3026636027075487205129421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8071029405534632547011789 3026636027075487205129421)
              ·
                refine ⟨1134988510153307701923533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3026636027075487205129421 1134988510153307701923533)
                ·
                  refine ⟨425620691307490388221325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1134988510153307701923533 425620691307490388221325)
                  ·
                    rfl

theorem cell21_1865010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 3].length) (baseStart_1865010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865010 prefixEnd_1865010 := by exact prefixLift 1865010
  have htrace : WordTrace (prefixWord ++ tailWord_1865010) baseStart_1865010 baseEnd_1865010 := by
    simpa [prefixWord, tailWord_1865010, baseEnd_1865010] using wordTrace_append hprefix tailTrace_1865010
  have hstable : (prefixWord ++ tailWord_1865010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865010).length < 2 ^ (prefixWord ++ tailWord_1865010).sum := by decide
  have hdescent : baseEnd_1865010 < baseStart_1865010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865083 : List Nat := [1, 1, 1, 1, 1, 6, 4, 2, 4]
def baseStart_1865083 : Nat := 118140960795 + 1865083 * 2 ^ 59
def prefixEnd_1865083 : Nat := 4983230072969 + 3 ^ 40 * 1865083 * 2
def baseEnd_1865083 : Nat := 425637350902058483504509

theorem tailTrace_1865083 : CollatzResearch.WordTrace tailWord_1865083 prefixEnd_1865083 425637350902058483504509 := by
  unfold tailWord_1865083
  simp only [CollatzResearch.WordTrace]
  refine ⟨68025165502130296661975903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45350110334753531107983935 68025165502130296661975903)
  ·
    refine ⟨102037748253195444992963855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68025165502130296661975903 102037748253195444992963855)
    ·
      refine ⟨153056622379793167489445783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102037748253195444992963855 153056622379793167489445783)
      ·
        refine ⟨229584933569689751234168675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153056622379793167489445783 229584933569689751234168675)
        ·
          refine ⟨344377400354534626851253013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229584933569689751234168675 344377400354534626851253013)
          ·
            refine ⟨16142690641618810633652485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 344377400354534626851253013 16142690641618810633652485)
            ·
              refine ⟨3026754495303526993809841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16142690641618810633652485 3026754495303526993809841)
              ·
                refine ⟨2270065871477645245357381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3026754495303526993809841 2270065871477645245357381)
                ·
                  refine ⟨425637350902058483504509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2270065871477645245357381 425637350902058483504509)
                  ·
                    rfl

theorem cell21_1865083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 4].length) (baseStart_1865083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865083 prefixEnd_1865083 := by exact prefixLift 1865083
  have htrace : WordTrace (prefixWord ++ tailWord_1865083) baseStart_1865083 baseEnd_1865083 := by
    simpa [prefixWord, tailWord_1865083, baseEnd_1865083] using wordTrace_append hprefix tailTrace_1865083
  have hstable : (prefixWord ++ tailWord_1865083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865083).length < 2 ^ (prefixWord ++ tailWord_1865083).sum := by decide
  have hdescent : baseEnd_1865083 < baseStart_1865083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865114 : List Nat := [3, 1, 1, 4, 1, 1, 5, 5]
def baseStart_1865114 : Nat := 118140960795 + 1865114 * 2 ^ 59
def prefixEnd_1865114 : Nat := 4983230072969 + 3 ^ 40 * 1865114 * 2
def baseEnd_1865114 : Nat := 141881475174803106162593

theorem tailTrace_1865114 : CollatzResearch.WordTrace tailWord_1865114 prefixEnd_1865114 141881475174803106162593 := by
  unfold tailWord_1865114
  simp only [CollatzResearch.WordTrace]
  refine ⟨17006574041254497239088599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45350864110011992637569597 17006574041254497239088599)
  ·
    refine ⟨25509861061881745858632899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17006574041254497239088599 25509861061881745858632899)
    ·
      refine ⟨38264791592822618787949349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25509861061881745858632899 38264791592822618787949349)
      ·
        refine ⟨7174648423654241022740503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38264791592822618787949349 7174648423654241022740503)
        ·
          refine ⟨10761972635481361534110755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7174648423654241022740503 10761972635481361534110755)
          ·
            refine ⟨16142958953222042301166133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10761972635481361534110755 16142958953222042301166133)
            ·
              refine ⟨1513402401864566465734325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16142958953222042301166133 1513402401864566465734325)
              ·
                refine ⟨141881475174803106162593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1513402401864566465734325 141881475174803106162593)
                ·
                  rfl

theorem cell21_1865114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_1865114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865114 prefixEnd_1865114 := by exact prefixLift 1865114
  have htrace : WordTrace (prefixWord ++ tailWord_1865114) baseStart_1865114 baseEnd_1865114 := by
    simpa [prefixWord, tailWord_1865114, baseEnd_1865114] using wordTrace_append hprefix tailTrace_1865114
  have hstable : (prefixWord ++ tailWord_1865114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865114).length < 2 ^ (prefixWord ++ tailWord_1865114).sum := by decide
  have hdescent : baseEnd_1865114 < baseStart_1865114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865145 : List Nat := [1, 2, 1, 4, 4, 1, 2, 1, 5]
def baseStart_1865145 : Nat := 118140960795 + 1865145 * 2 ^ 59
def prefixEnd_1865145 : Nat := 4983230072969 + 3 ^ 40 * 1865145 * 2
def baseEnd_1865145 : Nat := 425651500146760153471049

theorem tailTrace_1865145 : CollatzResearch.WordTrace tailWord_1865145 prefixEnd_1865145 425651500146760153471049 := by
  unfold tailWord_1865145
  simp only [CollatzResearch.WordTrace]
  refine ⟨68027426827905681250732889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45351617885270454167155259 68027426827905681250732889)
  ·
    refine ⟨51020570120929260938049667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68027426827905681250732889 51020570120929260938049667)
    ·
      refine ⟨76530855181393891407074501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51020570120929260938049667 76530855181393891407074501)
      ·
        refine ⟨14349535346511354638826469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76530855181393891407074501 14349535346511354638826469)
        ·
          refine ⟨2690537877470878994779963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14349535346511354638826469 2690537877470878994779963)
          ·
            refine ⟨4035806816206318492169945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2690537877470878994779963 4035806816206318492169945)
            ·
              refine ⟨3026855112154738869127459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4035806816206318492169945 3026855112154738869127459)
              ·
                refine ⟨4540282668232108303691189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3026855112154738869127459 4540282668232108303691189)
                ·
                  refine ⟨425651500146760153471049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4540282668232108303691189 425651500146760153471049)
                  ·
                    rfl

theorem cell21_1865145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_1865145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865145 prefixEnd_1865145 := by exact prefixLift 1865145
  have htrace : WordTrace (prefixWord ++ tailWord_1865145) baseStart_1865145 baseEnd_1865145 := by
    simpa [prefixWord, tailWord_1865145, baseEnd_1865145] using wordTrace_append hprefix tailTrace_1865145
  have hstable : (prefixWord ++ tailWord_1865145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865145).length < 2 ^ (prefixWord ++ tailWord_1865145).sum := by decide
  have hdescent : baseEnd_1865145 < baseStart_1865145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865173 : List Nat := [1, 3, 2, 3, 1, 1, 3, 7]
def baseStart_1865173 : Nat := 118140960795 + 1865173 * 2 ^ 59
def prefixEnd_1865173 : Nat := 4983230072969 + 3 ^ 40 * 1865173 * 2
def baseEnd_1865173 : Nat := 141885963376079442334775

theorem tailTrace_1865173 : CollatzResearch.WordTrace tailWord_1865173 prefixEnd_1865173 141885963376079442334775 := by
  unfold tailWord_1865173
  simp only [CollatzResearch.WordTrace]
  refine ⟨68028448071804242032752173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45352298714536161355168115 68028448071804242032752173)
  ·
    refine ⟨25510668026926590762282065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68028448071804242032752173 25510668026926590762282065)
    ·
      refine ⟨19133001020194943071711549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25510668026926590762282065 19133001020194943071711549)
      ·
        refine ⟨7174875382573103651891831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19133001020194943071711549 7174875382573103651891831)
        ·
          refine ⟨10762313073859655477837747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7174875382573103651891831 10762313073859655477837747)
          ·
            refine ⟨16143469610789483216756621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10762313073859655477837747 16143469610789483216756621)
            ·
              refine ⟨6053801104046056206283733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16143469610789483216756621 6053801104046056206283733)
              ·
                refine ⟨141885963376079442334775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6053801104046056206283733 141885963376079442334775)
                ·
                  rfl

theorem cell21_1865173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 7].length) (baseStart_1865173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865173 prefixEnd_1865173 := by exact prefixLift 1865173
  have htrace : WordTrace (prefixWord ++ tailWord_1865173) baseStart_1865173 baseEnd_1865173 := by
    simpa [prefixWord, tailWord_1865173, baseEnd_1865173] using wordTrace_append hprefix tailTrace_1865173
  have hstable : (prefixWord ++ tailWord_1865173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865173).length < 2 ^ (prefixWord ++ tailWord_1865173).sum := by decide
  have hdescent : baseEnd_1865173 < baseStart_1865173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865294 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_1865294 : Nat := 118140960795 + 1865294 * 2 ^ 59
def prefixEnd_1865294 : Nat := 4983230072969 + 3 ^ 40 * 1865294 * 2
def baseEnd_1865294 : Nat := 425685503976769005487411

theorem tailTrace_1865294 : CollatzResearch.WordTrace tailWord_1865294 prefixEnd_1865294 425685503976769005487411 := by
  unfold tailWord_1865294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8504107663045734962238367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45355240869577253131937957 8504107663045734962238367)
  ·
    refine ⟨12756161494568602443357551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8504107663045734962238367 12756161494568602443357551)
    ·
      refine ⟨19134242241852903665036327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12756161494568602443357551 19134242241852903665036327)
      ·
        refine ⟨28701363362779355497554491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19134242241852903665036327 28701363362779355497554491)
        ·
          refine ⟨43052045044169033246331737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28701363362779355497554491 43052045044169033246331737)
          ·
            refine ⟨32289033783126774934748803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43052045044169033246331737 32289033783126774934748803)
            ·
              refine ⟨48433550674690162402123205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32289033783126774934748803 48433550674690162402123205)
              ·
                refine ⟨9081290751504405450398101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48433550674690162402123205 9081290751504405450398101)
                ·
                  refine ⟨425685503976769005487411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9081290751504405450398101 425685503976769005487411)
                  ·
                    rfl

theorem cell21_1865294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_1865294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865294 prefixEnd_1865294 := by exact prefixLift 1865294
  have htrace : WordTrace (prefixWord ++ tailWord_1865294) baseStart_1865294 baseEnd_1865294 := by
    simpa [prefixWord, tailWord_1865294, baseEnd_1865294] using wordTrace_append hprefix tailTrace_1865294
  have hstable : (prefixWord ++ tailWord_1865294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865294).length < 2 ^ (prefixWord ++ tailWord_1865294).sum := by decide
  have hdescent : baseEnd_1865294 < baseStart_1865294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865297 : List Nat := [1, 2, 2, 1, 3, 2, 4, 3, 3]
def baseStart_1865297 : Nat := 118140960795 + 1865297 * 2 ^ 59
def prefixEnd_1865297 : Nat := 4983230072969 + 3 ^ 40 * 1865297 * 2
def baseEnd_1865297 : Nat := 425686188617641666937405

theorem tailTrace_1865297 : CollatzResearch.WordTrace tailWord_1865297 prefixEnd_1865297 425686188617641666937405 := by
  unfold tailWord_1865297
  simp only [CollatzResearch.WordTrace]
  refine ⟨68032970723355011210266145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45355313815570007473510763 68032970723355011210266145)
  ·
    refine ⟨51024728042516258407699609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68032970723355011210266145 51024728042516258407699609)
    ·
      refine ⟨38268546031887193805774707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51024728042516258407699609 38268546031887193805774707)
      ·
        refine ⟨57402819047830790708662061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38268546031887193805774707 57402819047830790708662061)
        ·
          refine ⟨21526057142936546515748273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57402819047830790708662061 21526057142936546515748273)
          ·
            refine ⟨16144542857202409886811205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21526057142936546515748273 16144542857202409886811205)
            ·
              refine ⟨3027101785725451853777101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16144542857202409886811205 3027101785725451853777101)
              ·
                refine ⟨1135163169647044445166413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3027101785725451853777101 1135163169647044445166413)
                ·
                  refine ⟨425686188617641666937405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1135163169647044445166413 425686188617641666937405)
                  ·
                    rfl

theorem cell21_1865297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 3].length) (baseStart_1865297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865297 prefixEnd_1865297 := by exact prefixLift 1865297
  have htrace : WordTrace (prefixWord ++ tailWord_1865297) baseStart_1865297 baseEnd_1865297 := by
    simpa [prefixWord, tailWord_1865297, baseEnd_1865297] using wordTrace_append hprefix tailTrace_1865297
  have hstable : (prefixWord ++ tailWord_1865297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865297).length < 2 ^ (prefixWord ++ tailWord_1865297).sum := by decide
  have hdescent : baseEnd_1865297 < baseStart_1865297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865328 : List Nat := [2, 1, 1, 1, 6, 2, 3, 1, 4]
def baseStart_1865328 : Nat := 118140960795 + 1865328 * 2 ^ 59
def prefixEnd_1865328 : Nat := 4983230072969 + 3 ^ 40 * 1865328 * 2
def baseEnd_1865328 : Nat := 425693263239992501920675

theorem tailTrace_1865328 : CollatzResearch.WordTrace tailWord_1865328 prefixEnd_1865328 425693263239992501920675 := by
  unfold tailWord_1865328
  simp only [CollatzResearch.WordTrace]
  refine ⟨34017050693121351752322319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45356067590828469003096425 34017050693121351752322319)
  ·
    refine ⟨51025576039682027628483479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34017050693121351752322319 51025576039682027628483479)
    ·
      refine ⟨76538364059523041442725219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51025576039682027628483479 76538364059523041442725219)
      ·
        refine ⟨114807546089284562164087829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76538364059523041442725219 114807546089284562164087829)
        ·
          refine ⟨5381603722935213851441617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114807546089284562164087829 5381603722935213851441617)
          ·
            refine ⟨4036202792201410388581213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5381603722935213851441617 4036202792201410388581213)
            ·
              refine ⟨1513576047075528895717955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4036202792201410388581213 1513576047075528895717955)
              ·
                refine ⟨2270364070613293343576933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1513576047075528895717955 2270364070613293343576933)
                ·
                  refine ⟨425693263239992501920675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2270364070613293343576933 425693263239992501920675)
                  ·
                    rfl

theorem cell21_1865328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 4].length) (baseStart_1865328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865328 prefixEnd_1865328 := by exact prefixLift 1865328
  have htrace : WordTrace (prefixWord ++ tailWord_1865328) baseStart_1865328 baseEnd_1865328 := by
    simpa [prefixWord, tailWord_1865328, baseEnd_1865328] using wordTrace_append hprefix tailTrace_1865328
  have hstable : (prefixWord ++ tailWord_1865328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865328).length < 2 ^ (prefixWord ++ tailWord_1865328).sum := by decide
  have hdescent : baseEnd_1865328 < baseStart_1865328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865339 : List Nat := [1, 1, 1, 1, 1, 4, 3, 4, 5]
def baseStart_1865339 : Nat := 118140960795 + 1865339 * 2 ^ 59
def prefixEnd_1865339 : Nat := 4983230072969 + 3 ^ 40 * 1865339 * 2
def baseEnd_1865339 : Nat := 425695773589858927237319

theorem tailTrace_1865339 : CollatzResearch.WordTrace tailWord_1865339 prefixEnd_1865339 425695773589858927237319 := by
  unfold tailWord_1865339
  simp only [CollatzResearch.WordTrace]
  refine ⟨68034502589202852383295071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45356335059468568255530047 68034502589202852383295071)
  ·
    refine ⟨102051753883804278574942607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68034502589202852383295071 102051753883804278574942607)
    ·
      refine ⟨153077630825706417862413911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102051753883804278574942607 153077630825706417862413911)
      ·
        refine ⟨229616446238559626793620867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153077630825706417862413911 229616446238559626793620867)
        ·
          refine ⟨344424669357839440190431301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229616446238559626793620867 344424669357839440190431301)
          ·
            refine ⟨64579625504594895035705869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 344424669357839440190431301 64579625504594895035705869)
            ·
              refine ⟨24217359564223085638389701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64579625504594895035705869 24217359564223085638389701)
              ·
                refine ⟨4540754918291828557198069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24217359564223085638389701 4540754918291828557198069)
                ·
                  refine ⟨425695773589858927237319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4540754918291828557198069 425695773589858927237319)
                  ·
                    rfl

theorem cell21_1865339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 5].length) (baseStart_1865339 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865339 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865339 prefixEnd_1865339 := by exact prefixLift 1865339
  have htrace : WordTrace (prefixWord ++ tailWord_1865339) baseStart_1865339 baseEnd_1865339 := by
    simpa [prefixWord, tailWord_1865339, baseEnd_1865339] using wordTrace_append hprefix tailTrace_1865339
  have hstable : (prefixWord ++ tailWord_1865339).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865339).length < 2 ^ (prefixWord ++ tailWord_1865339).sum := by decide
  have hdescent : baseEnd_1865339 < baseStart_1865339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865421 : List Nat := [1, 6, 2, 1, 1, 2, 2, 2, 4]
def baseStart_1865421 : Nat := 118140960795 + 1865421 * 2 ^ 59
def prefixEnd_1865421 : Nat := 4983230072969 + 3 ^ 40 * 1865421 * 2
def baseEnd_1865421 : Nat := 425714487107045006870485

theorem tailTrace_1865421 : CollatzResearch.WordTrace tailWord_1865421 prefixEnd_1865421 425714487107045006870485 := by
  unfold tailWord_1865421
  simp only [CollatzResearch.WordTrace]
  refine ⟨68037493374905780387780117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45358328916603853591853411 68037493374905780387780117)
  ·
    refine ⟨3189257501948708455677193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68037493374905780387780117 3189257501948708455677193)
    ·
      refine ⟨2391943126461531341757895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3189257501948708455677193 2391943126461531341757895)
      ·
        refine ⟨3587914689692297012636843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2391943126461531341757895 3587914689692297012636843)
        ·
          refine ⟨5381872034538445518955265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3587914689692297012636843 5381872034538445518955265)
          ·
            refine ⟨4036404025903834139216449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5381872034538445518955265 4036404025903834139216449)
            ·
              refine ⟨3027303019427875604412337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4036404025903834139216449 3027303019427875604412337)
              ·
                refine ⟨2270477264570906703309253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3027303019427875604412337 2270477264570906703309253)
                ·
                  refine ⟨425714487107045006870485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2270477264570906703309253 425714487107045006870485)
                  ·
                    rfl

theorem cell21_1865421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_1865421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865421 prefixEnd_1865421 := by exact prefixLift 1865421
  have htrace : WordTrace (prefixWord ++ tailWord_1865421) baseStart_1865421 baseEnd_1865421 := by
    simpa [prefixWord, tailWord_1865421, baseEnd_1865421] using wordTrace_append hprefix tailTrace_1865421
  have hstable : (prefixWord ++ tailWord_1865421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865421).length < 2 ^ (prefixWord ++ tailWord_1865421).sum := by decide
  have hdescent : baseEnd_1865421 < baseStart_1865421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865508 : List Nat := [2, 3, 1, 3, 2, 1, 2, 2, 5]
def baseStart_1865508 : Nat := 118140960795 + 1865508 * 2 ^ 59
def prefixEnd_1865508 : Nat := 4983230072969 + 3 ^ 40 * 1865508 * 2
def baseEnd_1865508 : Nat := 425734341692352188920307

theorem tailTrace_1865508 : CollatzResearch.WordTrace tailWord_1865508 prefixEnd_1865508 425734341692352188920307 := by
  unfold tailWord_1865508
  simp only [CollatzResearch.WordTrace]
  refine ⟨34020333262795297123098589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45360444350393729497464785 34020333262795297123098589)
  ·
    refine ⟨12757624973548236421161971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34020333262795297123098589 12757624973548236421161971)
    ·
      refine ⟨19136437460322354631742957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12757624973548236421161971 19136437460322354631742957)
      ·
        refine ⟨7176164047620882986903609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19136437460322354631742957 7176164047620882986903609)
        ·
          refine ⟨5382123035715662240177707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7176164047620882986903609 5382123035715662240177707)
          ·
            refine ⟨8073184553573493360266561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5382123035715662240177707 8073184553573493360266561)
            ·
              refine ⟨6054888415180120020199921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8073184553573493360266561 6054888415180120020199921)
              ·
                refine ⟨4541166311385090015149941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6054888415180120020199921 4541166311385090015149941)
                ·
                  refine ⟨425734341692352188920307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4541166311385090015149941 425734341692352188920307)
                  ·
                    rfl

theorem cell21_1865508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_1865508 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865508 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865508 prefixEnd_1865508 := by exact prefixLift 1865508
  have htrace : WordTrace (prefixWord ++ tailWord_1865508) baseStart_1865508 baseEnd_1865508 := by
    simpa [prefixWord, tailWord_1865508, baseEnd_1865508] using wordTrace_append hprefix tailTrace_1865508
  have hstable : (prefixWord ++ tailWord_1865508).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865508).length < 2 ^ (prefixWord ++ tailWord_1865508).sum := by decide
  have hdescent : baseEnd_1865508 < baseStart_1865508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865522 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 6]
def baseStart_1865522 : Nat := 118140960795 + 1865522 * 2 ^ 59
def prefixEnd_1865522 : Nat := 4983230072969 + 3 ^ 40 * 1865522 * 2
def baseEnd_1865522 : Nat := 425737536683091275686945

theorem tailTrace_1865522 : CollatzResearch.WordTrace tailWord_1865522 prefixEnd_1865522 425737536683091275686945 := by
  unfold tailWord_1865522
  simp only [CollatzResearch.WordTrace]
  refine ⟨17010294286884968659301705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45360784765026583091471213 17010294286884968659301705)
  ·
    refine ⟨12757720715163726494476279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17010294286884968659301705 12757720715163726494476279)
    ·
      refine ⟨19136581072745589741714419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12757720715163726494476279 19136581072745589741714419)
      ·
        refine ⟨28704871609118384612571629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19136581072745589741714419 28704871609118384612571629)
        ·
          refine ⟨10764326853419394229714361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28704871609118384612571629 10764326853419394229714361)
          ·
            refine ⟨8073245140064545672285771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10764326853419394229714361 8073245140064545672285771)
            ·
              refine ⟨12109867710096818508428657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8073245140064545672285771 12109867710096818508428657)
              ·
                refine ⟨9082400782572613881321493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12109867710096818508428657 9082400782572613881321493)
                ·
                  refine ⟨425737536683091275686945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9082400782572613881321493 425737536683091275686945)
                  ·
                    rfl

theorem cell21_1865522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_1865522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865522 prefixEnd_1865522 := by exact prefixLift 1865522
  have htrace : WordTrace (prefixWord ++ tailWord_1865522) baseStart_1865522 baseEnd_1865522 := by
    simpa [prefixWord, tailWord_1865522, baseEnd_1865522] using wordTrace_append hprefix tailTrace_1865522
  have hstable : (prefixWord ++ tailWord_1865522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865522).length < 2 ^ (prefixWord ++ tailWord_1865522).sum := by decide
  have hdescent : baseEnd_1865522 < baseStart_1865522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865542 : List Nat := [6, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_1865542 : Nat := 118140960795 + 1865542 * 2 ^ 59
def prefixEnd_1865542 : Nat := 4983230072969 + 3 ^ 40 * 1865542 * 2
def baseEnd_1865542 : Nat := 425742100955575685353571

theorem tailTrace_1865542 : CollatzResearch.WordTrace tailWord_1865542 prefixEnd_1865542 425742100955575685353571 := by
  unfold tailWord_1865542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2126309581483356814154215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45361271071644945368623253 2126309581483356814154215)
  ·
    refine ⟨3189464372225035221231323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2126309581483356814154215 3189464372225035221231323)
    ·
      refine ⟨4784196558337552831846985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3189464372225035221231323 4784196558337552831846985)
      ·
        refine ⟨3588147418753164623885239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4784196558337552831846985 3588147418753164623885239)
        ·
          refine ⟨5382221128129746935827859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3588147418753164623885239 5382221128129746935827859)
          ·
            refine ⟨8073331692194620403741789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5382221128129746935827859 8073331692194620403741789)
            ·
              refine ⟨3027499384572982651403171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8073331692194620403741789 3027499384572982651403171)
              ·
                refine ⟨4541249076859473977104757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3027499384572982651403171 4541249076859473977104757)
                ·
                  refine ⟨425742100955575685353571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4541249076859473977104757 425742100955575685353571)
                  ·
                    rfl

theorem cell21_1865542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_1865542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865542 prefixEnd_1865542 := by exact prefixLift 1865542
  have htrace : WordTrace (prefixWord ++ tailWord_1865542) baseStart_1865542 baseEnd_1865542 := by
    simpa [prefixWord, tailWord_1865542, baseEnd_1865542] using wordTrace_append hprefix tailTrace_1865542
  have hstable : (prefixWord ++ tailWord_1865542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865542).length < 2 ^ (prefixWord ++ tailWord_1865542).sum := by decide
  have hdescent : baseEnd_1865542 < baseStart_1865542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865553 : List Nat := [1, 2, 2, 1, 5, 2, 2, 6]
def baseStart_1865553 : Nat := 118140960795 + 1865553 * 2 ^ 59
def prefixEnd_1865553 : Nat := 4983230072969 + 3 ^ 40 * 1865553 * 2
def baseEnd_1865553 : Nat := 141914870435147370223405

theorem tailTrace_1865553 : CollatzResearch.WordTrace tailWord_1865553 prefixEnd_1865553 141914870435147370223405 := by
  unfold tailWord_1865553
  simp only [CollatzResearch.WordTrace]
  refine ⟨68042307810427566931585313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45361538540285044621056875 68042307810427566931585313)
  ·
    refine ⟨51031730857820675198688985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68042307810427566931585313 51031730857820675198688985)
    ·
      refine ⟨38273798143365506399016739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51031730857820675198688985 38273798143365506399016739)
      ·
        refine ⟨57410697215048259598525109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38273798143365506399016739 57410697215048259598525109)
        ·
          refine ⟨5382252863910774337361729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57410697215048259598525109 5382252863910774337361729)
          ·
            refine ⟨4036689647933080753021297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5382252863910774337361729 4036689647933080753021297)
            ·
              refine ⟨3027517235949810564765973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4036689647933080753021297 3027517235949810564765973)
              ·
                refine ⟨141914870435147370223405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3027517235949810564765973 141914870435147370223405)
                ·
                  rfl

theorem cell21_1865553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 6].length) (baseStart_1865553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865553 prefixEnd_1865553 := by exact prefixLift 1865553
  have htrace : WordTrace (prefixWord ++ tailWord_1865553) baseStart_1865553 baseEnd_1865553 := by
    simpa [prefixWord, tailWord_1865553, baseEnd_1865553] using wordTrace_append hprefix tailTrace_1865553
  have hstable : (prefixWord ++ tailWord_1865553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865553).length < 2 ^ (prefixWord ++ tailWord_1865553).sum := by decide
  have hdescent : baseEnd_1865553 < baseStart_1865553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865556 : List Nat := [2, 4, 1, 1, 3, 1, 4, 1, 4]
def baseStart_1865556 : Nat := 118140960795 + 1865556 * 2 ^ 59
def prefixEnd_1865556 : Nat := 4983230072969 + 3 ^ 40 * 1865556 * 2
def baseEnd_1865556 : Nat := 425745295946314772120209

theorem tailTrace_1865556 : CollatzResearch.WordTrace tailWord_1865556 prefixEnd_1865556 425745295946314772120209 := by
  unfold tailWord_1865556
  simp only [CollatzResearch.WordTrace]
  refine ⟨34021208614708349221972261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45361611486277798962629681 34021208614708349221972261)
  ·
    refine ⟨6378976615257815479119799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34021208614708349221972261 6378976615257815479119799)
    ·
      refine ⟨9568464922886723218679699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6378976615257815479119799 9568464922886723218679699)
      ·
        refine ⟨14352697384330084828019549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9568464922886723218679699 14352697384330084828019549)
        ·
          refine ⟨5382261519123781810507331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14352697384330084828019549 5382261519123781810507331)
          ·
            refine ⟨8073392278685672715760997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5382261519123781810507331 8073392278685672715760997)
            ·
              refine ⟨1513761052253563634205187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8073392278685672715760997 1513761052253563634205187)
              ·
                refine ⟨2270641578380345451307781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1513761052253563634205187 2270641578380345451307781)
                ·
                  refine ⟨425745295946314772120209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2270641578380345451307781 425745295946314772120209)
                  ·
                    rfl

theorem cell21_1865556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_1865556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865556 prefixEnd_1865556 := by exact prefixLift 1865556
  have htrace : WordTrace (prefixWord ++ tailWord_1865556) baseStart_1865556 baseEnd_1865556 := by
    simpa [prefixWord, tailWord_1865556, baseEnd_1865556] using wordTrace_append hprefix tailTrace_1865556
  have hstable : (prefixWord ++ tailWord_1865556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865556).length < 2 ^ (prefixWord ++ tailWord_1865556).sum := by decide
  have hdescent : baseEnd_1865556 < baseStart_1865556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865584 : List Nat := [2, 1, 1, 1, 4, 1, 1, 7, 3]
def baseStart_1865584 : Nat := 118140960795 + 1865584 * 2 ^ 59
def prefixEnd_1865584 : Nat := 4983230072969 + 3 ^ 40 * 1865584 * 2
def baseEnd_1865584 : Nat := 425751685927792945653485

theorem tailTrace_1865584 : CollatzResearch.WordTrace tailWord_1865584 prefixEnd_1865584 425751685927792945653485 := by
  unfold tailWord_1865584
  simp only [CollatzResearch.WordTrace]
  refine ⟨34021719236657629612981903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45362292315543506150642537 34021719236657629612981903)
  ·
    refine ⟨51032578854986444419472855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34021719236657629612981903 51032578854986444419472855)
    ·
      refine ⟨76548868282479666629209283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51032578854986444419472855 76548868282479666629209283)
      ·
        refine ⟨114823302423719499943813925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76548868282479666629209283 114823302423719499943813925)
        ·
          refine ⟨21529369204447406239465111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114823302423719499943813925 21529369204447406239465111)
          ·
            refine ⟨32294053806671109359197667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21529369204447406239465111 32294053806671109359197667)
            ·
              refine ⟨48441080710006664038796501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32294053806671109359197667 48441080710006664038796501)
              ·
                refine ⟨1135337829140781188409293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 48441080710006664038796501 1135337829140781188409293)
                ·
                  refine ⟨425751685927792945653485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1135337829140781188409293 425751685927792945653485)
                  ·
                    rfl

theorem cell21_1865584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 7, 3].length) (baseStart_1865584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865584 prefixEnd_1865584 := by exact prefixLift 1865584
  have htrace : WordTrace (prefixWord ++ tailWord_1865584) baseStart_1865584 baseEnd_1865584 := by
    simpa [prefixWord, tailWord_1865584, baseEnd_1865584] using wordTrace_append hprefix tailTrace_1865584
  have hstable : (prefixWord ++ tailWord_1865584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865584).length < 2 ^ (prefixWord ++ tailWord_1865584).sum := by decide
  have hdescent : baseEnd_1865584 < baseStart_1865584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865674 : List Nat := [3, 1, 2, 1, 2, 1, 2, 5, 4]
def baseStart_1865674 : Nat := 118140960795 + 1865674 * 2 ^ 59
def prefixEnd_1865674 : Nat := 4983230072969 + 3 ^ 40 * 1865674 * 2
def baseEnd_1865674 : Nat := 425772225153972789153301

theorem tailTrace_1865674 : CollatzResearch.WordTrace tailWord_1865674 prefixEnd_1865674 425772225153972789153301 := by
  unfold tailWord_1865674
  simp only [CollatzResearch.WordTrace]
  refine ⟨17011680260747301149185019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45364480695326136397826717 17011680260747301149185019)
  ·
    refine ⟨25517520391120951723777529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17011680260747301149185019 25517520391120951723777529)
    ·
      refine ⟨19138140293340713792833147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25517520391120951723777529 19138140293340713792833147)
      ·
        refine ⟨28707210440011070689249721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19138140293340713792833147 28707210440011070689249721)
        ·
          refine ⟨21530407830008303016937291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28707210440011070689249721 21530407830008303016937291)
          ·
            refine ⟨32295611745012454525405937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21530407830008303016937291 32295611745012454525405937)
            ·
              refine ⟨24221708808759340894054453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32295611745012454525405937 24221708808759340894054453)
              ·
                refine ⟨2270785200821188208817605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24221708808759340894054453 2270785200821188208817605)
                ·
                  refine ⟨425772225153972789153301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2270785200821188208817605 425772225153972789153301)
                  ·
                    rfl

theorem cell21_1865674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_1865674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865674 prefixEnd_1865674 := by exact prefixLift 1865674
  have htrace : WordTrace (prefixWord ++ tailWord_1865674) baseStart_1865674 baseEnd_1865674 := by
    simpa [prefixWord, tailWord_1865674, baseEnd_1865674] using wordTrace_append hprefix tailTrace_1865674
  have hstable : (prefixWord ++ tailWord_1865674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865674).length < 2 ^ (prefixWord ++ tailWord_1865674).sum := by decide
  have hdescent : baseEnd_1865674 < baseStart_1865674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865688 : List Nat := [2, 1, 2, 2, 2, 2, 3, 7]
def baseStart_1865688 : Nat := 118140960795 + 1865688 * 2 ^ 59
def prefixEnd_1865688 : Nat := 4983230072969 + 3 ^ 40 * 1865688 * 2
def baseEnd_1865688 : Nat := 141925140048237291973313

theorem tailTrace_1865688 : CollatzResearch.WordTrace tailWord_1865688 prefixEnd_1865688 141925140048237291973313 := by
  unfold tailWord_1865688
  simp only [CollatzResearch.WordTrace]
  refine ⟨34023615832469242493874859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45364821109958989991833145 34023615832469242493874859)
  ·
    refine ⟨51035423748703863740812289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34023615832469242493874859 51035423748703863740812289)
    ·
      refine ⟨38276567811527897805609217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51035423748703863740812289 38276567811527897805609217)
      ·
        refine ⟨28707425858645923354206913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38276567811527897805609217 28707425858645923354206913)
        ·
          refine ⟨21530569393984442515655185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28707425858645923354206913 21530569393984442515655185)
          ·
            refine ⟨16147927045488331886741389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21530569393984442515655185 16147927045488331886741389)
            ·
              refine ⟨6055472642058124457528021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16147927045488331886741389 6055472642058124457528021)
              ·
                refine ⟨141925140048237291973313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6055472642058124457528021 141925140048237291973313)
                ·
                  rfl

theorem cell21_1865688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 7].length) (baseStart_1865688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865688 prefixEnd_1865688 := by exact prefixLift 1865688
  have htrace : WordTrace (prefixWord ++ tailWord_1865688) baseStart_1865688 baseEnd_1865688 := by
    simpa [prefixWord, tailWord_1865688, baseEnd_1865688] using wordTrace_append hprefix tailTrace_1865688
  have hstable : (prefixWord ++ tailWord_1865688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865688).length < 2 ^ (prefixWord ++ tailWord_1865688).sum := by decide
  have hdescent : baseEnd_1865688 < baseStart_1865688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865764 : List Nat := [2, 3, 1, 4, 11]
def baseStart_1865764 : Nat := 118140960795 + 1865764 * 2 ^ 59
def prefixEnd_1865764 : Nat := 4983230072969 + 3 ^ 40 * 1865764 * 2
def baseEnd_1865764 : Nat := 5256700794816699168557

theorem tailTrace_1865764 : CollatzResearch.WordTrace tailWord_1865764 prefixEnd_1865764 5256700794816699168557 := by
  unfold tailWord_1865764
  simp only [CollatzResearch.WordTrace]
  refine ⟨34025001806331574983758173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45366669075108766645010897 34025001806331574983758173)
  ·
    refine ⟨12759375677374340618909315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34025001806331574983758173 12759375677374340618909315)
    ·
      refine ⟨19139063516061510928363973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12759375677374340618909315 19139063516061510928363973)
      ·
        refine ⟨3588574409261533299068245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19139063516061510928363973 3588574409261533299068245)
        ·
          refine ⟨5256700794816699168557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3588574409261533299068245 5256700794816699168557)
          ·
            rfl

theorem cell21_1865764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 11].length) (baseStart_1865764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865764 prefixEnd_1865764 := by exact prefixLift 1865764
  have htrace : WordTrace (prefixWord ++ tailWord_1865764) baseStart_1865764 baseEnd_1865764 := by
    simpa [prefixWord, tailWord_1865764, baseEnd_1865764] using wordTrace_append hprefix tailTrace_1865764
  have hstable : (prefixWord ++ tailWord_1865764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865764).length < 2 ^ (prefixWord ++ tailWord_1865764).sum := by decide
  have hdescent : baseEnd_1865764 < baseStart_1865764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865770 : List Nat := [3, 1, 4, 1, 2, 1, 4, 2, 3]
def baseStart_1865770 : Nat := 118140960795 + 1865770 * 2 ^ 59
def prefixEnd_1865770 : Nat := 4983230072969 + 3 ^ 40 * 1865770 * 2
def baseEnd_1865770 : Nat := 425794133661897955553105

theorem tailTrace_1865770 : CollatzResearch.WordTrace tailWord_1865770 prefixEnd_1865770 425794133661897955553105 := by
  unfold tailWord_1865770
  simp only [CollatzResearch.WordTrace]
  refine ⟨17012555612660353248058691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45366814967094275328156509 17012555612660353248058691)
  ·
    refine ⟨25518833418990529872088037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17012555612660353248058691 25518833418990529872088037)
    ·
      refine ⟨4784781266060724351016507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25518833418990529872088037 4784781266060724351016507)
      ·
        refine ⟨7177171899091086526524761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4784781266060724351016507 7177171899091086526524761)
        ·
          refine ⟨5382878924318314894893571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7177171899091086526524761 5382878924318314894893571)
          ·
            refine ⟨8074318386477472342340357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5382878924318314894893571 8074318386477472342340357)
            ·
              refine ⟨1513934697464526064188817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8074318386477472342340357 1513934697464526064188817)
              ·
                refine ⟨1135451023098394548141613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1513934697464526064188817 1135451023098394548141613)
                ·
                  refine ⟨425794133661897955553105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1135451023098394548141613 425794133661897955553105)
                  ·
                    rfl

theorem cell21_1865770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 2, 3].length) (baseStart_1865770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865770 prefixEnd_1865770 := by exact prefixLift 1865770
  have htrace : WordTrace (prefixWord ++ tailWord_1865770) baseStart_1865770 baseEnd_1865770 := by
    simpa [prefixWord, tailWord_1865770, baseEnd_1865770] using wordTrace_append hprefix tailTrace_1865770
  have hstable : (prefixWord ++ tailWord_1865770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865770).length < 2 ^ (prefixWord ++ tailWord_1865770).sum := by decide
  have hdescent : baseEnd_1865770 < baseStart_1865770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865809 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 6]
def baseStart_1865809 : Nat := 118140960795 + 1865809 * 2 ^ 59
def prefixEnd_1865809 : Nat := 4983230072969 + 3 ^ 40 * 1865809 * 2
def baseEnd_1865809 : Nat := 425803033993242554403025

theorem tailTrace_1865809 : CollatzResearch.WordTrace tailWord_1865809 prefixEnd_1865809 425803033993242554403025 := by
  unfold tailWord_1865809
  simp only [CollatzResearch.WordTrace]
  refine ⟨68051644897500122652904481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45367763265000081768602987 68051644897500122652904481)
  ·
    refine ⟨51038733673125091989678361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68051644897500122652904481 51038733673125091989678361)
    ·
      refine ⟨38279050254843818992258771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51038733673125091989678361 38279050254843818992258771)
      ·
        refine ⟨57418575382265728488388157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38279050254843818992258771 57418575382265728488388157)
        ·
          refine ⟨21531965768349648183145559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57418575382265728488388157 21531965768349648183145559)
          ·
            refine ⟨32297948652524472274718339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21531965768349648183145559 32297948652524472274718339)
            ·
              refine ⟨48446922978786708412077509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32297948652524472274718339 48446922978786708412077509)
              ·
                refine ⟨9083798058522507827264533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48446922978786708412077509 9083798058522507827264533)
                ·
                  refine ⟨425803033993242554403025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9083798058522507827264533 425803033993242554403025)
                  ·
                    rfl

theorem cell21_1865809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_1865809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865809 prefixEnd_1865809 := by exact prefixLift 1865809
  have htrace : WordTrace (prefixWord ++ tailWord_1865809) baseStart_1865809 baseEnd_1865809 := by
    simpa [prefixWord, tailWord_1865809, baseEnd_1865809] using wordTrace_append hprefix tailTrace_1865809
  have hstable : (prefixWord ++ tailWord_1865809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865809).length < 2 ^ (prefixWord ++ tailWord_1865809).sum := by decide
  have hdescent : baseEnd_1865809 < baseStart_1865809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865857 : List Nat := [1, 2, 4, 2, 3, 1, 1, 7]
def baseStart_1865857 : Nat := 118140960795 + 1865857 * 2 ^ 59
def prefixEnd_1865857 : Nat := 4983230072969 + 3 ^ 40 * 1865857 * 2
def baseEnd_1865857 : Nat := 141937996082401712534309

theorem tailTrace_1865857 : CollatzResearch.WordTrace tailWord_1865857 prefixEnd_1865857 141937996082401712534309 := by
  unfold tailWord_1865857
  simp only [CollatzResearch.WordTrace]
  refine ⟨68053395601326226850651825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45368930400884151233767883 68053395601326226850651825)
  ·
    refine ⟨51040046700994670137988869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68053395601326226850651825 51040046700994670137988869)
    ·
      refine ⟨9570008756436500650872913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51040046700994670137988869 9570008756436500650872913)
      ·
        refine ⟨7177506567327375488154685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9570008756436500650872913 7177506567327375488154685)
        ·
          refine ⟨2691564962747765808058007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7177506567327375488154685 2691564962747765808058007)
          ·
            refine ⟨4037347444121648712087011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2691564962747765808058007 4037347444121648712087011)
            ·
              refine ⟨6056021166182473068130517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4037347444121648712087011 6056021166182473068130517)
              ·
                refine ⟨141937996082401712534309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6056021166182473068130517 141937996082401712534309)
                ·
                  rfl

theorem cell21_1865857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 7].length) (baseStart_1865857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865857 prefixEnd_1865857 := by exact prefixLift 1865857
  have htrace : WordTrace (prefixWord ++ tailWord_1865857) baseStart_1865857 baseEnd_1865857 := by
    simpa [prefixWord, tailWord_1865857, baseEnd_1865857] using wordTrace_append hprefix tailTrace_1865857
  have hstable : (prefixWord ++ tailWord_1865857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865857).length < 2 ^ (prefixWord ++ tailWord_1865857).sum := by decide
  have hdescent : baseEnd_1865857 < baseStart_1865857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865888 : List Nat := [2, 1, 1, 4, 2, 4, 1, 1, 5]
def baseStart_1865888 : Nat := 118140960795 + 1865888 * 2 ^ 59
def prefixEnd_1865888 : Nat := 4983230072969 + 3 ^ 40 * 1865888 * 2
def baseEnd_1865888 : Nat := 425821062869555972586197

theorem tailTrace_1865888 : CollatzResearch.WordTrace tailWord_1865888 prefixEnd_1865888 425821062869555972586197 := by
  unfold tailWord_1865888
  simp only [CollatzResearch.WordTrace]
  refine ⟨34027263132106959572515159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45369684176142612763353545 34027263132106959572515159)
  ·
    refine ⟨51040894698160439358772739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34027263132106959572515159 51040894698160439358772739)
    ·
      refine ⟨76561342047240659038159109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51040894698160439358772739 76561342047240659038159109)
      ·
        refine ⟨14355251633857623569654833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76561342047240659038159109 14355251633857623569654833)
        ·
          refine ⟨10766438725393217677241125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14355251633857623569654833 10766438725393217677241125)
          ·
            refine ⟨2018707261011228314482711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10766438725393217677241125 2018707261011228314482711)
            ·
              refine ⟨3028060891516842471724067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2018707261011228314482711 3028060891516842471724067)
              ·
                refine ⟨4542091337275263707586101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3028060891516842471724067 4542091337275263707586101)
                ·
                  refine ⟨425821062869555972586197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4542091337275263707586101 425821062869555972586197)
                  ·
                    rfl

theorem cell21_1865888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 5].length) (baseStart_1865888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865888 prefixEnd_1865888 := by exact prefixLift 1865888
  have htrace : WordTrace (prefixWord ++ tailWord_1865888) baseStart_1865888 baseEnd_1865888 := by
    simpa [prefixWord, tailWord_1865888, baseEnd_1865888] using wordTrace_append hprefix tailTrace_1865888
  have hstable : (prefixWord ++ tailWord_1865888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865888).length < 2 ^ (prefixWord ++ tailWord_1865888).sum := by decide
  have hdescent : baseEnd_1865888 < baseStart_1865888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1865992 : List Nat := [2, 1, 3, 2, 3, 2, 8]
def baseStart_1865992 : Nat := 118140960795 + 1865992 * 2 ^ 59
def prefixEnd_1865992 : Nat := 4983230072969 + 3 ^ 40 * 1865992 * 2
def baseEnd_1865992 : Nat := 47316088565163878094739

theorem tailTrace_1865992 : CollatzResearch.WordTrace tailWord_1865992 prefixEnd_1865992 47316088565163878094739 := by
  unfold tailWord_1865992
  simp only [CollatzResearch.WordTrace]
  refine ⟨34029159727918572453408115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45372212970558096604544153 34029159727918572453408115)
  ·
    refine ⟨51043739591877858680112173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34029159727918572453408115 51043739591877858680112173)
    ·
      refine ⟨19141402346954197005042065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51043739591877858680112173 19141402346954197005042065)
      ·
        refine ⟨14356051760215647753781549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19141402346954197005042065 14356051760215647753781549)
        ·
          refine ⟨5383519410080867907668081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14356051760215647753781549 5383519410080867907668081)
          ·
            refine ⟨4037639557560650930751061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5383519410080867907668081 4037639557560650930751061)
            ·
              refine ⟨47316088565163878094739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4037639557560650930751061 47316088565163878094739)
              ·
                rfl

theorem cell21_1865992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 8].length) (baseStart_1865992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1865992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1865992 prefixEnd_1865992 := by exact prefixLift 1865992
  have htrace : WordTrace (prefixWord ++ tailWord_1865992) baseStart_1865992 baseEnd_1865992 := by
    simpa [prefixWord, tailWord_1865992, baseEnd_1865992] using wordTrace_append hprefix tailTrace_1865992
  have hstable : (prefixWord ++ tailWord_1865992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1865992).length < 2 ^ (prefixWord ++ tailWord_1865992).sum := by decide
  have hdescent : baseEnd_1865992 < baseStart_1865992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1865992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866037 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 8]
def baseStart_1866037 : Nat := 118140960795 + 1866037 * 2 ^ 59
def prefixEnd_1866037 : Nat := 4983230072969 + 3 ^ 40 * 1866037 * 2
def baseEnd_1866037 : Nat := 425855066699564824602559

theorem tailTrace_1866037 : CollatzResearch.WordTrace tailWord_1866037 prefixEnd_1866037 425855066699564824602559 := by
  unfold tailWord_1866037
  simp only [CollatzResearch.WordTrace]
  refine ⟨68059960740674117592204365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45373307160449411728136243 68059960740674117592204365)
  ·
    refine ⟨25522485277752794097076637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68059960740674117592204365 25522485277752794097076637)
    ·
      refine ⟨9570931979157297786403739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25522485277752794097076637 9570931979157297786403739)
      ·
        refine ⟨14356397968735946679605609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9570931979157297786403739 14356397968735946679605609)
        ·
          refine ⟨10767298476551960009704207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14356397968735946679605609 10767298476551960009704207)
          ·
            refine ⟨16150947714827940014556311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10767298476551960009704207 16150947714827940014556311)
            ·
              refine ⟨24226421572241910021834467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16150947714827940014556311 24226421572241910021834467)
              ·
                refine ⟨36339632358362865032751701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24226421572241910021834467 36339632358362865032751701)
                ·
                  refine ⟨425855066699564824602559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36339632358362865032751701 425855066699564824602559)
                  ·
                    rfl

theorem cell21_1866037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_1866037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866037 prefixEnd_1866037 := by exact prefixLift 1866037
  have htrace : WordTrace (prefixWord ++ tailWord_1866037) baseStart_1866037 baseEnd_1866037 := by
    simpa [prefixWord, tailWord_1866037, baseEnd_1866037] using wordTrace_append hprefix tailTrace_1866037
  have hstable : (prefixWord ++ tailWord_1866037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866037).length < 2 ^ (prefixWord ++ tailWord_1866037).sum := by decide
  have hdescent : baseEnd_1866037 < baseStart_1866037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866040 : List Nat := [2, 1, 2, 1, 3, 1, 5, 3, 3]
def baseStart_1866040 : Nat := 118140960795 + 1866040 * 2 ^ 59
def prefixEnd_1866040 : Nat := 4983230072969 + 3 ^ 40 * 1866040 * 2
def baseEnd_1866040 : Nat := 425855751340437486052553

theorem tailTrace_1866040 : CollatzResearch.WordTrace tailWord_1866040 prefixEnd_1866040 425855751340437486052553 := by
  unfold tailWord_1866040
  simp only [CollatzResearch.WordTrace]
  refine ⟨34030035079831624552281787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45373380106442166069709049 34030035079831624552281787)
  ·
    refine ⟨51045052619747436828422681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34030035079831624552281787 51045052619747436828422681)
    ·
      refine ⟨38283789464810577621317011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51045052619747436828422681 38283789464810577621317011)
      ·
        refine ⟨57425684197215866431975517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38283789464810577621317011 57425684197215866431975517)
        ·
          refine ⟨21534631573955949911990819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57425684197215866431975517 21534631573955949911990819)
          ·
            refine ⟨32301947360933924867986229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21534631573955949911990819 32301947360933924867986229)
            ·
              refine ⟨3028307565087555456373709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32301947360933924867986229 3028307565087555456373709)
              ·
                refine ⟨1135615336907833296140141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3028307565087555456373709 1135615336907833296140141)
                ·
                  refine ⟨425855751340437486052553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1135615336907833296140141 425855751340437486052553)
                  ·
                    rfl

theorem cell21_1866040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 3, 3].length) (baseStart_1866040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866040 prefixEnd_1866040 := by exact prefixLift 1866040
  have htrace : WordTrace (prefixWord ++ tailWord_1866040) baseStart_1866040 baseEnd_1866040 := by
    simpa [prefixWord, tailWord_1866040, baseEnd_1866040] using wordTrace_append hprefix tailTrace_1866040
  have hstable : (prefixWord ++ tailWord_1866040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866040).length < 2 ^ (prefixWord ++ tailWord_1866040).sum := by decide
  have hdescent : baseEnd_1866040 < baseStart_1866040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866051 : List Nat := [1, 1, 1, 3, 1, 3, 11]
def baseStart_1866051 : Nat := 118140960795 + 1866051 * 2 ^ 59
def prefixEnd_1866051 : Nat := 4983230072969 + 3 ^ 40 * 1866051 * 2
def baseEnd_1866051 : Nat := 47317584632255990152133

theorem tailTrace_1866051 : CollatzResearch.WordTrace tailWord_1866051 prefixEnd_1866051 47317584632255990152133 := by
  unfold tailWord_1866051
  simp only [CollatzResearch.WordTrace]
  refine ⟨68060471362623397983214007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45373647575082265322142671 68060471362623397983214007)
  ·
    refine ⟨102090707043935096974821011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68060471362623397983214007 102090707043935096974821011)
    ·
      refine ⟨153136060565902645462231517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102090707043935096974821011 153136060565902645462231517)
      ·
        refine ⟨57426022712213492048336819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153136060565902645462231517 57426022712213492048336819)
        ·
          refine ⟨86139034068320238072505229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57426022712213492048336819 86139034068320238072505229)
          ·
            refine ⟨32302137775620089277189461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86139034068320238072505229 32302137775620089277189461)
            ·
              refine ⟨47317584632255990152133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32302137775620089277189461 47317584632255990152133)
              ·
                rfl

theorem cell21_1866051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 11].length) (baseStart_1866051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866051 prefixEnd_1866051 := by exact prefixLift 1866051
  have htrace : WordTrace (prefixWord ++ tailWord_1866051) baseStart_1866051 baseEnd_1866051 := by
    simpa [prefixWord, tailWord_1866051, baseEnd_1866051] using wordTrace_append hprefix tailTrace_1866051
  have hstable : (prefixWord ++ tailWord_1866051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866051).length < 2 ^ (prefixWord ++ tailWord_1866051).sum := by decide
  have hdescent : baseEnd_1866051 < baseStart_1866051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866068 : List Nat := [2, 4, 1, 1, 2, 2, 1, 8]
def baseStart_1866068 : Nat := 118140960795 + 1866068 * 2 ^ 59
def prefixEnd_1866068 : Nat := 4983230072969 + 3 ^ 40 * 1866068 * 2
def baseEnd_1866068 : Nat := 141954047107305219861943

theorem tailTrace_1866068 : CollatzResearch.WordTrace tailWord_1866068 prefixEnd_1866068 141954047107305219861943 := by
  unfold tailWord_1866068
  simp only [CollatzResearch.WordTrace]
  refine ⟨34030545701780904943291429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45374060935707873257721905 34030545701780904943291429)
  ·
    refine ⟨6380727319083919676867143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34030545701780904943291429 6380727319083919676867143)
    ·
      refine ⟨9571090978625879515300715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6380727319083919676867143 9571090978625879515300715)
      ·
        refine ⟨14356636467938819272951073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9571090978625879515300715 14356636467938819272951073)
        ·
          refine ⟨10767477350954114454713305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14356636467938819272951073 10767477350954114454713305)
          ·
            refine ⟨8075608013215585841034979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10767477350954114454713305 8075608013215585841034979)
            ·
              refine ⟨12113412019823378761552469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8075608013215585841034979 12113412019823378761552469)
              ·
                refine ⟨141954047107305219861943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12113412019823378761552469 141954047107305219861943)
                ·
                  rfl

theorem cell21_1866068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 8].length) (baseStart_1866068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866068 prefixEnd_1866068 := by exact prefixLift 1866068
  have htrace : WordTrace (prefixWord ++ tailWord_1866068) baseStart_1866068 baseEnd_1866068 := by
    simpa [prefixWord, tailWord_1866068, baseEnd_1866068] using wordTrace_append hprefix tailTrace_1866068
  have hstable : (prefixWord ++ tailWord_1866068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866068).length < 2 ^ (prefixWord ++ tailWord_1866068).sum := by decide
  have hdescent : baseEnd_1866068 < baseStart_1866068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
