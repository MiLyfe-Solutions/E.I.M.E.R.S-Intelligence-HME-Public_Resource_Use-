import V185TrunkScan20Chunk035

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_219551 : List Nat := [1, 1, 2, 5, 1, 1, 3, 2, 4]
def baseStart_219551 : Nat := 118140960795 + 219551 * 2 ^ 59
def prefixEnd_219551 : Nat := 4983230072969 + 3 ^ 40 * 219551 * 2
def baseEnd_219551 : Nat := 100209058822556212802497

theorem tailTrace_219551 : CollatzResearch.WordTrace tailWord_219551 prefixEnd_219551 100209058822556212802497 := by
  unfold tailWord_219551
  simp only [CollatzResearch.WordTrace]
  refine ⟨8007682827611698170674507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5338455218407798780449671 8007682827611698170674507)
  ·
    refine ⟨12011524241417547256011761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8007682827611698170674507 12011524241417547256011761)
    ·
      refine ⟨9008643181063160442008821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12011524241417547256011761 9008643181063160442008821)
      ·
        refine ⟨844560298224671291438327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9008643181063160442008821 844560298224671291438327)
        ·
          refine ⟨1266840447337006937157491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844560298224671291438327 1266840447337006937157491)
          ·
            refine ⟨1900260671005510405736237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266840447337006937157491 1900260671005510405736237)
            ·
              refine ⟨712597751627066402151089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1900260671005510405736237 712597751627066402151089)
              ·
                refine ⟨534448313720299801613317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 712597751627066402151089 534448313720299801613317)
                ·
                  refine ⟨100209058822556212802497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 534448313720299801613317 100209058822556212802497)
                  ·
                    rfl

theorem cell20_219551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_219551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219551 prefixEnd_219551 := by exact prefixLift 219551
  have htrace : WordTrace (prefixWord ++ tailWord_219551) baseStart_219551 baseEnd_219551 := by
    simpa [prefixWord, tailWord_219551, baseEnd_219551] using wordTrace_append hprefix tailTrace_219551
  have hstable : (prefixWord ++ tailWord_219551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219551).length < 2 ^ (prefixWord ++ tailWord_219551).sum := by decide
  have hdescent : baseEnd_219551 < baseStart_219551 := by decide
  rcases family_descends (prefixWord ++ tailWord_219551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219606 : List Nat := [5, 2, 1, 1, 1, 1, 1, 4, 4]
def baseStart_219606 : Nat := 118140960795 + 219606 * 2 ^ 59
def prefixEnd_219606 : Nat := 4983230072969 + 3 ^ 40 * 219606 * 2
def baseEnd_219606 : Nat := 100234162321220465968939

theorem tailTrace_219606 : CollatzResearch.WordTrace tailWord_219606 prefixEnd_219606 100234162321220465968939 := by
  unfold tailWord_219606
  simp only [CollatzResearch.WordTrace]
  refine ⟨500605552650777660245417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5339792561608295042617781 500605552650777660245417)
  ·
    refine ⟨375454164488083245184063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 500605552650777660245417 375454164488083245184063)
    ·
      refine ⟨563181246732124867776095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375454164488083245184063 563181246732124867776095)
      ·
        refine ⟨844771870098187301664143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 563181246732124867776095 844771870098187301664143)
        ·
          refine ⟨1267157805147280952496215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844771870098187301664143 1267157805147280952496215)
          ·
            refine ⟨1900736707720921428744323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267157805147280952496215 1900736707720921428744323)
            ·
              refine ⟨2851105061581382143116485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900736707720921428744323 2851105061581382143116485)
              ·
                refine ⟨534582199046509151834341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2851105061581382143116485 534582199046509151834341)
                ·
                  refine ⟨100234162321220465968939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 534582199046509151834341 100234162321220465968939)
                  ·
                    rfl

theorem cell20_219606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_219606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219606 prefixEnd_219606 := by exact prefixLift 219606
  have htrace : WordTrace (prefixWord ++ tailWord_219606) baseStart_219606 baseEnd_219606 := by
    simpa [prefixWord, tailWord_219606, baseEnd_219606] using wordTrace_append hprefix tailTrace_219606
  have hstable : (prefixWord ++ tailWord_219606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219606).length < 2 ^ (prefixWord ++ tailWord_219606).sum := by decide
  have hdescent : baseEnd_219606 < baseStart_219606 := by decide
  rcases family_descends (prefixWord ++ tailWord_219606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219641 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 5]
def baseStart_219641 : Nat := 118140960795 + 219641 * 2 ^ 59
def prefixEnd_219641 : Nat := 4983230072969 + 3 ^ 40 * 219641 * 2
def baseEnd_219641 : Nat := 100250137274915899802129

theorem tailTrace_219641 : CollatzResearch.WordTrace tailWord_219641 prefixEnd_219641 100250137274915899802129 := by
  unfold tailWord_219641
  simp only [CollatzResearch.WordTrace]
  refine ⟨8010965397285643541450777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5340643598190429027633851 8010965397285643541450777)
  ·
    refine ⟨6008224047964232656088083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8010965397285643541450777 6008224047964232656088083)
    ·
      refine ⟨9012336071946348984132125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6008224047964232656088083 9012336071946348984132125)
      ·
        refine ⟨3379626026979880869049547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9012336071946348984132125 3379626026979880869049547)
        ·
          refine ⟨5069439040469821303574321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3379626026979880869049547 5069439040469821303574321)
          ·
            refine ⟨3802079280352365977680741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5069439040469821303574321 3802079280352365977680741)
            ·
              refine ⟨712889865066068620815139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3802079280352365977680741 712889865066068620815139)
              ·
                refine ⟨1069334797599102931222709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712889865066068620815139 1069334797599102931222709)
                ·
                  refine ⟨100250137274915899802129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1069334797599102931222709 100250137274915899802129)
                  ·
                    rfl

theorem cell20_219641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_219641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219641 prefixEnd_219641 := by exact prefixLift 219641
  have htrace : WordTrace (prefixWord ++ tailWord_219641) baseStart_219641 baseEnd_219641 := by
    simpa [prefixWord, tailWord_219641, baseEnd_219641] using wordTrace_append hprefix tailTrace_219641
  have hstable : (prefixWord ++ tailWord_219641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219641).length < 2 ^ (prefixWord ++ tailWord_219641).sum := by decide
  have hdescent : baseEnd_219641 < baseStart_219641 := by decide
  rcases family_descends (prefixWord ++ tailWord_219641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219650 : List Nat := [3, 4, 1, 2, 3, 1, 2, 1, 3]
def baseStart_219650 : Nat := 118140960795 + 219650 * 2 ^ 59
def prefixEnd_219650 : Nat := 4983230072969 + 3 ^ 40 * 219650 * 2
def baseEnd_219650 : Nat := 100254245120151868502093

theorem tailTrace_219650 : CollatzResearch.WordTrace tailWord_219650 prefixEnd_219650 100254245120151868502093 := by
  unfold tailWord_219650
  simp only [CollatzResearch.WordTrace]
  refine ⟨2002823413563259519632101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5340862436168692052352269 2002823413563259519632101)
  ·
    refine ⟨375529390043111159931019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2002823413563259519632101 375529390043111159931019)
    ·
      refine ⟨563294085064666739896529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375529390043111159931019 563294085064666739896529)
      ·
        refine ⟨422470563798500054922397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 563294085064666739896529 422470563798500054922397)
        ·
          refine ⟨158426461424437520595899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 422470563798500054922397 158426461424437520595899)
          ·
            refine ⟨237639692136656280893849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158426461424437520595899 237639692136656280893849)
            ·
              refine ⟨178229769102492210670387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237639692136656280893849 178229769102492210670387)
              ·
                refine ⟨267344653653738316005581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178229769102492210670387 267344653653738316005581)
                ·
                  refine ⟨100254245120151868502093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267344653653738316005581 100254245120151868502093)
                  ·
                    rfl

theorem cell20_219650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_219650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219650 prefixEnd_219650 := by exact prefixLift 219650
  have htrace : WordTrace (prefixWord ++ tailWord_219650) baseStart_219650 baseEnd_219650 := by
    simpa [prefixWord, tailWord_219650, baseEnd_219650] using wordTrace_append hprefix tailTrace_219650
  have hstable : (prefixWord ++ tailWord_219650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219650).length < 2 ^ (prefixWord ++ tailWord_219650).sum := by decide
  have hdescent : baseEnd_219650 < baseStart_219650 := by decide
  rcases family_descends (prefixWord ++ tailWord_219650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219658 : List Nat := [3, 1, 2, 2, 2, 1, 3, 3, 3]
def baseStart_219658 : Nat := 118140960795 + 219658 * 2 ^ 59
def prefixEnd_219658 : Nat := 4983230072969 + 3 ^ 40 * 219658 * 2
def baseEnd_219658 : Nat := 100257896538139396235393

theorem tailTrace_219658 : CollatzResearch.WordTrace tailWord_219658 prefixEnd_219658 100257896538139396235393 := by
  unfold tailWord_219658
  simp only [CollatzResearch.WordTrace]
  refine ⟨2002896359556013861204907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5341056958816036963213085 2002896359556013861204907)
  ·
    refine ⟨3004344539334020791807361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2002896359556013861204907 3004344539334020791807361)
    ·
      refine ⟨2253258404500515593855521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3004344539334020791807361 2253258404500515593855521)
      ·
        refine ⟨1689943803375386695391641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2253258404500515593855521 1689943803375386695391641)
        ·
          refine ⟨1267457852531540021543731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1689943803375386695391641 1267457852531540021543731)
          ·
            refine ⟨1901186778797310032315597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267457852531540021543731 1901186778797310032315597)
            ·
              refine ⟨712945042048991262118349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1901186778797310032315597 712945042048991262118349)
              ·
                refine ⟨267354390768371723294381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 712945042048991262118349 267354390768371723294381)
                ·
                  refine ⟨100257896538139396235393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267354390768371723294381 100257896538139396235393)
                  ·
                    rfl

theorem cell20_219658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_219658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219658 prefixEnd_219658 := by exact prefixLift 219658
  have htrace : WordTrace (prefixWord ++ tailWord_219658) baseStart_219658 baseEnd_219658 := by
    simpa [prefixWord, tailWord_219658, baseEnd_219658] using wordTrace_append hprefix tailTrace_219658
  have hstable : (prefixWord ++ tailWord_219658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219658).length < 2 ^ (prefixWord ++ tailWord_219658).sum := by decide
  have hdescent : baseEnd_219658 < baseStart_219658 := by decide
  rcases family_descends (prefixWord ++ tailWord_219658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219672 : List Nat := [2, 1, 2, 3, 3, 1, 2, 6]
def baseStart_219672 : Nat := 118140960795 + 219672 * 2 ^ 59
def prefixEnd_219672 : Nat := 4983230072969 + 3 ^ 40 * 219672 * 2
def baseEnd_219672 : Nat := 33421428839872523256223

theorem tailTrace_219672 : CollatzResearch.WordTrace tailWord_219672 prefixEnd_219672 33421428839872523256223 := by
  unfold tailWord_219672
  simp only [CollatzResearch.WordTrace]
  refine ⟨4006048030086667917914635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5341397373448890557219513 4006048030086667917914635)
  ·
    refine ⟨6009072045130001876871953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4006048030086667917914635 6009072045130001876871953)
    ·
      refine ⟨4506804033847501407653965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6009072045130001876871953 4506804033847501407653965)
      ·
        refine ⟨1690051512692813027870237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4506804033847501407653965 1690051512692813027870237)
        ·
          refine ⟨633769317259804885451339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1690051512692813027870237 633769317259804885451339)
          ·
            refine ⟨950653975889707328177009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633769317259804885451339 950653975889707328177009)
            ·
              refine ⟨712990481917280496132757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 950653975889707328177009 712990481917280496132757)
              ·
                refine ⟨33421428839872523256223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 712990481917280496132757 33421428839872523256223)
                ·
                  rfl

theorem cell20_219672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_219672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219672 prefixEnd_219672 := by exact prefixLift 219672
  have htrace : WordTrace (prefixWord ++ tailWord_219672) baseStart_219672 baseEnd_219672 := by
    simpa [prefixWord, tailWord_219672, baseEnd_219672] using wordTrace_append hprefix tailTrace_219672
  have hstable : (prefixWord ++ tailWord_219672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219672).length < 2 ^ (prefixWord ++ tailWord_219672).sum := by decide
  have hdescent : baseEnd_219672 < baseStart_219672 := by decide
  rcases family_descends (prefixWord ++ tailWord_219672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219682 : List Nat := [3, 3, 1, 1, 1, 1, 1, 7, 2]
def baseStart_219682 : Nat := 118140960795 + 219682 * 2 ^ 59
def prefixEnd_219682 : Nat := 4983230072969 + 3 ^ 40 * 219682 * 2
def baseEnd_219682 : Nat := 100268850792101979435295

theorem tailTrace_219682 : CollatzResearch.WordTrace tailWord_219682 prefixEnd_219682 100268850792101979435295 := by
  unfold tailWord_219682
  simp only [CollatzResearch.WordTrace]
  refine ⟨2003115197534276885923325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5341640526758071695795533 2003115197534276885923325)
  ·
    refine ⟨751168199075353832221247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2003115197534276885923325 751168199075353832221247)
    ·
      refine ⟨1126752298613030748331871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 751168199075353832221247 1126752298613030748331871)
      ·
        refine ⟨1690128447919546122497807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1126752298613030748331871 1690128447919546122497807)
        ·
          refine ⟨2535192671879319183746711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1690128447919546122497807 2535192671879319183746711)
          ·
            refine ⟨3802789007818978775620067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2535192671879319183746711 3802789007818978775620067)
            ·
              refine ⟨5704183511728468163430101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3802789007818978775620067 5704183511728468163430101)
              ·
                refine ⟨133691801056135972580393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5704183511728468163430101 133691801056135972580393)
                ·
                  refine ⟨100268850792101979435295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133691801056135972580393 100268850792101979435295)
                  ·
                    rfl

theorem cell20_219682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_219682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219682 prefixEnd_219682 := by exact prefixLift 219682
  have htrace : WordTrace (prefixWord ++ tailWord_219682) baseStart_219682 baseEnd_219682 := by
    simpa [prefixWord, tailWord_219682, baseEnd_219682] using wordTrace_append hprefix tailTrace_219682
  have hstable : (prefixWord ++ tailWord_219682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219682).length < 2 ^ (prefixWord ++ tailWord_219682).sum := by decide
  have hdescent : baseEnd_219682 < baseStart_219682 := by decide
  rcases family_descends (prefixWord ++ tailWord_219682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219716 : List Nat := [2, 3, 5, 1, 1, 1, 1, 2, 4]
def baseStart_219716 : Nat := 118140960795 + 219716 * 2 ^ 59
def prefixEnd_219716 : Nat := 4983230072969 + 3 ^ 40 * 219716 * 2
def baseEnd_219716 : Nat := 100284369318548972301823

theorem tailTrace_219716 : CollatzResearch.WordTrace tailWord_219716 prefixEnd_219716 100284369318548972301823 := by
  unfold tailWord_219716
  simp only [CollatzResearch.WordTrace]
  refine ⟨4006850436006965675215501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5342467248009287566954001 4006850436006965675215501)
  ·
    refine ⟨1502568913502612128205813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4006850436006965675215501 1502568913502612128205813)
    ·
      refine ⟨140865835640869887019295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1502568913502612128205813 140865835640869887019295)
      ·
        refine ⟨211298753461304830528943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140865835640869887019295 211298753461304830528943)
        ·
          refine ⟨316948130191957245793415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211298753461304830528943 316948130191957245793415)
          ·
            refine ⟨475422195287935868690123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316948130191957245793415 475422195287935868690123)
            ·
              refine ⟨713133292931903803035185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 475422195287935868690123 713133292931903803035185)
              ·
                refine ⟨534849969698927852276389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 713133292931903803035185 534849969698927852276389)
                ·
                  refine ⟨100284369318548972301823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 534849969698927852276389 100284369318548972301823)
                  ·
                    rfl

theorem cell20_219716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_219716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219716 prefixEnd_219716 := by exact prefixLift 219716
  have htrace : WordTrace (prefixWord ++ tailWord_219716) baseStart_219716 baseEnd_219716 := by
    simpa [prefixWord, tailWord_219716, baseEnd_219716] using wordTrace_append hprefix tailTrace_219716
  have hstable : (prefixWord ++ tailWord_219716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219716).length < 2 ^ (prefixWord ++ tailWord_219716).sum := by decide
  have hdescent : baseEnd_219716 < baseStart_219716 := by decide
  rcases family_descends (prefixWord ++ tailWord_219716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219755 : List Nat := [1, 1, 1, 1, 2, 2, 1, 8, 3]
def baseStart_219755 : Nat := 118140960795 + 219755 * 2 ^ 59
def prefixEnd_219755 : Nat := 4983230072969 + 3 ^ 40 * 219755 * 2
def baseEnd_219755 : Nat := 100302169981238170001663

theorem tailTrace_219755 : CollatzResearch.WordTrace tailWord_219755 prefixEnd_219755 100302169981238170001663 := by
  unfold tailWord_219755
  simp only [CollatzResearch.WordTrace]
  refine ⟨8015123318872641011100719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5343415545915094007400479 8015123318872641011100719)
  ·
    refine ⟨12022684978308961516651079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8015123318872641011100719 12022684978308961516651079)
    ·
      refine ⟨18034027467463442274976619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12022684978308961516651079 18034027467463442274976619)
      ·
        refine ⟨27051041201195163412464929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18034027467463442274976619 27051041201195163412464929)
        ·
          refine ⟨20288280900896372559348697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27051041201195163412464929 20288280900896372559348697)
          ·
            refine ⟨15216210675672279419511523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20288280900896372559348697 15216210675672279419511523)
            ·
              refine ⟨22824316013508419129267285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15216210675672279419511523 22824316013508419129267285)
              ·
                refine ⟨267472453283301786671101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 22824316013508419129267285 267472453283301786671101)
                ·
                  refine ⟨100302169981238170001663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267472453283301786671101 100302169981238170001663)
                  ·
                    rfl

theorem cell20_219755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 3].length) (baseStart_219755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219755 prefixEnd_219755 := by exact prefixLift 219755
  have htrace : WordTrace (prefixWord ++ tailWord_219755) baseStart_219755 baseEnd_219755 := by
    simpa [prefixWord, tailWord_219755, baseEnd_219755] using wordTrace_append hprefix tailTrace_219755
  have hstable : (prefixWord ++ tailWord_219755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219755).length < 2 ^ (prefixWord ++ tailWord_219755).sum := by decide
  have hdescent : baseEnd_219755 < baseStart_219755 := by decide
  rcases family_descends (prefixWord ++ tailWord_219755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219758 : List Nat := [4, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_219758 : Nat := 118140960795 + 219758 * 2 ^ 59
def prefixEnd_219758 : Nat := 4983230072969 + 3 ^ 40 * 219758 * 2
def baseEnd_219758 : Nat := 100303539262983492901651

theorem tailTrace_219758 : CollatzResearch.WordTrace tailWord_219758 prefixEnd_219758 100303539262983492901651 := by
  unfold tailWord_219758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1001904092232721565432491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5343488491907848348973285 1001904092232721565432491)
  ·
    refine ⟨1502856138349082348148737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1001904092232721565432491 1502856138349082348148737)
    ·
      refine ⟨1127142103761811761111553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1502856138349082348148737 1127142103761811761111553)
      ·
        refine ⟨845356577821358820833665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1127142103761811761111553 845356577821358820833665)
        ·
          refine ⟨634017433366019115625249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 845356577821358820833665 634017433366019115625249)
          ·
            refine ⟨475513075024514336718937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 634017433366019115625249 475513075024514336718937)
            ·
              refine ⟨356634806268385752539203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 475513075024514336718937 356634806268385752539203)
              ·
                refine ⟨534952209402578628808805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 356634806268385752539203 534952209402578628808805)
                ·
                  refine ⟨100303539262983492901651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 534952209402578628808805 100303539262983492901651)
                  ·
                    rfl

theorem cell20_219758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_219758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219758 prefixEnd_219758 := by exact prefixLift 219758
  have htrace : WordTrace (prefixWord ++ tailWord_219758) baseStart_219758 baseEnd_219758 := by
    simpa [prefixWord, tailWord_219758, baseEnd_219758] using wordTrace_append hprefix tailTrace_219758
  have hstable : (prefixWord ++ tailWord_219758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219758).length < 2 ^ (prefixWord ++ tailWord_219758).sum := by decide
  have hdescent : baseEnd_219758 < baseStart_219758 := by decide
  rcases family_descends (prefixWord ++ tailWord_219758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219827 : List Nat := [1, 1, 1, 2, 3, 6, 2, 1, 3]
def baseStart_219827 : Nat := 118140960795 + 219827 * 2 ^ 59
def prefixEnd_219827 : Nat := 4983230072969 + 3 ^ 40 * 219827 * 2
def baseEnd_219827 : Nat := 100335032743125919601369

theorem tailTrace_219827 : CollatzResearch.WordTrace tailWord_219827 prefixEnd_219827 100335032743125919601369 := by
  unfold tailWord_219827
  simp only [CollatzResearch.WordTrace]
  refine ⟨8017749374611797307721735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5345166249741198205147823 8017749374611797307721735)
  ·
    refine ⟨12026624061917695961582603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8017749374611797307721735 12026624061917695961582603)
    ·
      refine ⟨18039936092876543942373905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12026624061917695961582603 18039936092876543942373905)
      ·
        refine ⟨13529952069657407956780429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18039936092876543942373905 13529952069657407956780429)
        ·
          refine ⟨5073732026121527983792661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13529952069657407956780429 5073732026121527983792661)
          ·
            refine ⟨237831188724446624240281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5073732026121527983792661 237831188724446624240281)
            ·
              refine ⟨178373391543334968180211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237831188724446624240281 178373391543334968180211)
              ·
                refine ⟨267560087315002452270317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178373391543334968180211 267560087315002452270317)
                ·
                  refine ⟨100335032743125919601369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267560087315002452270317 100335032743125919601369)
                  ·
                    rfl

theorem cell20_219827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 1, 3].length) (baseStart_219827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219827 prefixEnd_219827 := by exact prefixLift 219827
  have htrace : WordTrace (prefixWord ++ tailWord_219827) baseStart_219827 baseEnd_219827 := by
    simpa [prefixWord, tailWord_219827, baseEnd_219827] using wordTrace_append hprefix tailTrace_219827
  have hstable : (prefixWord ++ tailWord_219827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219827).length < 2 ^ (prefixWord ++ tailWord_219827).sum := by decide
  have hdescent : baseEnd_219827 < baseStart_219827 := by decide
  rcases family_descends (prefixWord ++ tailWord_219827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219862 : List Nat := [5, 2, 1, 12]
def baseStart_219862 : Nat := 118140960795 + 219862 * 2 ^ 59
def prefixEnd_219862 : Nat := 4983230072969 + 3 ^ 40 * 219862 * 2
def baseEnd_219862 : Nat := 412967109863462359813

theorem tailTrace_219862 : CollatzResearch.WordTrace tailWord_219862 prefixEnd_219862 412967109863462359813 := by
  unfold tailWord_219862
  simp only [CollatzResearch.WordTrace]
  refine ⟨501189120592812392827865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5346017286323332190163893 501189120592812392827865)
  ·
    refine ⟨375891840444609294620899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 501189120592812392827865 375891840444609294620899)
    ·
      refine ⟨563837760666913941931349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 375891840444609294620899 563837760666913941931349)
      ·
        refine ⟨412967109863462359813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 563837760666913941931349 412967109863462359813)
        ·
          rfl

theorem cell20_219862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 12].length) (baseStart_219862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219862 prefixEnd_219862 := by exact prefixLift 219862
  have htrace : WordTrace (prefixWord ++ tailWord_219862) baseStart_219862 baseEnd_219862 := by
    simpa [prefixWord, tailWord_219862, baseEnd_219862] using wordTrace_append hprefix tailTrace_219862
  have hstable : (prefixWord ++ tailWord_219862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219862).length < 2 ^ (prefixWord ++ tailWord_219862).sum := by decide
  have hdescent : baseEnd_219862 < baseStart_219862 := by decide
  rcases family_descends (prefixWord ++ tailWord_219862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219868 : List Nat := [2, 2, 5, 1, 1, 1, 4, 2, 2]
def baseStart_219868 : Nat := 118140960795 + 219868 * 2 ^ 59
def prefixEnd_219868 : Nat := 4983230072969 + 3 ^ 40 * 219868 * 2
def baseEnd_219868 : Nat := 100353746260311999234535

theorem tailTrace_219868 : CollatzResearch.WordTrace tailWord_219868 prefixEnd_219868 100353746260311999234535 := by
  unfold tailWord_219868
  simp only [CollatzResearch.WordTrace]
  refine ⟨4009622383731630654982129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5346163178308840873309505 4009622383731630654982129)
  ·
    refine ⟨3007216787798722991236597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4009622383731630654982129 3007216787798722991236597)
    ·
      refine ⟨281926573856130280428431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3007216787798722991236597 281926573856130280428431)
      ·
        refine ⟨422889860784195420642647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281926573856130280428431 422889860784195420642647)
        ·
          refine ⟨634334791176293130963971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422889860784195420642647 634334791176293130963971)
          ·
            refine ⟨951502186764439696445957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634334791176293130963971 951502186764439696445957)
            ·
              refine ⟨178406660018332443083617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 951502186764439696445957 178406660018332443083617)
              ·
                refine ⟨133804995013749332312713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178406660018332443083617 133804995013749332312713)
                ·
                  refine ⟨100353746260311999234535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133804995013749332312713 100353746260311999234535)
                  ·
                    rfl

theorem cell20_219868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 2].length) (baseStart_219868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219868 prefixEnd_219868 := by exact prefixLift 219868
  have htrace : WordTrace (prefixWord ++ tailWord_219868) baseStart_219868 baseEnd_219868 := by
    simpa [prefixWord, tailWord_219868, baseEnd_219868] using wordTrace_append hprefix tailTrace_219868
  have hstable : (prefixWord ++ tailWord_219868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219868).length < 2 ^ (prefixWord ++ tailWord_219868).sum := by decide
  have hdescent : baseEnd_219868 < baseStart_219868 := by decide
  rcases family_descends (prefixWord ++ tailWord_219868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219886 : List Nat := [4, 1, 2, 1, 1, 3, 2, 3, 3]
def baseStart_219886 : Nat := 118140960795 + 219886 * 2 ^ 59
def prefixEnd_219886 : Nat := 4983230072969 + 3 ^ 40 * 219886 * 2
def baseEnd_219886 : Nat := 100361961950783936634461

theorem tailTrace_219886 : CollatzResearch.WordTrace tailWord_219886 prefixEnd_219886 100361961950783936634461 := by
  unfold tailWord_219886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1002487660174756298014939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5346600854265366922746341 1002487660174756298014939)
  ·
    refine ⟨1503731490262134447022409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1002487660174756298014939 1503731490262134447022409)
    ·
      refine ⟨1127798617696600835266807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1503731490262134447022409 1127798617696600835266807)
      ·
        refine ⟨1691697926544901252900211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1127798617696600835266807 1691697926544901252900211)
        ·
          refine ⟨2537546889817351879350317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1691697926544901252900211 2537546889817351879350317)
          ·
            refine ⟨951580083681506954756369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2537546889817351879350317 951580083681506954756369)
            ·
              refine ⟨713685062761130216067277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951580083681506954756369 713685062761130216067277)
              ·
                refine ⟨267631898535423831025229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 713685062761130216067277 267631898535423831025229)
                ·
                  refine ⟨100361961950783936634461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267631898535423831025229 100361961950783936634461)
                  ·
                    rfl

theorem cell20_219886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_219886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219886 prefixEnd_219886 := by exact prefixLift 219886
  have htrace : WordTrace (prefixWord ++ tailWord_219886) baseStart_219886 baseEnd_219886 := by
    simpa [prefixWord, tailWord_219886, baseEnd_219886] using wordTrace_append hprefix tailTrace_219886
  have hstable : (prefixWord ++ tailWord_219886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219886).length < 2 ^ (prefixWord ++ tailWord_219886).sum := by decide
  have hdescent : baseEnd_219886 < baseStart_219886 := by decide
  rcases family_descends (prefixWord ++ tailWord_219886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219914 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_219914 : Nat := 118140960795 + 219914 * 2 ^ 59
def prefixEnd_219914 : Nat := 4983230072969 + 3 ^ 40 * 219914 * 2
def baseEnd_219914 : Nat := 100374741913740283701013

theorem tailTrace_219914 : CollatzResearch.WordTrace tailWord_219914 prefixEnd_219914 100374741913740283701013 := by
  unfold tailWord_219914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2005230631324152791534699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5347281683531074110759197 2005230631324152791534699)
  ·
    refine ⟨3007845946986229187302049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2005230631324152791534699 3007845946986229187302049)
    ·
      refine ⟨2255884460239671890476537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3007845946986229187302049 2255884460239671890476537)
      ·
        refine ⟨1691913345179753917857403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2255884460239671890476537 1691913345179753917857403)
        ·
          refine ⟨2537870017769630876786105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1691913345179753917857403 2537870017769630876786105)
          ·
            refine ⟨1903402513327223157589579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2537870017769630876786105 1903402513327223157589579)
            ·
              refine ⟨2855103769990834736384369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1903402513327223157589579 2855103769990834736384369)
              ·
                refine ⟨2141327827493126052288277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2855103769990834736384369 2141327827493126052288277)
                ·
                  refine ⟨100374741913740283701013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2141327827493126052288277 100374741913740283701013)
                  ·
                    rfl

theorem cell20_219914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_219914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219914 prefixEnd_219914 := by exact prefixLift 219914
  have htrace : WordTrace (prefixWord ++ tailWord_219914) baseStart_219914 baseEnd_219914 := by
    simpa [prefixWord, tailWord_219914, baseEnd_219914] using wordTrace_append hprefix tailTrace_219914
  have hstable : (prefixWord ++ tailWord_219914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219914).length < 2 ^ (prefixWord ++ tailWord_219914).sum := by decide
  have hdescent : baseEnd_219914 < baseStart_219914 := by decide
  rcases family_descends (prefixWord ++ tailWord_219914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219955 : List Nat := [1, 1, 1, 2, 6, 3, 2, 4]
def baseStart_219955 : Nat := 118140960795 + 219955 * 2 ^ 59
def prefixEnd_219955 : Nat := 4983230072969 + 3 ^ 40 * 219955 * 2
def baseEnd_219955 : Nat := 33464485143642121111393

theorem tailTrace_219955 : CollatzResearch.WordTrace tailWord_219955 prefixEnd_219955 33464485143642121111393 := by
  unfold tailWord_219955
  simp only [CollatzResearch.WordTrace]
  refine ⟨8022417918148075168381319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5348278612098716778920879 8022417918148075168381319)
  ·
    refine ⟨12033626877222112752571979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8022417918148075168381319 12033626877222112752571979)
    ·
      refine ⟨18050440315833169128857969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12033626877222112752571979 18050440315833169128857969)
      ·
        refine ⟨13537830236874876846643477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18050440315833169128857969 13537830236874876846643477)
        ·
          refine ⟨634585792353509852186413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13537830236874876846643477 634585792353509852186413)
          ·
            refine ⟨237969672132566194569905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 634585792353509852186413 237969672132566194569905)
            ·
              refine ⟨178477254099424645927429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237969672132566194569905 178477254099424645927429)
              ·
                refine ⟨33464485143642121111393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178477254099424645927429 33464485143642121111393)
                ·
                  rfl

theorem cell20_219955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 2, 4].length) (baseStart_219955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219955 prefixEnd_219955 := by exact prefixLift 219955
  have htrace : WordTrace (prefixWord ++ tailWord_219955) baseStart_219955 baseEnd_219955 := by
    simpa [prefixWord, tailWord_219955, baseEnd_219955] using wordTrace_append hprefix tailTrace_219955
  have hstable : (prefixWord ++ tailWord_219955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219955).length < 2 ^ (prefixWord ++ tailWord_219955).sum := by decide
  have hdescent : baseEnd_219955 < baseStart_219955 := by decide
  rcases family_descends (prefixWord ++ tailWord_219955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219959 : List Nat := [1, 1, 3, 1, 2, 1, 5, 6]
def baseStart_219959 : Nat := 118140960795 + 219959 * 2 ^ 59
def prefixEnd_219959 : Nat := 4983230072969 + 3 ^ 40 * 219959 * 2
def baseEnd_219959 : Nat := 33465093713306709066943

theorem tailTrace_219959 : CollatzResearch.WordTrace tailWord_219959 prefixEnd_219959 33465093713306709066943 := by
  unfold tailWord_219959
  simp only [CollatzResearch.WordTrace]
  refine ⟨8022563810133583851526931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5348375873422389234351287 8022563810133583851526931)
  ·
    refine ⟨12033845715200375777290397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8022563810133583851526931 12033845715200375777290397)
    ·
      refine ⟨4512692143200140916483899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12033845715200375777290397 4512692143200140916483899)
      ·
        refine ⟨6769038214800211374725849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4512692143200140916483899 6769038214800211374725849)
        ·
          refine ⟨5076778661100158531044387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6769038214800211374725849 5076778661100158531044387)
          ·
            refine ⟨7615167991650237796566581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5076778661100158531044387 7615167991650237796566581)
            ·
              refine ⟨713921999217209793428117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7615167991650237796566581 713921999217209793428117)
              ·
                refine ⟨33465093713306709066943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 713921999217209793428117 33465093713306709066943)
                ·
                  rfl

theorem cell20_219959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 6].length) (baseStart_219959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219959 prefixEnd_219959 := by exact prefixLift 219959
  have htrace : WordTrace (prefixWord ++ tailWord_219959) baseStart_219959 baseEnd_219959 := by
    simpa [prefixWord, tailWord_219959, baseEnd_219959] using wordTrace_append hprefix tailTrace_219959
  have hstable : (prefixWord ++ tailWord_219959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219959).length < 2 ^ (prefixWord ++ tailWord_219959).sum := by decide
  have hdescent : baseEnd_219959 < baseStart_219959 := by decide
  rcases family_descends (prefixWord ++ tailWord_219959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219972 : List Nat := [2, 3, 4, 2, 1, 2, 6]
def baseStart_219972 : Nat := 118140960795 + 219972 * 2 ^ 59
def prefixEnd_219972 : Nat := 4983230072969 + 3 ^ 40 * 219972 * 2
def baseEnd_219972 : Nat := 11155690521572206640827

theorem tailTrace_219972 : CollatzResearch.WordTrace tailWord_219972 prefixEnd_219972 11155690521572206640827 := by
  unfold tailWord_219972
  simp only [CollatzResearch.WordTrace]
  refine ⟨4011518979543243535875085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5348691972724324714500113 4011518979543243535875085)
  ·
    refine ⟨1504319617328716325953157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4011518979543243535875085 1504319617328716325953157)
    ·
      refine ⟨282059928249134311116217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1504319617328716325953157 282059928249134311116217)
      ·
        refine ⟨211544946186850733337163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282059928249134311116217 211544946186850733337163)
        ·
          refine ⟨317317419280276100005745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211544946186850733337163 317317419280276100005745)
          ·
            refine ⟨237988064460207075004309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317317419280276100005745 237988064460207075004309)
            ·
              refine ⟨11155690521572206640827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 237988064460207075004309 11155690521572206640827)
              ·
                rfl

theorem cell20_219972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 6].length) (baseStart_219972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219972 prefixEnd_219972 := by exact prefixLift 219972
  have htrace : WordTrace (prefixWord ++ tailWord_219972) baseStart_219972 baseEnd_219972 := by
    simpa [prefixWord, tailWord_219972, baseEnd_219972] using wordTrace_append hprefix tailTrace_219972
  have hstable : (prefixWord ++ tailWord_219972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219972).length < 2 ^ (prefixWord ++ tailWord_219972).sum := by decide
  have hdescent : baseEnd_219972 < baseStart_219972 := by decide
  rcases family_descends (prefixWord ++ tailWord_219972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219996 : List Nat := [2, 2, 4, 2, 1, 3, 2, 1, 3]
def baseStart_219996 : Nat := 118140960795 + 219996 * 2 ^ 59
def prefixEnd_219996 : Nat := 4983230072969 + 3 ^ 40 * 219996 * 2
def baseEnd_219996 : Nat := 100412168948112442967345

theorem tailTrace_219996 : CollatzResearch.WordTrace tailWord_219996 prefixEnd_219996 100412168948112442967345 := by
  unfold tailWord_219996
  simp only [CollatzResearch.WordTrace]
  refine ⟨4011956655499769585311921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5349275540666359447082561 4011956655499769585311921)
  ·
    refine ⟨3008967491624827188983941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4011956655499769585311921 3008967491624827188983941)
    ·
      refine ⟨564181404679655097934489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3008967491624827188983941 564181404679655097934489)
      ·
        refine ⟨423136053509741323450867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564181404679655097934489 423136053509741323450867)
        ·
          refine ⟨634704080264611985176301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423136053509741323450867 634704080264611985176301)
          ·
            refine ⟨238014030099229494441113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 634704080264611985176301 238014030099229494441113)
            ·
              refine ⟨178510522574422120830835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238014030099229494441113 178510522574422120830835)
              ·
                refine ⟨267765783861633181246253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178510522574422120830835 267765783861633181246253)
                ·
                  refine ⟨100412168948112442967345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267765783861633181246253 100412168948112442967345)
                  ·
                    rfl

theorem cell20_219996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_219996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_219996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_219996 prefixEnd_219996 := by exact prefixLift 219996
  have htrace : WordTrace (prefixWord ++ tailWord_219996) baseStart_219996 baseEnd_219996 := by
    simpa [prefixWord, tailWord_219996, baseEnd_219996] using wordTrace_append hprefix tailTrace_219996
  have hstable : (prefixWord ++ tailWord_219996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219996).length < 2 ^ (prefixWord ++ tailWord_219996).sum := by decide
  have hdescent : baseEnd_219996 < baseStart_219996 := by decide
  rcases family_descends (prefixWord ++ tailWord_219996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220041 : List Nat := [1, 2, 1, 1, 5, 4, 2, 2, 2]
def baseStart_220041 : Nat := 118140960795 + 220041 * 2 ^ 59
def prefixEnd_220041 : Nat := 4983230072969 + 3 ^ 40 * 220041 * 2
def baseEnd_220041 : Nat := 100432708174292286467161

theorem tailTrace_220041 : CollatzResearch.WordTrace tailWord_220041 prefixEnd_220041 100432708174292286467161 := by
  unfold tailWord_220041
  simp only [CollatzResearch.WordTrace]
  refine ⟨8025554595836511856011977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5350369730557674570674651 8025554595836511856011977)
  ·
    refine ⟨6019165946877383892008983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8025554595836511856011977 6019165946877383892008983)
    ·
      refine ⟨9028748920316075838013475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6019165946877383892008983 9028748920316075838013475)
      ·
        refine ⟨13543123380474113757020213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9028748920316075838013475 13543123380474113757020213)
        ·
          refine ⟨1269667816919448164720645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13543123380474113757020213 1269667816919448164720645)
          ·
            refine ⟨238062715672396530885121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1269667816919448164720645 238062715672396530885121)
            ·
              refine ⟨178547036754297398163841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238062715672396530885121 178547036754297398163841)
              ·
                refine ⟨133910277565723048622881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178547036754297398163841 133910277565723048622881)
                ·
                  refine ⟨100432708174292286467161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133910277565723048622881 100432708174292286467161)
                  ·
                    rfl

theorem cell20_220041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2, 2].length) (baseStart_220041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220041 prefixEnd_220041 := by exact prefixLift 220041
  have htrace : WordTrace (prefixWord ++ tailWord_220041) baseStart_220041 baseEnd_220041 := by
    simpa [prefixWord, tailWord_220041, baseEnd_220041] using wordTrace_append hprefix tailTrace_220041
  have hstable : (prefixWord ++ tailWord_220041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220041).length < 2 ^ (prefixWord ++ tailWord_220041).sum := by decide
  have hdescent : baseEnd_220041 < baseStart_220041 := by decide
  rcases family_descends (prefixWord ++ tailWord_220041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220093 : List Nat := [1, 4, 1, 2, 4, 2, 1, 2, 3]
def baseStart_220093 : Nat := 118140960795 + 220093 * 2 ^ 59
def prefixEnd_220093 : Nat := 4983230072969 + 3 ^ 40 * 220093 * 2
def baseEnd_220093 : Nat := 100456442391211216733615

theorem tailTrace_220093 : CollatzResearch.WordTrace tailWord_220093 prefixEnd_220093 100456442391211216733615 := by
  unfold tailWord_220093
  simp only [CollatzResearch.WordTrace]
  refine ⟨8027451191648124736904933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5351634127765416491269955 8027451191648124736904933)
  ·
    refine ⟨1505147098434023388169675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8027451191648124736904933 1505147098434023388169675)
    ·
      refine ⟨2257720647651035082254513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1505147098434023388169675 2257720647651035082254513)
      ·
        refine ⟨1693290485738276311690885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2257720647651035082254513 1693290485738276311690885)
        ·
          refine ⟨317491966075926808442041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1693290485738276311690885 317491966075926808442041)
          ·
            refine ⟨238118974556945106331531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317491966075926808442041 238118974556945106331531)
            ·
              refine ⟨357178461835417659497297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238118974556945106331531 357178461835417659497297)
              ·
                refine ⟨267883846376563244622973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357178461835417659497297 267883846376563244622973)
                ·
                  refine ⟨100456442391211216733615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267883846376563244622973 100456442391211216733615)
                  ·
                    rfl

theorem cell20_220093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_220093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220093 prefixEnd_220093 := by exact prefixLift 220093
  have htrace : WordTrace (prefixWord ++ tailWord_220093) baseStart_220093 baseEnd_220093 := by
    simpa [prefixWord, tailWord_220093, baseEnd_220093] using wordTrace_append hprefix tailTrace_220093
  have hstable : (prefixWord ++ tailWord_220093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220093).length < 2 ^ (prefixWord ++ tailWord_220093).sum := by decide
  have hdescent : baseEnd_220093 < baseStart_220093 := by decide
  rcases family_descends (prefixWord ++ tailWord_220093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220135 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 5]
def baseStart_220135 : Nat := 118140960795 + 220135 * 2 ^ 59
def prefixEnd_220135 : Nat := 4983230072969 + 3 ^ 40 * 220135 * 2
def baseEnd_220135 : Nat := 100475612335645737333443

theorem tailTrace_220135 : CollatzResearch.WordTrace tailWord_220135 prefixEnd_220135 100475612335645737333443 := by
  unfold tailWord_220135
  simp only [CollatzResearch.WordTrace]
  refine ⟨8028983057495965909933859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5352655371663977273289239 8028983057495965909933859)
  ·
    refine ⟨12043474586243948864900789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8028983057495965909933859 12043474586243948864900789)
    ·
      refine ⟨1129075742460370206084449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12043474586243948864900789 1129075742460370206084449)
      ·
        refine ⟨846806806845277654563337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1129075742460370206084449 846806806845277654563337)
        ·
          refine ⟨635105105133958240922503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 846806806845277654563337 635105105133958240922503)
          ·
            refine ⟨952657657700937361383755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635105105133958240922503 952657657700937361383755)
            ·
              refine ⟨1428986486551406042075633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952657657700937361383755 1428986486551406042075633)
              ·
                refine ⟨1071739864913554531556725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1428986486551406042075633 1071739864913554531556725)
                ·
                  refine ⟨100475612335645737333443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1071739864913554531556725 100475612335645737333443)
                  ·
                    rfl

theorem cell20_220135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 5].length) (baseStart_220135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220135 prefixEnd_220135 := by exact prefixLift 220135
  have htrace : WordTrace (prefixWord ++ tailWord_220135) baseStart_220135 baseEnd_220135 := by
    simpa [prefixWord, tailWord_220135, baseEnd_220135] using wordTrace_append hprefix tailTrace_220135
  have hstable : (prefixWord ++ tailWord_220135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220135).length < 2 ^ (prefixWord ++ tailWord_220135).sum := by decide
  have hdescent : baseEnd_220135 < baseStart_220135 := by decide
  rcases family_descends (prefixWord ++ tailWord_220135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220138 : List Nat := [3, 1, 3, 1, 2, 2, 3, 3, 2]
def baseStart_220138 : Nat := 118140960795 + 220138 * 2 ^ 59
def prefixEnd_220138 : Nat := 4983230072969 + 3 ^ 40 * 220138 * 2
def baseEnd_220138 : Nat := 100476981617391060233431

theorem tailTrace_220138 : CollatzResearch.WordTrace tailWord_220138 prefixEnd_220138 100476981617391060233431 := by
  unfold tailWord_220138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2007273119121274355573267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5352728317656731614862045 2007273119121274355573267)
  ·
    refine ⟨3010909678681911533359901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2007273119121274355573267 3010909678681911533359901)
    ·
      refine ⟨1129091129505716825009963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3010909678681911533359901 1129091129505716825009963)
      ·
        refine ⟨1693636694258575237514945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129091129505716825009963 1693636694258575237514945)
        ·
          refine ⟨1270227520693931428136209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1693636694258575237514945 1270227520693931428136209)
          ·
            refine ⟨952670640520448571102157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1270227520693931428136209 952670640520448571102157)
            ·
              refine ⟨357251490195168214163309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 952670640520448571102157 357251490195168214163309)
              ·
                refine ⟨133969308823188080311241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357251490195168214163309 133969308823188080311241)
                ·
                  refine ⟨100476981617391060233431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133969308823188080311241 100476981617391060233431)
                  ·
                    rfl

theorem cell20_220138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_220138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220138 prefixEnd_220138 := by exact prefixLift 220138
  have htrace : WordTrace (prefixWord ++ tailWord_220138) baseStart_220138 baseEnd_220138 := by
    simpa [prefixWord, tailWord_220138, baseEnd_220138] using wordTrace_append hprefix tailTrace_220138
  have hstable : (prefixWord ++ tailWord_220138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220138).length < 2 ^ (prefixWord ++ tailWord_220138).sum := by decide
  have hdescent : baseEnd_220138 < baseStart_220138 := by decide
  rcases family_descends (prefixWord ++ tailWord_220138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220162 : List Nat := [3, 4, 1, 3, 1, 1, 2, 5]
def baseStart_220162 : Nat := 118140960795 + 220162 * 2 ^ 59
def prefixEnd_220162 : Nat := 4983230072969 + 3 ^ 40 * 220162 * 2
def baseEnd_220162 : Nat := 33495978623784547811111

theorem tailTrace_220162 : CollatzResearch.WordTrace tailWord_220162 prefixEnd_220162 33495978623784547811111 := by
  unfold tailWord_220162
  simp only [CollatzResearch.WordTrace]
  refine ⟨2007491957099537380291685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5353311885598766347444493 2007491957099537380291685)
  ·
    refine ⟨376404741956163258804691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2007491957099537380291685 376404741956163258804691)
    ·
      refine ⟨564607112934244888207037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376404741956163258804691 564607112934244888207037)
      ·
        refine ⟨211727667350341833077639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 564607112934244888207037 211727667350341833077639)
        ·
          refine ⟨317591501025512749616459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211727667350341833077639 317591501025512749616459)
          ·
            refine ⟨476387251538269124424689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317591501025512749616459 476387251538269124424689)
            ·
              refine ⟨357290438653701843318517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476387251538269124424689 357290438653701843318517)
              ·
                refine ⟨33495978623784547811111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 357290438653701843318517 33495978623784547811111)
                ·
                  rfl

theorem cell20_220162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_220162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220162 prefixEnd_220162 := by exact prefixLift 220162
  have htrace : WordTrace (prefixWord ++ tailWord_220162) baseStart_220162 baseEnd_220162 := by
    simpa [prefixWord, tailWord_220162, baseEnd_220162] using wordTrace_append hprefix tailTrace_220162
  have hstable : (prefixWord ++ tailWord_220162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220162).length < 2 ^ (prefixWord ++ tailWord_220162).sum := by decide
  have hdescent : baseEnd_220162 < baseStart_220162 := by decide
  rcases family_descends (prefixWord ++ tailWord_220162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220197 : List Nat := [1, 3, 1, 2, 2, 2, 2, 5, 2]
def baseStart_220197 : Nat := 118140960795 + 220197 * 2 ^ 59
def prefixEnd_220197 : Nat := 4983230072969 + 3 ^ 40 * 220197 * 2
def baseEnd_220197 : Nat := 100503910825049077266523

theorem tailTrace_220197 : CollatzResearch.WordTrace tailWord_220197 prefixEnd_220197 100503910825049077266523 := by
  unfold tailWord_220197
  simp only [CollatzResearch.WordTrace]
  refine ⟨8031244383271350498690845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5354162922180900332460563 8031244383271350498690845)
  ·
    refine ⟨3011716643726756437009067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8031244383271350498690845 3011716643726756437009067)
    ·
      refine ⟨4517574965590134655513601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3011716643726756437009067 4517574965590134655513601)
      ·
        refine ⟨3388181224192600991635201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4517574965590134655513601 3388181224192600991635201)
        ·
          refine ⟨2541135918144450743726401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3388181224192600991635201 2541135918144450743726401)
          ·
            refine ⟨1905851938608338057794801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2541135918144450743726401 1905851938608338057794801)
            ·
              refine ⟨1429388953956253543346101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1905851938608338057794801 1429388953956253543346101)
              ·
                refine ⟨134005214433398769688697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1429388953956253543346101 134005214433398769688697)
                ·
                  refine ⟨100503910825049077266523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134005214433398769688697 100503910825049077266523)
                  ·
                    rfl

theorem cell20_220197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_220197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220197 prefixEnd_220197 := by exact prefixLift 220197
  have htrace : WordTrace (prefixWord ++ tailWord_220197) baseStart_220197 baseEnd_220197 := by
    simpa [prefixWord, tailWord_220197, baseEnd_220197] using wordTrace_append hprefix tailTrace_220197
  have hstable : (prefixWord ++ tailWord_220197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220197).length < 2 ^ (prefixWord ++ tailWord_220197).sum := by decide
  have hdescent : baseEnd_220197 < baseStart_220197 := by decide
  rcases family_descends (prefixWord ++ tailWord_220197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220252 : List Nat := [2, 2, 4, 1, 1, 1, 4, 3, 2]
def baseStart_220252 : Nat := 118140960795 + 220252 * 2 ^ 59
def prefixEnd_220252 : Nat := 4983230072969 + 3 ^ 40 * 220252 * 2
def baseEnd_220252 : Nat := 100529014323713330432965

theorem tailTrace_220252 : CollatzResearch.WordTrace tailWord_220252 prefixEnd_220252 100529014323713330432965 := by
  unfold tailWord_220252
  simp only [CollatzResearch.WordTrace]
  refine ⟨4016625199036047445971505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5355500265381396594628673 4016625199036047445971505)
  ·
    refine ⟨3012468899277035584478629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4016625199036047445971505 3012468899277035584478629)
    ·
      refine ⟨564837918614444172089743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3012468899277035584478629 564837918614444172089743)
      ·
        refine ⟨847256877921666258134615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564837918614444172089743 847256877921666258134615)
        ·
          refine ⟨1270885316882499387201923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 847256877921666258134615 1270885316882499387201923)
          ·
            refine ⟨1906327975323749080802885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270885316882499387201923 1906327975323749080802885)
            ·
              refine ⟨357436495373202952650541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1906327975323749080802885 357436495373202952650541)
              ·
                refine ⟨134038685764951107243953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357436495373202952650541 134038685764951107243953)
                ·
                  refine ⟨100529014323713330432965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134038685764951107243953 100529014323713330432965)
                  ·
                    rfl

theorem cell20_220252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_220252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220252 prefixEnd_220252 := by exact prefixLift 220252
  have htrace : WordTrace (prefixWord ++ tailWord_220252) baseStart_220252 baseEnd_220252 := by
    simpa [prefixWord, tailWord_220252, baseEnd_220252] using wordTrace_append hprefix tailTrace_220252
  have hstable : (prefixWord ++ tailWord_220252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220252).length < 2 ^ (prefixWord ++ tailWord_220252).sum := by decide
  have hdescent : baseEnd_220252 < baseStart_220252 := by decide
  rcases family_descends (prefixWord ++ tailWord_220252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220263 : List Nat := [1, 1, 5, 1, 1, 4, 7]
def baseStart_220263 : Nat := 118140960795 + 220263 * 2 ^ 59
def prefixEnd_220263 : Nat := 4983230072969 + 3 ^ 40 * 220263 * 2
def baseEnd_220263 : Nat := 11170448335938464562917

theorem tailTrace_220263 : CollatzResearch.WordTrace tailWord_220263 prefixEnd_220263 11170448335938464562917 := by
  unfold tailWord_220263
  simp only [CollatzResearch.WordTrace]
  refine ⟨8033651601032243770593443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5355767734021495847062295 8033651601032243770593443)
  ·
    refine ⟨12050477401548365655890165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8033651601032243770593443 12050477401548365655890165)
    ·
      refine ⟨1129732256395159280239703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12050477401548365655890165 1129732256395159280239703)
      ·
        refine ⟨1694598384592738920359555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129732256395159280239703 1694598384592738920359555)
        ·
          refine ⟨2541897576889108380539333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1694598384592738920359555 2541897576889108380539333)
          ·
            refine ⟨476605795666707821351125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2541897576889108380539333 476605795666707821351125)
            ·
              refine ⟨11170448335938464562917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 476605795666707821351125 11170448335938464562917)
              ·
                rfl

theorem cell20_220263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 7].length) (baseStart_220263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220263 prefixEnd_220263 := by exact prefixLift 220263
  have htrace : WordTrace (prefixWord ++ tailWord_220263) baseStart_220263 baseEnd_220263 := by
    simpa [prefixWord, tailWord_220263, baseEnd_220263] using wordTrace_append hprefix tailTrace_220263
  have hstable : (prefixWord ++ tailWord_220263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220263).length < 2 ^ (prefixWord ++ tailWord_220263).sum := by decide
  have hdescent : baseEnd_220263 < baseStart_220263 := by decide
  rcases family_descends (prefixWord ++ tailWord_220263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220266 : List Nat := [3, 1, 3, 2, 2, 1, 3, 2, 3]
def baseStart_220266 : Nat := 118140960795 + 220266 * 2 ^ 59
def prefixEnd_220266 : Nat := 4983230072969 + 3 ^ 40 * 220266 * 2
def baseEnd_220266 : Nat := 100535404305191503966241

theorem tailTrace_220266 : CollatzResearch.WordTrace tailWord_220266 prefixEnd_220266 100535404305191503966241 := by
  unfold tailWord_220266
  simp only [CollatzResearch.WordTrace]
  refine ⟨2008440255005343820738163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5355840680014250188635101 2008440255005343820738163)
  ·
    refine ⟨3012660382508015731107245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2008440255005343820738163 3012660382508015731107245)
    ·
      refine ⟨1129747643440505899165217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3012660382508015731107245 1129747643440505899165217)
      ·
        refine ⟨847310732580379424373913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1129747643440505899165217 847310732580379424373913)
        ·
          refine ⟨635483049435284568280435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 847310732580379424373913 635483049435284568280435)
          ·
            refine ⟨953224574152926852420653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635483049435284568280435 953224574152926852420653)
            ·
              refine ⟨357459215307347569657745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 953224574152926852420653 357459215307347569657745)
              ·
                refine ⟨268094411480510677243309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357459215307347569657745 268094411480510677243309)
                ·
                  refine ⟨100535404305191503966241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 268094411480510677243309 100535404305191503966241)
                  ·
                    rfl

theorem cell20_220266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_220266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220266 prefixEnd_220266 := by exact prefixLift 220266
  have htrace : WordTrace (prefixWord ++ tailWord_220266) baseStart_220266 baseEnd_220266 := by
    simpa [prefixWord, tailWord_220266, baseEnd_220266] using wordTrace_append hprefix tailTrace_220266
  have hstable : (prefixWord ++ tailWord_220266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220266).length < 2 ^ (prefixWord ++ tailWord_220266).sum := by decide
  have hdescent : baseEnd_220266 < baseStart_220266 := by decide
  rcases family_descends (prefixWord ++ tailWord_220266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220318 : List Nat := [4, 3, 1, 1, 2, 1, 8]
def baseStart_220318 : Nat := 118140960795 + 220318 * 2 ^ 59
def prefixEnd_220318 : Nat := 4983230072969 + 3 ^ 40 * 220318 * 2
def baseEnd_220318 : Nat := 11173237613567826025855

theorem tailTrace_220318 : CollatzResearch.WordTrace tailWord_220318 prefixEnd_220318 11173237613567826025855 := by
  unfold tailWord_220318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1004457201979123520480701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5357105077221992109230405 1004457201979123520480701)
  ·
    refine ⟨376671450742171320180263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1004457201979123520480701 376671450742171320180263)
    ·
      refine ⟨565007176113256980270395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376671450742171320180263 565007176113256980270395)
      ·
        refine ⟨847510764169885470405593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565007176113256980270395 847510764169885470405593)
        ·
          refine ⟨635633073127414102804195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 847510764169885470405593 635633073127414102804195)
          ·
            refine ⟨953449609691121154206293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635633073127414102804195 953449609691121154206293)
            ·
              refine ⟨11173237613567826025855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 953449609691121154206293 11173237613567826025855)
              ·
                rfl

theorem cell20_220318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 8].length) (baseStart_220318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220318 prefixEnd_220318 := by exact prefixLift 220318
  have htrace : WordTrace (prefixWord ++ tailWord_220318) baseStart_220318 baseEnd_220318 := by
    simpa [prefixWord, tailWord_220318, baseEnd_220318] using wordTrace_append hprefix tailTrace_220318
  have hstable : (prefixWord ++ tailWord_220318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220318).length < 2 ^ (prefixWord ++ tailWord_220318).sum := by decide
  have hdescent : baseEnd_220318 < baseStart_220318 := by decide
  rcases family_descends (prefixWord ++ tailWord_220318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220394 : List Nat := [3, 1, 3, 1, 1, 5, 1, 5]
def baseStart_220394 : Nat := 118140960795 + 220394 * 2 ^ 59
def prefixEnd_220394 : Nat := 4983230072969 + 3 ^ 40 * 220394 * 2
def baseEnd_220394 : Nat := 33531275664330649233017

theorem tailTrace_220394 : CollatzResearch.WordTrace tailWord_220394 prefixEnd_220394 33531275664330649233017 := by
  unfold tailWord_220394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2009607390889413285903059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5358953042371768762408157 2009607390889413285903059)
  ·
    refine ⟨3014411086334119928854589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2009607390889413285903059 3014411086334119928854589)
    ·
      refine ⟨1130404157375294973320471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3014411086334119928854589 1130404157375294973320471)
      ·
        refine ⟨1695606236062942459980707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1130404157375294973320471 1695606236062942459980707)
        ·
          refine ⟨2543409354094413689971061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1695606236062942459980707 2543409354094413689971061)
          ·
            refine ⟨238444626946351283434787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2543409354094413689971061 238444626946351283434787)
            ·
              refine ⟨357666940419526925152181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238444626946351283434787 357666940419526925152181)
              ·
                refine ⟨33531275664330649233017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 357666940419526925152181 33531275664330649233017)
                ·
                  rfl

theorem cell20_220394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_220394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220394 prefixEnd_220394 := by exact prefixLift 220394
  have htrace : WordTrace (prefixWord ++ tailWord_220394) baseStart_220394 baseEnd_220394 := by
    simpa [prefixWord, tailWord_220394, baseEnd_220394] using wordTrace_append hprefix tailTrace_220394
  have hstable : (prefixWord ++ tailWord_220394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220394).length < 2 ^ (prefixWord ++ tailWord_220394).sum := by decide
  have hdescent : baseEnd_220394 < baseStart_220394 := by decide
  rcases family_descends (prefixWord ++ tailWord_220394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220425 : List Nat := [1, 2, 1, 1, 3, 3, 4, 3, 2]
def baseStart_220425 : Nat := 118140960795 + 220425 * 2 ^ 59
def prefixEnd_220425 : Nat := 4983230072969 + 3 ^ 40 * 220425 * 2
def baseEnd_220425 : Nat := 100607976237693617665591

theorem tailTrace_220425 : CollatzResearch.WordTrace tailWord_220425 prefixEnd_220425 100607976237693617665591 := by
  unfold tailWord_220425
  simp only [CollatzResearch.WordTrace]
  refine ⟨8039560226445345437990729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5359706817630230291993819 8039560226445345437990729)
  ·
    refine ⟨6029670169834009078493047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8039560226445345437990729 6029670169834009078493047)
    ·
      refine ⟨9044505254751013617739571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6029670169834009078493047 9044505254751013617739571)
      ·
        refine ⟨13566757882126520426609357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9044505254751013617739571 13566757882126520426609357)
        ·
          refine ⟨5087534205797445159978509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13566757882126520426609357 5087534205797445159978509)
          ·
            refine ⟨1907825327174041934991941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5087534205797445159978509 1907825327174041934991941)
            ·
              refine ⟨357717248845132862810989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1907825327174041934991941 357717248845132862810989)
              ·
                refine ⟨134143968316924823554121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357717248845132862810989 134143968316924823554121)
                ·
                  refine ⟨100607976237693617665591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134143968316924823554121 100607976237693617665591)
                  ·
                    rfl

theorem cell20_220425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 2].length) (baseStart_220425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220425 prefixEnd_220425 := by exact prefixLift 220425
  have htrace : WordTrace (prefixWord ++ tailWord_220425) baseStart_220425 baseEnd_220425 := by
    simpa [prefixWord, tailWord_220425, baseEnd_220425] using wordTrace_append hprefix tailTrace_220425
  have hstable : (prefixWord ++ tailWord_220425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220425).length < 2 ^ (prefixWord ++ tailWord_220425).sum := by decide
  have hdescent : baseEnd_220425 < baseStart_220425 := by decide
  rcases family_descends (prefixWord ++ tailWord_220425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220501 : List Nat := [1, 3, 2, 2, 3, 3, 1, 1, 4]
def baseStart_220501 : Nat := 118140960795 + 220501 * 2 ^ 59
def prefixEnd_220501 : Nat := 4983230072969 + 3 ^ 40 * 220501 * 2
def baseEnd_220501 : Nat := 100642664708575131131947

theorem tailTrace_220501 : CollatzResearch.WordTrace tailWord_220501 prefixEnd_220501 100642664708575131131947 := by
  unfold tailWord_220501
  simp only [CollatzResearch.WordTrace]
  refine ⟨8042332174170010417757357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5361554782780006945171571 8042332174170010417757357)
  ·
    refine ⟨3015874565313753906659009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8042332174170010417757357 3015874565313753906659009)
    ·
      refine ⟨2261905923985315429994257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3015874565313753906659009 2261905923985315429994257)
      ·
        refine ⟨1696429442988986572495693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2261905923985315429994257 1696429442988986572495693)
        ·
          refine ⟨636161041120869964685885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1696429442988986572495693 636161041120869964685885)
          ·
            refine ⟨238560390420326236757207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 636161041120869964685885 238560390420326236757207)
            ·
              refine ⟨357840585630489355135811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238560390420326236757207 357840585630489355135811)
              ·
                refine ⟨536760878445734032703717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357840585630489355135811 536760878445734032703717)
                ·
                  refine ⟨100642664708575131131947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 536760878445734032703717 100642664708575131131947)
                  ·
                    rfl

theorem cell20_220501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_220501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220501 prefixEnd_220501 := by exact prefixLift 220501
  have htrace : WordTrace (prefixWord ++ tailWord_220501) baseStart_220501 baseEnd_220501 := by
    simpa [prefixWord, tailWord_220501, baseEnd_220501] using wordTrace_append hprefix tailTrace_220501
  have hstable : (prefixWord ++ tailWord_220501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220501).length < 2 ^ (prefixWord ++ tailWord_220501).sum := by decide
  have hdescent : baseEnd_220501 < baseStart_220501 := by decide
  rcases family_descends (prefixWord ++ tailWord_220501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220515 : List Nat := [1, 1, 1, 5, 2, 3, 1, 3, 3]
def baseStart_220515 : Nat := 118140960795 + 220515 * 2 ^ 59
def prefixEnd_220515 : Nat := 4983230072969 + 3 ^ 40 * 220515 * 2
def baseEnd_220515 : Nat := 100649054690053304665223

theorem tailTrace_220515 : CollatzResearch.WordTrace tailWord_220515 prefixEnd_220515 100649054690053304665223 := by
  unfold tailWord_220515
  simp only [CollatzResearch.WordTrace]
  refine ⟨8042842796119290808766999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5361895197412860539177999 8042842796119290808766999)
  ·
    refine ⟨12064264194178936213150499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8042842796119290808766999 12064264194178936213150499)
    ·
      refine ⟨18096396291268404319725749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12064264194178936213150499 18096396291268404319725749)
      ·
        refine ⟨1696537152306412904974289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18096396291268404319725749 1696537152306412904974289)
        ·
          refine ⟨1272402864229809678730717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1696537152306412904974289 1272402864229809678730717)
          ·
            refine ⟨477151074086178629524019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1272402864229809678730717 477151074086178629524019)
            ·
              refine ⟨715726611129267944286029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477151074086178629524019 715726611129267944286029)
              ·
                refine ⟨268397479173475479107261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 715726611129267944286029 268397479173475479107261)
                ·
                  refine ⟨100649054690053304665223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 268397479173475479107261 100649054690053304665223)
                  ·
                    rfl

theorem cell20_220515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 3].length) (baseStart_220515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220515 prefixEnd_220515 := by exact prefixLift 220515
  have htrace : WordTrace (prefixWord ++ tailWord_220515) baseStart_220515 baseEnd_220515 := by
    simpa [prefixWord, tailWord_220515, baseEnd_220515] using wordTrace_append hprefix tailTrace_220515
  have hstable : (prefixWord ++ tailWord_220515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220515).length < 2 ^ (prefixWord ++ tailWord_220515).sum := by decide
  have hdescent : baseEnd_220515 < baseStart_220515 := by decide
  rcases family_descends (prefixWord ++ tailWord_220515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220546 : List Nat := [3, 4, 2, 1, 1, 9]
def baseStart_220546 : Nat := 118140960795 + 220546 * 2 ^ 59
def prefixEnd_220546 : Nat := 4983230072969 + 3 ^ 40 * 220546 * 2
def baseEnd_220546 : Nat := 3728266812398332393769

theorem tailTrace_220546 : CollatzResearch.WordTrace tailWord_220546 prefixEnd_220546 3728266812398332393769 := by
  unfold tailWord_220546
  simp only [CollatzResearch.WordTrace]
  refine ⟨2010993364751745775786373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5362648972671322068763661 2010993364751745775786373)
  ·
    refine ⟨377061255890952332959945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2010993364751745775786373 377061255890952332959945)
    ·
      refine ⟨282795941918214249719959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 377061255890952332959945 282795941918214249719959)
      ·
        refine ⟨424193912877321374579939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282795941918214249719959 424193912877321374579939)
        ·
          refine ⟨636290869315982061869909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424193912877321374579939 636290869315982061869909)
          ·
            refine ⟨3728266812398332393769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 636290869315982061869909 3728266812398332393769)
            ·
              rfl

theorem cell20_220546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 9].length) (baseStart_220546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220546 prefixEnd_220546 := by exact prefixLift 220546
  have htrace : WordTrace (prefixWord ++ tailWord_220546) baseStart_220546 baseEnd_220546 := by
    simpa [prefixWord, tailWord_220546, baseEnd_220546] using wordTrace_append hprefix tailTrace_220546
  have hstable : (prefixWord ++ tailWord_220546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220546).length < 2 ^ (prefixWord ++ tailWord_220546).sum := by decide
  have hdescent : baseEnd_220546 < baseStart_220546 := by decide
  rcases family_descends (prefixWord ++ tailWord_220546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220588 : List Nat := [2, 2, 1, 1, 1, 1, 4, 8]
def baseStart_220588 : Nat := 118140960795 + 220588 * 2 ^ 59
def prefixEnd_220588 : Nat := 4983230072969 + 3 ^ 40 * 220588 * 2
def baseEnd_220588 : Nat := 33560791293063165077197

theorem tailTrace_220588 : CollatzResearch.WordTrace tailWord_220588 prefixEnd_220588 33560791293063165077197 := by
  unfold tailWord_220588
  simp only [CollatzResearch.WordTrace]
  refine ⟨4022752662427412138087209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5363670216569882850782945 4022752662427412138087209)
  ·
    refine ⟨3017064496820559103565407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4022752662427412138087209 3017064496820559103565407)
    ·
      refine ⟨4525596745230838655348111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3017064496820559103565407 4525596745230838655348111)
      ·
        refine ⟨6788395117846257983022167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4525596745230838655348111 6788395117846257983022167)
        ·
          refine ⟨10182592676769386974533251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6788395117846257983022167 10182592676769386974533251)
          ·
            refine ⟨15273889015154080461799877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10182592676769386974533251 15273889015154080461799877)
            ·
              refine ⟨2863854190341390086587477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15273889015154080461799877 2863854190341390086587477)
              ·
                refine ⟨33560791293063165077197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2863854190341390086587477 33560791293063165077197)
                ·
                  rfl

theorem cell20_220588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_220588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220588 prefixEnd_220588 := by exact prefixLift 220588
  have htrace : WordTrace (prefixWord ++ tailWord_220588) baseStart_220588 baseEnd_220588 := by
    simpa [prefixWord, tailWord_220588, baseEnd_220588] using wordTrace_append hprefix tailTrace_220588
  have hstable : (prefixWord ++ tailWord_220588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220588).length < 2 ^ (prefixWord ++ tailWord_220588).sum := by decide
  have hdescent : baseEnd_220588 < baseStart_220588 := by decide
  rcases family_descends (prefixWord ++ tailWord_220588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220619 : List Nat := [1, 1, 1, 1, 3, 3, 3, 3, 4]
def baseStart_220619 : Nat := 118140960795 + 220619 * 2 ^ 59
def prefixEnd_220619 : Nat := 4983230072969 + 3 ^ 40 * 220619 * 2
def baseEnd_220619 : Nat := 100696523123891165198131

theorem tailTrace_220619 : CollatzResearch.WordTrace tailWord_220619 prefixEnd_220619 100696523123891165198131 := by
  unfold tailWord_220619
  simp only [CollatzResearch.WordTrace]
  refine ⟨8046635987742516570552911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5364423991828344380368607 8046635987742516570552911)
  ·
    refine ⟨12069953981613774855829367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8046635987742516570552911 12069953981613774855829367)
    ·
      refine ⟨18104930972420662283744051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12069953981613774855829367 18104930972420662283744051)
      ·
        refine ⟨27157396458630993425616077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18104930972420662283744051 27157396458630993425616077)
        ·
          refine ⟨10184023671986622534606029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27157396458630993425616077 10184023671986622534606029)
          ·
            refine ⟨3819008876994983450477261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10184023671986622534606029 3819008876994983450477261)
            ·
              refine ⟨1432128328873118793928973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3819008876994983450477261 1432128328873118793928973)
              ·
                refine ⟨537048123327419547723365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1432128328873118793928973 537048123327419547723365)
                ·
                  refine ⟨100696523123891165198131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 537048123327419547723365 100696523123891165198131)
                  ·
                    rfl

theorem cell20_220619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_220619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220619 prefixEnd_220619 := by exact prefixLift 220619
  have htrace : WordTrace (prefixWord ++ tailWord_220619) baseStart_220619 baseEnd_220619 := by
    simpa [prefixWord, tailWord_220619, baseEnd_220619] using wordTrace_append hprefix tailTrace_220619
  have hstable : (prefixWord ++ tailWord_220619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220619).length < 2 ^ (prefixWord ++ tailWord_220619).sum := by decide
  have hdescent : baseEnd_220619 < baseStart_220619 := by decide
  rcases family_descends (prefixWord ++ tailWord_220619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220643 : List Nat := [1, 1, 1, 6, 2, 2, 1, 6]
def baseStart_220643 : Nat := 118140960795 + 220643 * 2 ^ 59
def prefixEnd_220643 : Nat := 4983230072969 + 3 ^ 40 * 220643 * 2
def baseEnd_220643 : Nat := 33569159125951249466011

theorem tailTrace_220643 : CollatzResearch.WordTrace tailWord_220643 prefixEnd_220643 33569159125951249466011 := by
  unfold tailWord_220643
  simp only [CollatzResearch.WordTrace]
  refine ⟨8047511339655568669426583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5365007559770379112951055 8047511339655568669426583)
  ·
    refine ⟨12071267009483353004139875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8047511339655568669426583 12071267009483353004139875)
    ·
      refine ⟨18106900514225029506209813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12071267009483353004139875 18106900514225029506209813)
      ·
        refine ⟨848760961604298258103585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18106900514225029506209813 848760961604298258103585)
        ·
          refine ⟨636570721203223693577689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 848760961604298258103585 636570721203223693577689)
          ·
            refine ⟨477428040902417770183267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 636570721203223693577689 477428040902417770183267)
            ·
              refine ⟨716142061353626655274901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477428040902417770183267 716142061353626655274901)
              ·
                refine ⟨33569159125951249466011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 716142061353626655274901 33569159125951249466011)
                ·
                  rfl

theorem cell20_220643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 6].length) (baseStart_220643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220643 prefixEnd_220643 := by exact prefixLift 220643
  have htrace : WordTrace (prefixWord ++ tailWord_220643) baseStart_220643 baseEnd_220643 := by
    simpa [prefixWord, tailWord_220643, baseEnd_220643] using wordTrace_append hprefix tailTrace_220643
  have hstable : (prefixWord ++ tailWord_220643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220643).length < 2 ^ (prefixWord ++ tailWord_220643).sum := by decide
  have hdescent : baseEnd_220643 < baseStart_220643 := by decide
  rcases family_descends (prefixWord ++ tailWord_220643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220664 : List Nat := [2, 1, 2, 1, 1, 5, 8]
def baseStart_220664 : Nat := 118140960795 + 220664 * 2 ^ 59
def prefixEnd_220664 : Nat := 4983230072969 + 3 ^ 40 * 220664 * 2
def baseEnd_220664 : Nat := 11190784705563445410883

theorem tailTrace_220664 : CollatzResearch.WordTrace tailWord_220664 prefixEnd_220664 11190784705563445410883 := by
  unfold tailWord_220664
  simp only [CollatzResearch.WordTrace]
  refine ⟨4024138636289744627970523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5365518181719659503960697 4024138636289744627970523)
  ·
    refine ⟨6036207954434616941955785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4024138636289744627970523 6036207954434616941955785)
    ·
      refine ⟨4527155965825962706466839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6036207954434616941955785 4527155965825962706466839)
      ·
        refine ⟨6790733948738944059700259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4527155965825962706466839 6790733948738944059700259)
        ·
          refine ⟨10186100923108416089550389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6790733948738944059700259 10186100923108416089550389)
          ·
            refine ⟨954946961541414008395349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10186100923108416089550389 954946961541414008395349)
            ·
              refine ⟨11190784705563445410883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 954946961541414008395349 11190784705563445410883)
              ·
                rfl

theorem cell20_220664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 8].length) (baseStart_220664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220664 prefixEnd_220664 := by exact prefixLift 220664
  have htrace : WordTrace (prefixWord ++ tailWord_220664) baseStart_220664 baseEnd_220664 := by
    simpa [prefixWord, tailWord_220664, baseEnd_220664] using wordTrace_append hprefix tailTrace_220664
  have hstable : (prefixWord ++ tailWord_220664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220664).length < 2 ^ (prefixWord ++ tailWord_220664).sum := by decide
  have hdescent : baseEnd_220664 < baseStart_220664 := by decide
  rcases family_descends (prefixWord ++ tailWord_220664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220729 : List Nat := [1, 2, 1, 5, 1, 3, 1, 4, 2]
def baseStart_220729 : Nat := 118140960795 + 220729 * 2 ^ 59
def prefixEnd_220729 : Nat := 4983230072969 + 3 ^ 40 * 220729 * 2
def baseEnd_220729 : Nat := 100746730121219671531015

theorem tailTrace_220729 : CollatzResearch.WordTrace tailWord_220729 prefixEnd_220729 100746730121219671531015 := by
  unfold tailWord_220729
  simp only [CollatzResearch.WordTrace]
  refine ⟨8050648017344005357057241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5367098678229336904704827 8050648017344005357057241)
  ·
    refine ⟨6037986013008004017792931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8050648017344005357057241 6037986013008004017792931)
    ·
      refine ⟨9056979019512006026689397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6037986013008004017792931 9056979019512006026689397)
      ·
        refine ⟨849091783079250565002131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9056979019512006026689397 849091783079250565002131)
        ·
          refine ⟨1273637674618875847503197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849091783079250565002131 1273637674618875847503197)
          ·
            refine ⟨477614127982078442813699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1273637674618875847503197 477614127982078442813699)
            ·
              refine ⟨716421191973117664220549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477614127982078442813699 716421191973117664220549)
              ·
                refine ⟨134328973494959562041353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 716421191973117664220549 134328973494959562041353)
                ·
                  refine ⟨100746730121219671531015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134328973494959562041353 100746730121219671531015)
                  ·
                    rfl

theorem cell20_220729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 2].length) (baseStart_220729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220729 prefixEnd_220729 := by exact prefixLift 220729
  have htrace : WordTrace (prefixWord ++ tailWord_220729) baseStart_220729 baseEnd_220729 := by
    simpa [prefixWord, tailWord_220729, baseEnd_220729] using wordTrace_append hprefix tailTrace_220729
  have hstable : (prefixWord ++ tailWord_220729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220729).length < 2 ^ (prefixWord ++ tailWord_220729).sum := by decide
  have hdescent : baseEnd_220729 < baseStart_220729 := by decide
  rcases family_descends (prefixWord ++ tailWord_220729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220747 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 7]
def baseStart_220747 : Nat := 118140960795 + 220747 * 2 ^ 59
def prefixEnd_220747 : Nat := 4983230072969 + 3 ^ 40 * 220747 * 2
def baseEnd_220747 : Nat := 100754945811691608930941

theorem tailTrace_220747 : CollatzResearch.WordTrace tailWord_220747 prefixEnd_220747 100754945811691608930941 := by
  unfold tailWord_220747
  simp only [CollatzResearch.WordTrace]
  refine ⟨8051304531278794431212495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5367536354185862954141663 8051304531278794431212495)
  ·
    refine ⟨12076956796918191646818743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8051304531278794431212495 12076956796918191646818743)
    ·
      refine ⟨18115435195377287470228115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12076956796918191646818743 18115435195377287470228115)
      ·
        refine ⟨27173152793065931205342173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18115435195377287470228115 27173152793065931205342173)
        ·
          refine ⟨10189932297399724202003315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27173152793065931205342173 10189932297399724202003315)
          ·
            refine ⟨15284898446099586303004973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10189932297399724202003315 15284898446099586303004973)
            ·
              refine ⟨5731836917287344863626865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15284898446099586303004973 5731836917287344863626865)
              ·
                refine ⟨4298877687965508647720149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5731836917287344863626865 4298877687965508647720149)
                ·
                  refine ⟨100754945811691608930941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4298877687965508647720149 100754945811691608930941)
                  ·
                    rfl

theorem cell20_220747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 7].length) (baseStart_220747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220747 prefixEnd_220747 := by exact prefixLift 220747
  have htrace : WordTrace (prefixWord ++ tailWord_220747) baseStart_220747 baseEnd_220747 := by
    simpa [prefixWord, tailWord_220747, baseEnd_220747] using wordTrace_append hprefix tailTrace_220747
  have hstable : (prefixWord ++ tailWord_220747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220747).length < 2 ^ (prefixWord ++ tailWord_220747).sum := by decide
  have hdescent : baseEnd_220747 < baseStart_220747 := by decide
  rcases family_descends (prefixWord ++ tailWord_220747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220781 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 5]
def baseStart_220781 : Nat := 118140960795 + 220781 * 2 ^ 59
def prefixEnd_220781 : Nat := 4983230072969 + 3 ^ 40 * 220781 * 2
def baseEnd_220781 : Nat := 100770464338138601797469

theorem tailTrace_220781 : CollatzResearch.WordTrace tailWord_220781 prefixEnd_220781 100770464338138601797469 := by
  unfold tailWord_220781
  simp only [CollatzResearch.WordTrace]
  refine ⟨8052544613155618237950197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5368363075437078825300131 8052544613155618237950197)
  ·
    refine ⟨754926057483339209807831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8052544613155618237950197 754926057483339209807831)
    ·
      refine ⟨1132389086225008814711747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 754926057483339209807831 1132389086225008814711747)
      ·
        refine ⟨1698583629337513222067621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1132389086225008814711747 1698583629337513222067621)
        ·
          refine ⟨318484430500783729137679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1698583629337513222067621 318484430500783729137679)
          ·
            refine ⟨477726645751175593706519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318484430500783729137679 477726645751175593706519)
            ·
              refine ⟨716589968626763390559779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 477726645751175593706519 716589968626763390559779)
              ·
                refine ⟨1074884952940145085839669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716589968626763390559779 1074884952940145085839669)
                ·
                  refine ⟨100770464338138601797469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1074884952940145085839669 100770464338138601797469)
                  ·
                    rfl

theorem cell20_220781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_220781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220781 prefixEnd_220781 := by exact prefixLift 220781
  have htrace : WordTrace (prefixWord ++ tailWord_220781) baseStart_220781 baseEnd_220781 := by
    simpa [prefixWord, tailWord_220781, baseEnd_220781] using wordTrace_append hprefix tailTrace_220781
  have hstable : (prefixWord ++ tailWord_220781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220781).length < 2 ^ (prefixWord ++ tailWord_220781).sum := by decide
  have hdescent : baseEnd_220781 < baseStart_220781 := by decide
  rcases family_descends (prefixWord ++ tailWord_220781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220808 : List Nat := [2, 1, 3, 5, 2, 1, 2, 4]
def baseStart_220808 : Nat := 118140960795 + 220808 * 2 ^ 59
def prefixEnd_220808 : Nat := 4983230072969 + 3 ^ 40 * 220808 * 2
def baseEnd_220808 : Nat := 33594262624615502632453

theorem tailTrace_220808 : CollatzResearch.WordTrace tailWord_220808 prefixEnd_220808 33594262624615502632453 := by
  unfold tailWord_220808
  simp only [CollatzResearch.WordTrace]
  refine ⟨4026764692028900924591539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5369019589371867899455385 4026764692028900924591539)
  ·
    refine ⟨6040147038043351386887309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4026764692028900924591539 6040147038043351386887309)
    ·
      refine ⟨2265055139266256770082741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6040147038043351386887309 2265055139266256770082741)
      ·
        refine ⟨212348919306211572195257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2265055139266256770082741 212348919306211572195257)
        ·
          refine ⟨159261689479658679146443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 212348919306211572195257 159261689479658679146443)
          ·
            refine ⟨238892534219488018719665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159261689479658679146443 238892534219488018719665)
            ·
              refine ⟨179169400664616014039749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238892534219488018719665 179169400664616014039749)
              ·
                refine ⟨33594262624615502632453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179169400664616014039749 33594262624615502632453)
                ·
                  rfl

theorem cell20_220808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 2, 4].length) (baseStart_220808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220808 prefixEnd_220808 := by exact prefixLift 220808
  have htrace : WordTrace (prefixWord ++ tailWord_220808) baseStart_220808 baseEnd_220808 := by
    simpa [prefixWord, tailWord_220808, baseEnd_220808] using wordTrace_append hprefix tailTrace_220808
  have hstable : (prefixWord ++ tailWord_220808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220808).length < 2 ^ (prefixWord ++ tailWord_220808).sum := by decide
  have hdescent : baseEnd_220808 < baseStart_220808 := by decide
  rcases family_descends (prefixWord ++ tailWord_220808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220809 : List Nat := [1, 2, 1, 1, 4, 1, 4, 2, 4]
def baseStart_220809 : Nat := 118140960795 + 220809 * 2 ^ 59
def prefixEnd_220809 : Nat := 4983230072969 + 3 ^ 40 * 220809 * 2
def baseEnd_220809 : Nat := 100783244301094948864021

theorem tailTrace_220809 : CollatzResearch.WordTrace tailWord_220809 prefixEnd_220809 100783244301094948864021 := by
  unfold tailWord_220809
  simp only [CollatzResearch.WordTrace]
  refine ⟨8053565857054179019969481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5369043904702786013312987 8053565857054179019969481)
  ·
    refine ⟨6040174392790634264977111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8053565857054179019969481 6040174392790634264977111)
    ·
      refine ⟨9060261589185951397465667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6040174392790634264977111 9060261589185951397465667)
      ·
        refine ⟨13590392383778927096198501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9060261589185951397465667 13590392383778927096198501)
        ·
          refine ⟨2548198571958548830537219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13590392383778927096198501 2548198571958548830537219)
          ·
            refine ⟨3822297857937823245805829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2548198571958548830537219 3822297857937823245805829)
            ·
              refine ⟨716680848363341858588593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3822297857937823245805829 716680848363341858588593)
              ·
                refine ⟨537510636272506393941445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 716680848363341858588593 537510636272506393941445)
                ·
                  refine ⟨100783244301094948864021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 537510636272506393941445 100783244301094948864021)
                  ·
                    rfl

theorem cell20_220809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_220809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220809 prefixEnd_220809 := by exact prefixLift 220809
  have htrace : WordTrace (prefixWord ++ tailWord_220809) baseStart_220809 baseEnd_220809 := by
    simpa [prefixWord, tailWord_220809, baseEnd_220809] using wordTrace_append hprefix tailTrace_220809
  have hstable : (prefixWord ++ tailWord_220809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220809).length < 2 ^ (prefixWord ++ tailWord_220809).sum := by decide
  have hdescent : baseEnd_220809 < baseStart_220809 := by decide
  rcases family_descends (prefixWord ++ tailWord_220809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220833 : List Nat := [1, 2, 3, 3, 2, 3, 6]
def baseStart_220833 : Nat := 118140960795 + 220833 * 2 ^ 59
def prefixEnd_220833 : Nat := 4983230072969 + 3 ^ 40 * 220833 * 2
def baseEnd_220833 : Nat := 11199355395006392451547

theorem tailTrace_220833 : CollatzResearch.WordTrace tailWord_220833 prefixEnd_220833 11199355395006392451547 := by
  unfold tailWord_220833
  simp only [CollatzResearch.WordTrace]
  refine ⟨8054441208967231118843153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5369627472644820745895435 8054441208967231118843153)
  ·
    refine ⟨6040830906725423339132365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8054441208967231118843153 6040830906725423339132365)
    ·
      refine ⟨2265311590022033752174637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6040830906725423339132365 2265311590022033752174637)
      ·
        refine ⟨849491846258262657065489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2265311590022033752174637 849491846258262657065489)
        ·
          refine ⟨637118884693696992799117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 849491846258262657065489 637118884693696992799117)
          ·
            refine ⟨238919581760136372299669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 637118884693696992799117 238919581760136372299669)
            ·
              refine ⟨11199355395006392451547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 238919581760136372299669 11199355395006392451547)
              ·
                rfl

theorem cell20_220833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 6].length) (baseStart_220833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220833 prefixEnd_220833 := by exact prefixLift 220833
  have htrace : WordTrace (prefixWord ++ tailWord_220833) baseStart_220833 baseEnd_220833 := by
    simpa [prefixWord, tailWord_220833, baseEnd_220833] using wordTrace_append hprefix tailTrace_220833
  have hstable : (prefixWord ++ tailWord_220833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220833).length < 2 ^ (prefixWord ++ tailWord_220833).sum := by decide
  have hdescent : baseEnd_220833 < baseStart_220833 := by decide
  rcases family_descends (prefixWord ++ tailWord_220833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220853 : List Nat := [1, 3, 3, 3, 2, 2, 2, 1, 3]
def baseStart_220853 : Nat := 118140960795 + 220853 * 2 ^ 59
def prefixEnd_220853 : Nat := 4983230072969 + 3 ^ 40 * 220853 * 2
def baseEnd_220853 : Nat := 100803327100026351397175

theorem tailTrace_220853 : CollatzResearch.WordTrace tailWord_220853 prefixEnd_220853 100803327100026351397175 := by
  unfold tailWord_220853
  simp only [CollatzResearch.WordTrace]
  refine ⟨8055170668894774534571213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5370113779263183023047475 8055170668894774534571213)
  ·
    refine ⟨3020689000835540450464205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8055170668894774534571213 3020689000835540450464205)
    ·
      refine ⟨1132758375313327668924077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3020689000835540450464205 1132758375313327668924077)
      ·
        refine ⟨424784390742497875846529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1132758375313327668924077 424784390742497875846529)
        ·
          refine ⟨318588293056873406884897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424784390742497875846529 318588293056873406884897)
          ·
            refine ⟨238941219792655055163673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318588293056873406884897 238941219792655055163673)
            ·
              refine ⟨179205914844491291372755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238941219792655055163673 179205914844491291372755)
              ·
                refine ⟨268808872266736937059133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179205914844491291372755 268808872266736937059133)
                ·
                  refine ⟨100803327100026351397175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 268808872266736937059133 100803327100026351397175)
                  ·
                    rfl

theorem cell20_220853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_220853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220853 prefixEnd_220853 := by exact prefixLift 220853
  have htrace : WordTrace (prefixWord ++ tailWord_220853) baseStart_220853 baseEnd_220853 := by
    simpa [prefixWord, tailWord_220853, baseEnd_220853] using wordTrace_append hprefix tailTrace_220853
  have hstable : (prefixWord ++ tailWord_220853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220853).length < 2 ^ (prefixWord ++ tailWord_220853).sum := by decide
  have hdescent : baseEnd_220853 < baseStart_220853 := by decide
  rcases family_descends (prefixWord ++ tailWord_220853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220857 : List Nat := [1, 2, 1, 4, 1, 1, 6, 1, 3]
def baseStart_220857 : Nat := 118140960795 + 220857 * 2 ^ 59
def prefixEnd_220857 : Nat := 4983230072969 + 3 ^ 40 * 220857 * 2
def baseEnd_220857 : Nat := 100805152809020115263825

theorem tailTrace_220857 : CollatzResearch.WordTrace tailWord_220857 prefixEnd_220857 100805152809020115263825 := by
  unfold tailWord_220857
  simp only [CollatzResearch.WordTrace]
  refine ⟨8055316560880283217716825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5370211040586855478477883 8055316560880283217716825)
  ·
    refine ⟨6041487420660212413287619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8055316560880283217716825 6041487420660212413287619)
    ·
      refine ⟨9062231130990318619931429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6041487420660212413287619 9062231130990318619931429)
      ·
        refine ⟨1699168337060684741237143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9062231130990318619931429 1699168337060684741237143)
        ·
          refine ⟨2548752505591027111855715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1699168337060684741237143 2548752505591027111855715)
          ·
            refine ⟨3823128758386540667783573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2548752505591027111855715 3823128758386540667783573)
            ·
              refine ⟨179209160549369093802355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3823128758386540667783573 179209160549369093802355)
              ·
                refine ⟨268813740824053640703533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179209160549369093802355 268813740824053640703533)
                ·
                  refine ⟨100805152809020115263825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 268813740824053640703533 100805152809020115263825)
                  ·
                    rfl

theorem cell20_220857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 3].length) (baseStart_220857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220857 prefixEnd_220857 := by exact prefixLift 220857
  have htrace : WordTrace (prefixWord ++ tailWord_220857) baseStart_220857 baseEnd_220857 := by
    simpa [prefixWord, tailWord_220857, baseEnd_220857] using wordTrace_append hprefix tailTrace_220857
  have hstable : (prefixWord ++ tailWord_220857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220857).length < 2 ^ (prefixWord ++ tailWord_220857).sum := by decide
  have hdescent : baseEnd_220857 < baseStart_220857 := by decide
  rcases family_descends (prefixWord ++ tailWord_220857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220909 : List Nat := [1, 5, 1, 2, 1, 2, 3, 5]
def baseStart_220909 : Nat := 118140960795 + 220909 * 2 ^ 59
def prefixEnd_220909 : Nat := 4983230072969 + 3 ^ 40 * 220909 * 2
def baseEnd_220909 : Nat := 33609629008646348510093

theorem tailTrace_220909 : CollatzResearch.WordTrace tailWord_220909 prefixEnd_220909 33609629008646348510093 := by
  unfold tailWord_220909
  simp only [CollatzResearch.WordTrace]
  refine ⟨8057213156691896098609781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5371475437794597399073187 8057213156691896098609781)
  ·
    refine ⟨755363733439865259244667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8057213156691896098609781 755363733439865259244667)
    ·
      refine ⟨1133045600159797888867001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 755363733439865259244667 1133045600159797888867001)
      ·
        refine ⟨849784200119848416650251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1133045600159797888867001 849784200119848416650251)
        ·
          refine ⟨1274676300179772624975377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 849784200119848416650251 1274676300179772624975377)
          ·
            refine ⟨956007225134829468731533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1274676300179772624975377 956007225134829468731533)
            ·
              refine ⟨358502709425561050774325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 956007225134829468731533 358502709425561050774325)
              ·
                refine ⟨33609629008646348510093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 358502709425561050774325 33609629008646348510093)
                ·
                  rfl

theorem cell20_220909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 5].length) (baseStart_220909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220909 prefixEnd_220909 := by exact prefixLift 220909
  have htrace : WordTrace (prefixWord ++ tailWord_220909) baseStart_220909 baseEnd_220909 := by
    simpa [prefixWord, tailWord_220909, baseEnd_220909] using wordTrace_append hprefix tailTrace_220909
  have hstable : (prefixWord ++ tailWord_220909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220909).length < 2 ^ (prefixWord ++ tailWord_220909).sum := by decide
  have hdescent : baseEnd_220909 < baseStart_220909 := by decide
  rcases family_descends (prefixWord ++ tailWord_220909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220937 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 5]
def baseStart_220937 : Nat := 118140960795 + 220937 * 2 ^ 59
def prefixEnd_220937 : Nat := 4983230072969 + 3 ^ 40 * 220937 * 2
def baseEnd_220937 : Nat := 100841666988895392596831

theorem tailTrace_220937 : CollatzResearch.WordTrace tailWord_220937 prefixEnd_220937 100841666988895392596831 := by
  unfold tailWord_220937
  simp only [CollatzResearch.WordTrace]
  refine ⟨8058234400590456880629065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5372156267060304587086043 8058234400590456880629065)
  ·
    refine ⟨6043675800442842660471799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8058234400590456880629065 6043675800442842660471799)
    ·
      refine ⟨9065513700664263990707699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6043675800442842660471799 9065513700664263990707699)
      ·
        refine ⟨13598270550996395986061549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9065513700664263990707699 13598270550996395986061549)
        ·
          refine ⟨5099351456623648494773081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13598270550996395986061549 5099351456623648494773081)
          ·
            refine ⟨3824513592467736371079811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5099351456623648494773081 3824513592467736371079811)
            ·
              refine ⟨5736770388701604556619717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3824513592467736371079811 5736770388701604556619717)
              ·
                refine ⟨1075644447881550854366197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5736770388701604556619717 1075644447881550854366197)
                ·
                  refine ⟨100841666988895392596831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1075644447881550854366197 100841666988895392596831)
                  ·
                    rfl

theorem cell20_220937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_220937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220937 prefixEnd_220937 := by exact prefixLift 220937
  have htrace : WordTrace (prefixWord ++ tailWord_220937) baseStart_220937 baseEnd_220937 := by
    simpa [prefixWord, tailWord_220937, baseEnd_220937] using wordTrace_append hprefix tailTrace_220937
  have hstable : (prefixWord ++ tailWord_220937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220937).length < 2 ^ (prefixWord ++ tailWord_220937).sum := by decide
  have hdescent : baseEnd_220937 < baseStart_220937 := by decide
  rcases family_descends (prefixWord ++ tailWord_220937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220940 : List Nat := [2, 2, 1, 2, 2, 1, 3, 5, 2]
def baseStart_220940 : Nat := 118140960795 + 220940 * 2 ^ 59
def prefixEnd_220940 : Nat := 4983230072969 + 3 ^ 40 * 220940 * 2
def baseEnd_220940 : Nat := 100843036270640715496819

theorem tailTrace_220940 : CollatzResearch.WordTrace tailWord_220940 prefixEnd_220940 100843036270640715496819 := by
  unfold tailWord_220940
  simp only [CollatzResearch.WordTrace]
  refine ⟨4029171909789794196494137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5372229213053058928658849 4029171909789794196494137)
  ·
    refine ⟨3021878932342345647370603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4029171909789794196494137 3021878932342345647370603)
    ·
      refine ⟨4532818398513518471055905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3021878932342345647370603 4532818398513518471055905)
      ·
        refine ⟨3399613798885138853291929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4532818398513518471055905 3399613798885138853291929)
        ·
          refine ⟨2549710349163854139968947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3399613798885138853291929 2549710349163854139968947)
          ·
            refine ⟨3824565523745781209953421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2549710349163854139968947 3824565523745781209953421)
            ·
              refine ⟨1434212071404667953732533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3824565523745781209953421 1434212071404667953732533)
              ·
                refine ⟨134457381694187620662425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1434212071404667953732533 134457381694187620662425)
                ·
                  refine ⟨100843036270640715496819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134457381694187620662425 100843036270640715496819)
                  ·
                    rfl

theorem cell20_220940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_220940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220940 prefixEnd_220940 := by exact prefixLift 220940
  have htrace : WordTrace (prefixWord ++ tailWord_220940) baseStart_220940 baseEnd_220940 := by
    simpa [prefixWord, tailWord_220940, baseEnd_220940] using wordTrace_append hprefix tailTrace_220940
  have hstable : (prefixWord ++ tailWord_220940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220940).length < 2 ^ (prefixWord ++ tailWord_220940).sum := by decide
  have hdescent : baseEnd_220940 < baseStart_220940 := by decide
  rcases family_descends (prefixWord ++ tailWord_220940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220954 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_220954 : Nat := 118140960795 + 220954 * 2 ^ 59
def prefixEnd_220954 : Nat := 4983230072969 + 3 ^ 40 * 220954 * 2
def baseEnd_220954 : Nat := 100849426252118889030095

theorem tailTrace_220954 : CollatzResearch.WordTrace tailWord_220954 prefixEnd_220954 100849426252118889030095 := by
  unfold tailWord_220954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2014713610382217195999479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5372569627685912522665277 2014713610382217195999479)
  ·
    refine ⟨3022070415573325793999219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2014713610382217195999479 3022070415573325793999219)
    ·
      refine ⟨4533105623359988690998829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3022070415573325793999219 4533105623359988690998829)
      ·
        refine ⟨1699914608759995759124561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4533105623359988690998829 1699914608759995759124561)
        ·
          refine ⟨1274935956569996819343421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1699914608759995759124561 1274935956569996819343421)
          ·
            refine ⟨478100983713748807253783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1274935956569996819343421 478100983713748807253783)
            ·
              refine ⟨717151475570623210880675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478100983713748807253783 717151475570623210880675)
              ·
                refine ⟨1075727213355934816321013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 717151475570623210880675 1075727213355934816321013)
                ·
                  refine ⟨100849426252118889030095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1075727213355934816321013 100849426252118889030095)
                  ·
                    rfl

theorem cell20_220954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_220954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220954 prefixEnd_220954 := by exact prefixLift 220954
  have htrace : WordTrace (prefixWord ++ tailWord_220954) baseStart_220954 baseEnd_220954 := by
    simpa [prefixWord, tailWord_220954, baseEnd_220954] using wordTrace_append hprefix tailTrace_220954
  have hstable : (prefixWord ++ tailWord_220954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220954).length < 2 ^ (prefixWord ++ tailWord_220954).sum := by decide
  have hdescent : baseEnd_220954 < baseStart_220954 := by decide
  rcases family_descends (prefixWord ++ tailWord_220954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220961 : List Nat := [1, 2, 3, 2, 1, 3, 1, 3, 4]
def baseStart_220961 : Nat := 118140960795 + 220961 * 2 ^ 59
def prefixEnd_220961 : Nat := 4983230072969 + 3 ^ 40 * 220961 * 2
def baseEnd_220961 : Nat := 100852621242857975796733

theorem tailTrace_220961 : CollatzResearch.WordTrace tailWord_220961 prefixEnd_220961 100852621242857975796733 := by
  unfold tailWord_220961
  simp only [CollatzResearch.WordTrace]
  refine ⟨8059109752503508979502737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5372739835002339319668491 8059109752503508979502737)
  ·
    refine ⟨6044332314377631734627053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8059109752503508979502737 6044332314377631734627053)
    ·
      refine ⟨2266624617891611900485145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6044332314377631734627053 2266624617891611900485145)
      ·
        refine ⟨1699968463418708925363859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2266624617891611900485145 1699968463418708925363859)
        ·
          refine ⟨2549952695128063388045789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1699968463418708925363859 2549952695128063388045789)
          ·
            refine ⟨956232260673023770517171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2549952695128063388045789 956232260673023770517171)
            ·
              refine ⟨1434348391009535655775757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 956232260673023770517171 1434348391009535655775757)
              ·
                refine ⟨537880646628575870915909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1434348391009535655775757 537880646628575870915909)
                ·
                  refine ⟨100852621242857975796733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 537880646628575870915909 100852621242857975796733)
                  ·
                    rfl

theorem cell20_220961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_220961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220961 prefixEnd_220961 := by exact prefixLift 220961
  have htrace : WordTrace (prefixWord ++ tailWord_220961) baseStart_220961 baseEnd_220961 := by
    simpa [prefixWord, tailWord_220961, baseEnd_220961] using wordTrace_append hprefix tailTrace_220961
  have hstable : (prefixWord ++ tailWord_220961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220961).length < 2 ^ (prefixWord ++ tailWord_220961).sum := by decide
  have hdescent : baseEnd_220961 < baseStart_220961 := by decide
  rcases family_descends (prefixWord ++ tailWord_220961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220981 : List Nat := [1, 3, 3, 1, 5, 1, 2, 4]
def baseStart_220981 : Nat := 118140960795 + 220981 * 2 ^ 59
def prefixEnd_220981 : Nat := 4983230072969 + 3 ^ 40 * 220981 * 2
def baseEnd_220981 : Nat := 33620583262608931709995

theorem tailTrace_220981 : CollatzResearch.WordTrace tailWord_220981 prefixEnd_220981 33620583262608931709995 := by
  unfold tailWord_220981
  simp only [CollatzResearch.WordTrace]
  refine ⟨8059839212431052395230797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5373226141620701596820531 8059839212431052395230797)
  ·
    refine ⟨3022439704661644648211549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8059839212431052395230797 3022439704661644648211549)
    ·
      refine ⟨1133414889248116743079331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3022439704661644648211549 1133414889248116743079331)
      ·
        refine ⟨1700122333872175114618997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1133414889248116743079331 1700122333872175114618997)
        ·
          refine ⟨159386468800516416995531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1700122333872175114618997 159386468800516416995531)
          ·
            refine ⟨239079703200774625493297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159386468800516416995531 239079703200774625493297)
            ·
              refine ⟨179309777400580969119973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239079703200774625493297 179309777400580969119973)
              ·
                refine ⟨33620583262608931709995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179309777400580969119973 33620583262608931709995)
                ·
                  rfl

theorem cell20_220981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 2, 4].length) (baseStart_220981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220981 prefixEnd_220981 := by exact prefixLift 220981
  have htrace : WordTrace (prefixWord ++ tailWord_220981) baseStart_220981 baseEnd_220981 := by
    simpa [prefixWord, tailWord_220981, baseEnd_220981] using wordTrace_append hprefix tailTrace_220981
  have hstable : (prefixWord ++ tailWord_220981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220981).length < 2 ^ (prefixWord ++ tailWord_220981).sum := by decide
  have hdescent : baseEnd_220981 < baseStart_220981 := by decide
  rcases family_descends (prefixWord ++ tailWord_220981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220995 : List Nat := [1, 1, 1, 3, 1, 7, 1, 3, 2]
def baseStart_220995 : Nat := 118140960795 + 220995 * 2 ^ 59
def prefixEnd_220995 : Nat := 4983230072969 + 3 ^ 40 * 220995 * 2
def baseEnd_220995 : Nat := 100868139769304968663261

theorem tailTrace_220995 : CollatzResearch.WordTrace tailWord_220995 prefixEnd_220995 100868139769304968663261 := by
  unfold tailWord_220995
  simp only [CollatzResearch.WordTrace]
  refine ⟨8060349834380332786240439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5373566556253555190826959 8060349834380332786240439)
  ·
    refine ⟨12090524751570499179360659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8060349834380332786240439 12090524751570499179360659)
    ·
      refine ⟨18135787127355748769040989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12090524751570499179360659 18135787127355748769040989)
      ·
        refine ⟨6800920172758405788390371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18135787127355748769040989 6800920172758405788390371)
        ·
          refine ⟨10201380259137608682585557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6800920172758405788390371 10201380259137608682585557)
          ·
            refine ⟨239094849823537703498099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 10201380259137608682585557 239094849823537703498099)
            ·
              refine ⟨358642274735306555247149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239094849823537703498099 358642274735306555247149)
              ·
                refine ⟨134490853025739958217681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358642274735306555247149 134490853025739958217681)
                ·
                  refine ⟨100868139769304968663261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134490853025739958217681 100868139769304968663261)
                  ·
                    rfl

theorem cell20_220995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 3, 2].length) (baseStart_220995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_220995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_220995 prefixEnd_220995 := by exact prefixLift 220995
  have htrace : WordTrace (prefixWord ++ tailWord_220995) baseStart_220995 baseEnd_220995 := by
    simpa [prefixWord, tailWord_220995, baseEnd_220995] using wordTrace_append hprefix tailTrace_220995
  have hstable : (prefixWord ++ tailWord_220995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220995).length < 2 ^ (prefixWord ++ tailWord_220995).sum := by decide
  have hdescent : baseEnd_220995 < baseStart_220995 := by decide
  rcases family_descends (prefixWord ++ tailWord_220995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221012 : List Nat := [2, 4, 1, 1, 3, 2, 3, 2, 2]
def baseStart_221012 : Nat := 118140960795 + 221012 * 2 ^ 59
def prefixEnd_221012 : Nat := 4983230072969 + 3 ^ 40 * 221012 * 2
def baseEnd_221012 : Nat := 100875899032528465096525

theorem tailTrace_221012 : CollatzResearch.WordTrace tailWord_221012 prefixEnd_221012 100875899032528465096525 := by
  unfold tailWord_221012
  simp only [CollatzResearch.WordTrace]
  refine ⟨4030484937659372344804645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5373979916879163126406193 4030484937659372344804645)
  ·
    refine ⟨755715925811132314650871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4030484937659372344804645 755715925811132314650871)
    ·
      refine ⟨1133573888716698471976307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 755715925811132314650871 1133573888716698471976307)
      ·
        refine ⟨1700360833075047707964461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1133573888716698471976307 1700360833075047707964461)
        ·
          refine ⟨637635312403142890486673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1700360833075047707964461 637635312403142890486673)
          ·
            refine ⟨478226484302357167865005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 637635312403142890486673 478226484302357167865005)
            ·
              refine ⟨179334931613383937949377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 478226484302357167865005 179334931613383937949377)
              ·
                refine ⟨134501198710037953462033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179334931613383937949377 134501198710037953462033)
                ·
                  refine ⟨100875899032528465096525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134501198710037953462033 100875899032528465096525)
                  ·
                    rfl

theorem cell20_221012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_221012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221012 prefixEnd_221012 := by exact prefixLift 221012
  have htrace : WordTrace (prefixWord ++ tailWord_221012) baseStart_221012 baseEnd_221012 := by
    simpa [prefixWord, tailWord_221012, baseEnd_221012] using wordTrace_append hprefix tailTrace_221012
  have hstable : (prefixWord ++ tailWord_221012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221012).length < 2 ^ (prefixWord ++ tailWord_221012).sum := by decide
  have hdescent : baseEnd_221012 < baseStart_221012 := by decide
  rcases family_descends (prefixWord ++ tailWord_221012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221026 : List Nat := [3, 3, 2, 1, 2, 1, 4, 1, 3]
def baseStart_221026 : Nat := 118140960795 + 221026 * 2 ^ 59
def prefixEnd_221026 : Nat := 4983230072969 + 3 ^ 40 * 221026 * 2
def baseEnd_221026 : Nat := 100882289014006638629801

theorem tailTrace_221026 : CollatzResearch.WordTrace tailWord_221026 prefixEnd_221026 100882289014006638629801 := by
  unfold tailWord_221026
  simp only [CollatzResearch.WordTrace]
  refine ⟨2015370124317006270154733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5374320331512016720412621 2015370124317006270154733)
  ·
    refine ⟨755763796618877351308025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2015370124317006270154733 755763796618877351308025)
    ·
      refine ⟨566822847464158013481019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 755763796618877351308025 566822847464158013481019)
      ·
        refine ⟨850234271196237020221529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 566822847464158013481019 850234271196237020221529)
        ·
          refine ⟨637675703397177765166147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 850234271196237020221529 637675703397177765166147)
          ·
            refine ⟨956513555095766647749221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637675703397177765166147 956513555095766647749221)
            ·
              refine ⟨179346291580456246452979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 956513555095766647749221 179346291580456246452979)
              ·
                refine ⟨269019437370684369679469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179346291580456246452979 269019437370684369679469)
                ·
                  refine ⟨100882289014006638629801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269019437370684369679469 100882289014006638629801)
                  ·
                    rfl

theorem cell20_221026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_221026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221026 prefixEnd_221026 := by exact prefixLift 221026
  have htrace : WordTrace (prefixWord ++ tailWord_221026) baseStart_221026 baseEnd_221026 := by
    simpa [prefixWord, tailWord_221026, baseEnd_221026] using wordTrace_append hprefix tailTrace_221026
  have hstable : (prefixWord ++ tailWord_221026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221026).length < 2 ^ (prefixWord ++ tailWord_221026).sum := by decide
  have hdescent : baseEnd_221026 < baseStart_221026 := by decide
  rcases family_descends (prefixWord ++ tailWord_221026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221037 : List Nat := [1, 5, 1, 1, 1, 1, 2, 4, 4]
def baseStart_221037 : Nat := 118140960795 + 221037 * 2 ^ 59
def prefixEnd_221037 : Nat := 4983230072969 + 3 ^ 40 * 221037 * 2
def baseEnd_221037 : Nat := 100887309713739489263089

theorem tailTrace_221037 : CollatzResearch.WordTrace tailWord_221037 prefixEnd_221037 100887309713739489263089 := by
  unfold tailWord_221037
  simp only [CollatzResearch.WordTrace]
  refine ⟨8061881700228173959269365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5374587800152115972846243 8061881700228173959269365)
  ·
    refine ⟨755801409396391308681503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8061881700228173959269365 755801409396391308681503)
    ·
      refine ⟨1133702114094586963022255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 755801409396391308681503 1133702114094586963022255)
      ·
        refine ⟨1700553171141880444533383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1133702114094586963022255 1700553171141880444533383)
        ·
          refine ⟨2550829756712820666800075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1700553171141880444533383 2550829756712820666800075)
          ·
            refine ⟨3826244635069231000200113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2550829756712820666800075 3826244635069231000200113)
            ·
              refine ⟨2869683476301923250150085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3826244635069231000200113 2869683476301923250150085)
              ·
                refine ⟨538065651806610609403141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2869683476301923250150085 538065651806610609403141)
                ·
                  refine ⟨100887309713739489263089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 538065651806610609403141 100887309713739489263089)
                  ·
                    rfl

theorem cell20_221037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_221037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221037 prefixEnd_221037 := by exact prefixLift 221037
  have htrace : WordTrace (prefixWord ++ tailWord_221037) baseStart_221037 baseEnd_221037 := by
    simpa [prefixWord, tailWord_221037, baseEnd_221037] using wordTrace_append hprefix tailTrace_221037
  have hstable : (prefixWord ++ tailWord_221037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221037).length < 2 ^ (prefixWord ++ tailWord_221037).sum := by decide
  have hdescent : baseEnd_221037 < baseStart_221037 := by decide
  rcases family_descends (prefixWord ++ tailWord_221037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221109 : List Nat := [1, 3, 3, 2, 1, 3, 2, 3, 2]
def baseStart_221109 : Nat := 118140960795 + 221109 * 2 ^ 59
def prefixEnd_221109 : Nat := 4983230072969 + 3 ^ 40 * 221109 * 2
def baseEnd_221109 : Nat := 100920172475627238862795

theorem tailTrace_221109 : CollatzResearch.WordTrace tailWord_221109 prefixEnd_221109 100920172475627238862795 := by
  unfold tailWord_221109
  simp only [CollatzResearch.WordTrace]
  refine ⟨8064507755967330255890381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5376338503978220170593587 8064507755967330255890381)
  ·
    refine ⟨3024190408487748845958893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8064507755967330255890381 3024190408487748845958893)
    ·
      refine ⟨1134071403182905817234585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3024190408487748845958893 1134071403182905817234585)
      ·
        refine ⟨850553552387179362925939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1134071403182905817234585 850553552387179362925939)
        ·
          refine ⟨1275830328580769044388909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850553552387179362925939 1275830328580769044388909)
          ·
            refine ⟨478436373217788391645841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1275830328580769044388909 478436373217788391645841)
            ·
              refine ⟨358827279913341293734381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478436373217788391645841 358827279913341293734381)
              ·
                refine ⟨134560229967502985150393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358827279913341293734381 134560229967502985150393)
                ·
                  refine ⟨100920172475627238862795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134560229967502985150393 100920172475627238862795)
                  ·
                    rfl

theorem cell20_221109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_221109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221109 prefixEnd_221109 := by exact prefixLift 221109
  have htrace : WordTrace (prefixWord ++ tailWord_221109) baseStart_221109 baseEnd_221109 := by
    simpa [prefixWord, tailWord_221109, baseEnd_221109] using wordTrace_append hprefix tailTrace_221109
  have hstable : (prefixWord ++ tailWord_221109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221109).length < 2 ^ (prefixWord ++ tailWord_221109).sum := by decide
  have hdescent : baseEnd_221109 < baseStart_221109 := by decide
  rcases family_descends (prefixWord ++ tailWord_221109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221130 : List Nat := [3, 1, 2, 1, 2, 1, 4, 4, 2]
def baseStart_221130 : Nat := 118140960795 + 221130 * 2 ^ 59
def prefixEnd_221130 : Nat := 4983230072969 + 3 ^ 40 * 221130 * 2
def baseEnd_221130 : Nat := 100929757447844499162709

theorem tailTrace_221130 : CollatzResearch.WordTrace tailWord_221130 prefixEnd_221130 100929757447844499162709 := by
  unfold tailWord_221130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2016318422222812710601211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5376849125927500561603229 2016318422222812710601211)
  ·
    refine ⟨3024477633334219065901817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2016318422222812710601211 3024477633334219065901817)
    ·
      refine ⟨2268358225000664299426363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3024477633334219065901817 2268358225000664299426363)
      ·
        refine ⟨3402537337500996449139545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2268358225000664299426363 3402537337500996449139545)
        ·
          refine ⟨2551903003125747336854659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3402537337500996449139545 2551903003125747336854659)
          ·
            refine ⟨3827854504688621005281989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2551903003125747336854659 3827854504688621005281989)
            ·
              refine ⟨717722719629116438490373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3827854504688621005281989 717722719629116438490373)
              ·
                refine ⟨134573009930459332216945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 717722719629116438490373 134573009930459332216945)
                ·
                  refine ⟨100929757447844499162709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134573009930459332216945 100929757447844499162709)
                  ·
                    rfl

theorem cell20_221130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_221130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221130 prefixEnd_221130 := by exact prefixLift 221130
  have htrace : WordTrace (prefixWord ++ tailWord_221130) baseStart_221130 baseEnd_221130 := by
    simpa [prefixWord, tailWord_221130, baseEnd_221130] using wordTrace_append hprefix tailTrace_221130
  have hstable : (prefixWord ++ tailWord_221130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221130).length < 2 ^ (prefixWord ++ tailWord_221130).sum := by decide
  have hdescent : baseEnd_221130 < baseStart_221130 := by decide
  rcases family_descends (prefixWord ++ tailWord_221130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221151 : List Nat := [1, 1, 2, 3, 4, 1, 2, 2, 4]
def baseStart_221151 : Nat := 118140960795 + 221151 * 2 ^ 59
def prefixEnd_221151 : Nat := 4983230072969 + 3 ^ 40 * 221151 * 2
def baseEnd_221151 : Nat := 100939342420061759462623

theorem tailTrace_221151 : CollatzResearch.WordTrace tailWord_221151 prefixEnd_221151 100939342420061759462623 := by
  unfold tailWord_221151
  simp only [CollatzResearch.WordTrace]
  refine ⟨8066039621815171428919307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5377359747876780952612871 8066039621815171428919307)
  ·
    refine ⟨12099059432722757143378961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8066039621815171428919307 12099059432722757143378961)
    ·
      refine ⟨9074294574542067857534221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12099059432722757143378961 9074294574542067857534221)
      ·
        refine ⟨3402860465453275446575333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9074294574542067857534221 3402860465453275446575333)
        ·
          refine ⟨638036337272489146232875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3402860465453275446575333 638036337272489146232875)
          ·
            refine ⟨957054505908733719349313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638036337272489146232875 957054505908733719349313)
            ·
              refine ⟨717790879431550289511985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 957054505908733719349313 717790879431550289511985)
              ·
                refine ⟨538343159573662717133989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 717790879431550289511985 538343159573662717133989)
                ·
                  refine ⟨100939342420061759462623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 538343159573662717133989 100939342420061759462623)
                  ·
                    rfl

theorem cell20_221151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 4].length) (baseStart_221151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221151 prefixEnd_221151 := by exact prefixLift 221151
  have htrace : WordTrace (prefixWord ++ tailWord_221151) baseStart_221151 baseEnd_221151 := by
    simpa [prefixWord, tailWord_221151, baseEnd_221151] using wordTrace_append hprefix tailTrace_221151
  have hstable : (prefixWord ++ tailWord_221151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221151).length < 2 ^ (prefixWord ++ tailWord_221151).sum := by decide
  have hdescent : baseEnd_221151 < baseStart_221151 := by decide
  rcases family_descends (prefixWord ++ tailWord_221151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221154 : List Nat := [3, 3, 3, 1, 2, 1, 1, 6]
def baseStart_221154 : Nat := 118140960795 + 221154 * 2 ^ 59
def prefixEnd_221154 : Nat := 4983230072969 + 3 ^ 40 * 221154 * 2
def baseEnd_221154 : Nat := 33646903900602360787537

theorem tailTrace_221154 : CollatzResearch.WordTrace tailWord_221154 prefixEnd_221154 33646903900602360787537 := by
  unfold tailWord_221154
  simp only [CollatzResearch.WordTrace]
  refine ⟨2016537260201075735319629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5377432693869535294185677 2016537260201075735319629)
  ·
    refine ⟨756201472575403400744861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2016537260201075735319629 756201472575403400744861)
    ·
      refine ⟨283575552215776275279323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 756201472575403400744861 283575552215776275279323)
      ·
        refine ⟨425363328323664412918985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283575552215776275279323 425363328323664412918985)
        ·
          refine ⟨319022496242748309689239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425363328323664412918985 319022496242748309689239)
          ·
            refine ⟨478533744364122464533859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319022496242748309689239 478533744364122464533859)
            ·
              refine ⟨717800616546183696800789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478533744364122464533859 717800616546183696800789)
              ·
                refine ⟨33646903900602360787537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 717800616546183696800789 33646903900602360787537)
                ·
                  rfl

theorem cell20_221154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_221154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221154 prefixEnd_221154 := by exact prefixLift 221154
  have htrace : WordTrace (prefixWord ++ tailWord_221154) baseStart_221154 baseEnd_221154 := by
    simpa [prefixWord, tailWord_221154, baseEnd_221154] using wordTrace_append hprefix tailTrace_221154
  have hstable : (prefixWord ++ tailWord_221154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221154).length < 2 ^ (prefixWord ++ tailWord_221154).sum := by decide
  have hdescent : baseEnd_221154 < baseStart_221154 := by decide
  rcases family_descends (prefixWord ++ tailWord_221154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221168 : List Nat := [2, 1, 1, 1, 3, 2, 5, 3, 2]
def baseStart_221168 : Nat := 118140960795 + 221168 * 2 ^ 59
def prefixEnd_221168 : Nat := 4983230072969 + 3 ^ 40 * 221168 * 2
def baseEnd_221168 : Nat := 100947101683285255895887

theorem tailTrace_221168 : CollatzResearch.WordTrace tailWord_221168 prefixEnd_221168 100947101683285255895887 := by
  unfold tailWord_221168
  simp only [CollatzResearch.WordTrace]
  refine ⟨4033329831376791666144079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5377773108502388888192105 4033329831376791666144079)
  ·
    refine ⟨6049994747065187499216119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4033329831376791666144079 6049994747065187499216119)
    ·
      refine ⟨9074992120597781248824179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6049994747065187499216119 9074992120597781248824179)
      ·
        refine ⟨13612488180896671873236269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9074992120597781248824179 13612488180896671873236269)
        ·
          refine ⟨5104683067836251952463601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13612488180896671873236269 5104683067836251952463601)
          ·
            refine ⟨3828512300877188964347701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5104683067836251952463601 3828512300877188964347701)
            ·
              refine ⟨358923028207236465407597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3828512300877188964347701 358923028207236465407597)
              ·
                refine ⟨134596135577713674527849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 358923028207236465407597 134596135577713674527849)
                ·
                  refine ⟨100947101683285255895887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134596135577713674527849 100947101683285255895887)
                  ·
                    rfl

theorem cell20_221168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 2].length) (baseStart_221168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221168 prefixEnd_221168 := by exact prefixLift 221168
  have htrace : WordTrace (prefixWord ++ tailWord_221168) baseStart_221168 baseEnd_221168 := by
    simpa [prefixWord, tailWord_221168, baseEnd_221168] using wordTrace_append hprefix tailTrace_221168
  have hstable : (prefixWord ++ tailWord_221168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221168).length < 2 ^ (prefixWord ++ tailWord_221168).sum := by decide
  have hdescent : baseEnd_221168 < baseStart_221168 := by decide
  rcases family_descends (prefixWord ++ tailWord_221168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221179 : List Nat := [1, 1, 1, 1, 1, 3, 12]
def baseStart_221179 : Nat := 118140960795 + 221179 * 2 ^ 59
def prefixEnd_221179 : Nat := 4983230072969 + 3 ^ 40 * 221179 * 2
def baseEnd_221179 : Nat := 11216902487002011836575

theorem tailTrace_221179 : CollatzResearch.WordTrace tailWord_221179 prefixEnd_221179 11216902487002011836575 := by
  unfold tailWord_221179
  simp only [CollatzResearch.WordTrace]
  refine ⟨8067060865713732210938591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5378040577142488140625727 8067060865713732210938591)
  ·
    refine ⟨12100591298570598316407887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8067060865713732210938591 12100591298570598316407887)
    ·
      refine ⟨18150886947855897474611831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12100591298570598316407887 18150886947855897474611831)
      ·
        refine ⟨27226330421783846211917747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18150886947855897474611831 27226330421783846211917747)
        ·
          refine ⟨40839495632675769317876621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27226330421783846211917747 40839495632675769317876621)
          ·
            refine ⟨15314810862253413494203733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40839495632675769317876621 15314810862253413494203733)
            ·
              refine ⟨11216902487002011836575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 15314810862253413494203733 11216902487002011836575)
              ·
                rfl

theorem cell20_221179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 12].length) (baseStart_221179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221179 prefixEnd_221179 := by exact prefixLift 221179
  have htrace : WordTrace (prefixWord ++ tailWord_221179) baseStart_221179 baseEnd_221179 := by
    simpa [prefixWord, tailWord_221179, baseEnd_221179] using wordTrace_append hprefix tailTrace_221179
  have hstable : (prefixWord ++ tailWord_221179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221179).length < 2 ^ (prefixWord ++ tailWord_221179).sum := by decide
  have hdescent : baseEnd_221179 < baseStart_221179 := by decide
  rcases family_descends (prefixWord ++ tailWord_221179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221185 : List Nat := [1, 2, 4, 1, 2, 1, 5, 2, 2]
def baseStart_221185 : Nat := 118140960795 + 221185 * 2 ^ 59
def prefixEnd_221185 : Nat := 4983230072969 + 3 ^ 40 * 221185 * 2
def baseEnd_221185 : Nat := 100954860946508752329151

theorem tailTrace_221185 : CollatzResearch.WordTrace tailWord_221185 prefixEnd_221185 100954860946508752329151 := by
  unfold tailWord_221185
  simp only [CollatzResearch.WordTrace]
  refine ⟨8067279703691995235657009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5378186469127996823771339 8067279703691995235657009)
  ·
    refine ⟨6050459777768996426742757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8067279703691995235657009 6050459777768996426742757)
    ·
      refine ⟨1134461208331686830014267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6050459777768996426742757 1134461208331686830014267)
      ·
        refine ⟨1701691812497530245021401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1134461208331686830014267 1701691812497530245021401)
        ·
          refine ⟨1276268859373147683766051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1701691812497530245021401 1276268859373147683766051)
          ·
            refine ⟨1914403289059721525649077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276268859373147683766051 1914403289059721525649077)
            ·
              refine ⟨179475308349348893029601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1914403289059721525649077 179475308349348893029601)
              ·
                refine ⟨134606481262011669772201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179475308349348893029601 134606481262011669772201)
                ·
                  refine ⟨100954860946508752329151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134606481262011669772201 100954860946508752329151)
                  ·
                    rfl

theorem cell20_221185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 2].length) (baseStart_221185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221185 prefixEnd_221185 := by exact prefixLift 221185
  have htrace : WordTrace (prefixWord ++ tailWord_221185) baseStart_221185 baseEnd_221185 := by
    simpa [prefixWord, tailWord_221185, baseEnd_221185] using wordTrace_append hprefix tailTrace_221185
  have hstable : (prefixWord ++ tailWord_221185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221185).length < 2 ^ (prefixWord ++ tailWord_221185).sum := by decide
  have hdescent : baseEnd_221185 < baseStart_221185 := by decide
  rcases family_descends (prefixWord ++ tailWord_221185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221189 : List Nat := [1, 3, 1, 1, 2, 4, 3, 1, 4]
def baseStart_221189 : Nat := 118140960795 + 221189 * 2 ^ 59
def prefixEnd_221189 : Nat := 4983230072969 + 3 ^ 40 * 221189 * 2
def baseEnd_221189 : Nat := 100956686655502516195801

theorem tailTrace_221189 : CollatzResearch.WordTrace tailWord_221189 prefixEnd_221189 100956686655502516195801 := by
  unfold tailWord_221189
  simp only [CollatzResearch.WordTrace]
  refine ⟨8067425595677503918802621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5378283730451669279201747 8067425595677503918802621)
  ·
    refine ⟨3025284598379063969550983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8067425595677503918802621 3025284598379063969550983)
    ·
      refine ⟨4537926897568595954326475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3025284598379063969550983 4537926897568595954326475)
      ·
        refine ⟨6806890346352893931489713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4537926897568595954326475 6806890346352893931489713)
        ·
          refine ⟨5105167759764670448617285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6806890346352893931489713 5105167759764670448617285)
          ·
            refine ⟨957218954955875709115741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5105167759764670448617285 957218954955875709115741)
            ·
              refine ⟨358957108108453390918403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 957218954955875709115741 358957108108453390918403)
              ·
                refine ⟨538435662162680086377605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 358957108108453390918403 538435662162680086377605)
                ·
                  refine ⟨100956686655502516195801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 538435662162680086377605 100956686655502516195801)
                  ·
                    rfl

theorem cell20_221189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_221189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221189 prefixEnd_221189 := by exact prefixLift 221189
  have htrace : WordTrace (prefixWord ++ tailWord_221189) baseStart_221189 baseEnd_221189 := by
    simpa [prefixWord, tailWord_221189, baseEnd_221189] using wordTrace_append hprefix tailTrace_221189
  have hstable : (prefixWord ++ tailWord_221189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221189).length < 2 ^ (prefixWord ++ tailWord_221189).sum := by decide
  have hdescent : baseEnd_221189 < baseStart_221189 := by decide
  rcases family_descends (prefixWord ++ tailWord_221189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221196 : List Nat := [2, 2, 1, 2, 3, 1, 4, 5]
def baseStart_221196 : Nat := 118140960795 + 221196 * 2 ^ 59
def prefixEnd_221196 : Nat := 4983230072969 + 3 ^ 40 * 221196 * 2
def baseEnd_221196 : Nat := 33653293882080534320813

theorem tailTrace_221196 : CollatzResearch.WordTrace tailWord_221196 prefixEnd_221196 33653293882080534320813 := by
  unfold tailWord_221196
  simp only [CollatzResearch.WordTrace]
  refine ⟨4033840453326072057153721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5378453937768096076204961 4033840453326072057153721)
  ·
    refine ⟨3025380339994554042865291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4033840453326072057153721 3025380339994554042865291)
    ·
      refine ⟨4538070509991831064297937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3025380339994554042865291 4538070509991831064297937)
      ·
        refine ⟨3403552882493873298223453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4538070509991831064297937 3403552882493873298223453)
        ·
          refine ⟨1276332330935202486833795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3403552882493873298223453 1276332330935202486833795)
          ·
            refine ⟨1914498496402803730250693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276332330935202486833795 1914498496402803730250693)
            ·
              refine ⟨358968468075525699422005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1914498496402803730250693 358968468075525699422005)
              ·
                refine ⟨33653293882080534320813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 358968468075525699422005 33653293882080534320813)
                ·
                  rfl

theorem cell20_221196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_221196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221196 prefixEnd_221196 := by exact prefixLift 221196
  have htrace : WordTrace (prefixWord ++ tailWord_221196) baseStart_221196 baseEnd_221196 := by
    simpa [prefixWord, tailWord_221196, baseEnd_221196] using wordTrace_append hprefix tailTrace_221196
  have hstable : (prefixWord ++ tailWord_221196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221196).length < 2 ^ (prefixWord ++ tailWord_221196).sum := by decide
  have hdescent : baseEnd_221196 < baseStart_221196 := by decide
  rcases family_descends (prefixWord ++ tailWord_221196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221236 : List Nat := [2, 5, 1, 2, 3, 1, 2, 2, 2]
def baseStart_221236 : Nat := 118140960795 + 221236 * 2 ^ 59
def prefixEnd_221236 : Nat := 4983230072969 + 3 ^ 40 * 221236 * 2
def baseEnd_221236 : Nat := 100978138736179241628943

theorem tailTrace_221236 : CollatzResearch.WordTrace tailWord_221236 prefixEnd_221236 100978138736179241628943 := by
  unfold tailWord_221236
  simp only [CollatzResearch.WordTrace]
  refine ⟨4034569913253615472881781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5379426551004820630509041 4034569913253615472881781)
  ·
    refine ⟨378240929367526450582667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4034569913253615472881781 378240929367526450582667)
    ·
      refine ⟨567361394051289675874001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378240929367526450582667 567361394051289675874001)
      ·
        refine ⟨425521045538467256905501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567361394051289675874001 425521045538467256905501)
        ·
          refine ⟨159570392076925221339563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425521045538467256905501 159570392076925221339563)
          ·
            refine ⟨239355588115387832009345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159570392076925221339563 239355588115387832009345)
            ·
              refine ⟨179516691086540874007009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239355588115387832009345 179516691086540874007009)
              ·
                refine ⟨134637518314905655505257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179516691086540874007009 134637518314905655505257)
                ·
                  refine ⟨100978138736179241628943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134637518314905655505257 100978138736179241628943)
                  ·
                    rfl

theorem cell20_221236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_221236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221236 prefixEnd_221236 := by exact prefixLift 221236
  have htrace : WordTrace (prefixWord ++ tailWord_221236) baseStart_221236 baseEnd_221236 := by
    simpa [prefixWord, tailWord_221236, baseEnd_221236] using wordTrace_append hprefix tailTrace_221236
  have hstable : (prefixWord ++ tailWord_221236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221236).length < 2 ^ (prefixWord ++ tailWord_221236).sum := by decide
  have hdescent : baseEnd_221236 < baseStart_221236 := by decide
  rcases family_descends (prefixWord ++ tailWord_221236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221240 : List Nat := [2, 1, 2, 1, 6, 2, 2, 2, 2]
def baseStart_221240 : Nat := 118140960795 + 221240 * 2 ^ 59
def prefixEnd_221240 : Nat := 4983230072969 + 3 ^ 40 * 221240 * 2
def baseEnd_221240 : Nat := 100979964445173005495593

theorem tailTrace_221240 : CollatzResearch.WordTrace tailWord_221240 prefixEnd_221240 100979964445173005495593 := by
  unfold tailWord_221240
  simp only [CollatzResearch.WordTrace]
  refine ⟨4034642859246369814454587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5379523812328493085939449 4034642859246369814454587)
  ·
    refine ⟨6051964288869554721681881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4034642859246369814454587 6051964288869554721681881)
    ·
      refine ⟨4538973216652166041261411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6051964288869554721681881 4538973216652166041261411)
      ·
        refine ⟨6808459824978249061892117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4538973216652166041261411 6808459824978249061892117)
        ·
          refine ⟨319146554295855424776193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6808459824978249061892117 319146554295855424776193)
          ·
            refine ⟨239359915721891568582145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319146554295855424776193 239359915721891568582145)
            ·
              refine ⟨179519936791418676436609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239359915721891568582145 179519936791418676436609)
              ·
                refine ⟨134639952593564007327457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179519936791418676436609 134639952593564007327457)
                ·
                  refine ⟨100979964445173005495593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134639952593564007327457 100979964445173005495593)
                  ·
                    rfl

theorem cell20_221240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 2, 2].length) (baseStart_221240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221240 prefixEnd_221240 := by exact prefixLift 221240
  have htrace : WordTrace (prefixWord ++ tailWord_221240) baseStart_221240 baseEnd_221240 := by
    simpa [prefixWord, tailWord_221240, baseEnd_221240] using wordTrace_append hprefix tailTrace_221240
  have hstable : (prefixWord ++ tailWord_221240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221240).length < 2 ^ (prefixWord ++ tailWord_221240).sum := by decide
  have hdescent : baseEnd_221240 < baseStart_221240 := by decide
  rcases family_descends (prefixWord ++ tailWord_221240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221244 : List Nat := [2, 2, 2, 2, 2, 1, 3, 4, 2]
def baseStart_221244 : Nat := 118140960795 + 221244 * 2 ^ 59
def prefixEnd_221244 : Nat := 4983230072969 + 3 ^ 40 * 221244 * 2
def baseEnd_221244 : Nat := 100981790154166769362243

theorem tailTrace_221244 : CollatzResearch.WordTrace tailWord_221244 prefixEnd_221244 100981790154166769362243 := by
  unfold tailWord_221244
  simp only [CollatzResearch.WordTrace]
  refine ⟨4034715805239124156027393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5379621073652165541369857 4034715805239124156027393)
  ·
    refine ⟨3026036853929343117020545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4034715805239124156027393 3026036853929343117020545)
    ·
      refine ⟨2269527640447007337765409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3026036853929343117020545 2269527640447007337765409)
      ·
        refine ⟨1702145730335255503324057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2269527640447007337765409 1702145730335255503324057)
        ·
          refine ⟨1276609297751441627493043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1702145730335255503324057 1276609297751441627493043)
          ·
            refine ⟨1914913946627162441239565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1276609297751441627493043 1914913946627162441239565)
            ·
              refine ⟨718092729985185915464837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1914913946627162441239565 718092729985185915464837)
              ·
                refine ⟨134642386872222359149657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 718092729985185915464837 134642386872222359149657)
                ·
                  refine ⟨100981790154166769362243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134642386872222359149657 100981790154166769362243)
                  ·
                    rfl

theorem cell20_221244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_221244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221244 prefixEnd_221244 := by exact prefixLift 221244
  have htrace : WordTrace (prefixWord ++ tailWord_221244) baseStart_221244 baseEnd_221244 := by
    simpa [prefixWord, tailWord_221244, baseEnd_221244] using wordTrace_append hprefix tailTrace_221244
  have hstable : (prefixWord ++ tailWord_221244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221244).length < 2 ^ (prefixWord ++ tailWord_221244).sum := by decide
  have hdescent : baseEnd_221244 < baseStart_221244 := by decide
  rcases family_descends (prefixWord ++ tailWord_221244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221296 : List Nat := [2, 1, 1, 1, 5, 2, 3, 2, 3]
def baseStart_221296 : Nat := 118140960795 + 221296 * 2 ^ 59
def prefixEnd_221296 : Nat := 4983230072969 + 3 ^ 40 * 221296 * 2
def baseEnd_221296 : Nat := 101005524371085699628697

theorem tailTrace_221296 : CollatzResearch.WordTrace tailWord_221296 prefixEnd_221296 101005524371085699628697 := by
  unfold tailWord_221296
  simp only [CollatzResearch.WordTrace]
  refine ⟨4035664103144930596473871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5380885470859907461965161 4035664103144930596473871)
  ·
    refine ⟨6053496154717395894710807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4035664103144930596473871 6053496154717395894710807)
    ·
      refine ⟨9080244232076093842066211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6053496154717395894710807 9080244232076093842066211)
      ·
        refine ⟨13620366348114140763099317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9080244232076093842066211 13620366348114140763099317)
        ·
          refine ⟨1276909345135700696540561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13620366348114140763099317 1276909345135700696540561)
          ·
            refine ⟨957682008851775522405421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1276909345135700696540561 957682008851775522405421)
            ·
              refine ⟨359130753319415820902033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 957682008851775522405421 359130753319415820902033)
              ·
                refine ⟨269348064989561865676525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359130753319415820902033 269348064989561865676525)
                ·
                  refine ⟨101005524371085699628697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269348064989561865676525 101005524371085699628697)
                  ·
                    rfl

theorem cell20_221296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_221296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221296 prefixEnd_221296 := by exact prefixLift 221296
  have htrace : WordTrace (prefixWord ++ tailWord_221296) baseStart_221296 baseEnd_221296 := by
    simpa [prefixWord, tailWord_221296, baseEnd_221296] using wordTrace_append hprefix tailTrace_221296
  have hstable : (prefixWord ++ tailWord_221296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221296).length < 2 ^ (prefixWord ++ tailWord_221296).sum := by decide
  have hdescent : baseEnd_221296 < baseStart_221296 := by decide
  rcases family_descends (prefixWord ++ tailWord_221296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221303 : List Nat := [1, 1, 3, 1, 1, 6, 2, 1, 4]
def baseStart_221303 : Nat := 118140960795 + 221303 * 2 ^ 59
def prefixEnd_221303 : Nat := 4983230072969 + 3 ^ 40 * 221303 * 2
def baseEnd_221303 : Nat := 101008719361824786395335

theorem tailTrace_221303 : CollatzResearch.WordTrace tailWord_221303 prefixEnd_221303 101008719361824786395335 := by
  unfold tailWord_221303
  simp only [CollatzResearch.WordTrace]
  refine ⟨8071583517264501388452563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5381055678176334258968375 8071583517264501388452563)
  ·
    refine ⟨12107375275896752082678845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8071583517264501388452563 12107375275896752082678845)
    ·
      refine ⟨4540265728461282031004567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12107375275896752082678845 4540265728461282031004567)
      ·
        refine ⟨6810398592691923046506851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4540265728461282031004567 6810398592691923046506851)
        ·
          refine ⟨10215597889037884569760277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6810398592691923046506851 10215597889037884569760277)
          ·
            refine ⟨478856151048650839207513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 10215597889037884569760277 478856151048650839207513)
            ·
              refine ⟨359142113286488129405635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478856151048650839207513 359142113286488129405635)
              ·
                refine ⟨538713169929732194108453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359142113286488129405635 538713169929732194108453)
                ·
                  refine ⟨101008719361824786395335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 538713169929732194108453 101008719361824786395335)
                  ·
                    rfl

theorem cell20_221303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 4].length) (baseStart_221303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221303 prefixEnd_221303 := by exact prefixLift 221303
  have htrace : WordTrace (prefixWord ++ tailWord_221303) baseStart_221303 baseEnd_221303 := by
    simpa [prefixWord, tailWord_221303, baseEnd_221303] using wordTrace_append hprefix tailTrace_221303
  have hstable : (prefixWord ++ tailWord_221303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221303).length < 2 ^ (prefixWord ++ tailWord_221303).sum := by decide
  have hdescent : baseEnd_221303 < baseStart_221303 := by decide
  rcases family_descends (prefixWord ++ tailWord_221303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221354 : List Nat := [3, 1, 5, 1, 3, 1, 1, 1, 4]
def baseStart_221354 : Nat := 118140960795 + 221354 * 2 ^ 59
def prefixEnd_221354 : Nat := 4983230072969 + 3 ^ 40 * 221354 * 2
def baseEnd_221354 : Nat := 101031997151495275695127

theorem tailTrace_221354 : CollatzResearch.WordTrace tailWord_221354 prefixEnd_221354 101031997151495275695127 := by
  unfold tailWord_221354
  simp only [CollatzResearch.WordTrace]
  refine ⟨2018360910019934274639779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5382295760053158065706077 2018360910019934274639779)
  ·
    refine ⟨3027541365029901411959669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2018360910019934274639779 3027541365029901411959669)
    ·
      refine ⟨283832002971553257371219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3027541365029901411959669 283832002971553257371219)
      ·
        refine ⟨425748004457329886056829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283832002971553257371219 425748004457329886056829)
        ·
          refine ⟨159655501671498707271311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 425748004457329886056829 159655501671498707271311)
          ·
            refine ⟨239483252507248060906967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159655501671498707271311 239483252507248060906967)
            ·
              refine ⟨359224878760872091360451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239483252507248060906967 359224878760872091360451)
              ·
                refine ⟨538837318141308137040677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359224878760872091360451 538837318141308137040677)
                ·
                  refine ⟨101031997151495275695127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 538837318141308137040677 101031997151495275695127)
                  ·
                    rfl

theorem cell20_221354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_221354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221354 prefixEnd_221354 := by exact prefixLift 221354
  have htrace : WordTrace (prefixWord ++ tailWord_221354) baseStart_221354 baseEnd_221354 := by
    simpa [prefixWord, tailWord_221354, baseEnd_221354] using wordTrace_append hprefix tailTrace_221354
  have hstable : (prefixWord ++ tailWord_221354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221354).length < 2 ^ (prefixWord ++ tailWord_221354).sum := by decide
  have hdescent : baseEnd_221354 < baseStart_221354 := by decide
  rcases family_descends (prefixWord ++ tailWord_221354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221413 : List Nat := [1, 3, 1, 4, 2, 1, 4, 2, 2]
def baseStart_221413 : Nat := 118140960795 + 221413 * 2 ^ 59
def prefixEnd_221413 : Nat := 4983230072969 + 3 ^ 40 * 221413 * 2
def baseEnd_221413 : Nat := 101058926359153292728219

theorem tailTrace_221413 : CollatzResearch.WordTrace tailWord_221413 prefixEnd_221413 101058926359153292728219 := by
  unfold tailWord_221413
  simp only [CollatzResearch.WordTrace]
  refine ⟨8075595546865990174956893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5383730364577326783304595 8075595546865990174956893)
  ·
    refine ⟨3028348330074746315608835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8075595546865990174956893 3028348330074746315608835)
    ·
      refine ⟨4542522495112119473413253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3028348330074746315608835 4542522495112119473413253)
      ·
        refine ⟨851722967833522401264985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4542522495112119473413253 851722967833522401264985)
        ·
          refine ⟨638792225875141800948739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 851722967833522401264985 638792225875141800948739)
          ·
            refine ⟨958188338812712701423109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638792225875141800948739 958188338812712701423109)
            ·
              refine ⟨179660313527383631516833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 958188338812712701423109 179660313527383631516833)
              ·
                refine ⟨134745235145537723637625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179660313527383631516833 134745235145537723637625)
                ·
                  refine ⟨101058926359153292728219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134745235145537723637625 101058926359153292728219)
                  ·
                    rfl

theorem cell20_221413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 2].length) (baseStart_221413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221413 prefixEnd_221413 := by exact prefixLift 221413
  have htrace : WordTrace (prefixWord ++ tailWord_221413) baseStart_221413 baseEnd_221413 := by
    simpa [prefixWord, tailWord_221413, baseEnd_221413] using wordTrace_append hprefix tailTrace_221413
  have hstable : (prefixWord ++ tailWord_221413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221413).length < 2 ^ (prefixWord ++ tailWord_221413).sum := by decide
  have hdescent : baseEnd_221413 < baseStart_221413 := by decide
  rcases family_descends (prefixWord ++ tailWord_221413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221417 : List Nat := [1, 2, 1, 1, 1, 2, 2, 8, 2]
def baseStart_221417 : Nat := 118140960795 + 221417 * 2 ^ 59
def prefixEnd_221417 : Nat := 4983230072969 + 3 ^ 40 * 221417 * 2
def baseEnd_221417 : Nat := 101060752068147056594869

theorem tailTrace_221417 : CollatzResearch.WordTrace tailWord_221417 prefixEnd_221417 101060752068147056594869 := by
  unfold tailWord_221417
  simp only [CollatzResearch.WordTrace]
  refine ⟨8075741438851498858102505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5383827625900999238735003 8075741438851498858102505)
  ·
    refine ⟨6056806079138624143576879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8075741438851498858102505 6056806079138624143576879)
    ·
      refine ⟨9085209118707936215365319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6056806079138624143576879 9085209118707936215365319)
      ·
        refine ⟨13627813678061904323047979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9085209118707936215365319 13627813678061904323047979)
        ·
          refine ⟨20441720517092856484571969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13627813678061904323047979 20441720517092856484571969)
          ·
            refine ⟨15331290387819642363428977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20441720517092856484571969 15331290387819642363428977)
            ·
              refine ⟨11498467790864731772571733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15331290387819642363428977 11498467790864731772571733)
              ·
                refine ⟨134747669424196075459825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11498467790864731772571733 134747669424196075459825)
                ·
                  refine ⟨101060752068147056594869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134747669424196075459825 101060752068147056594869)
                  ·
                    rfl

theorem cell20_221417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 8, 2].length) (baseStart_221417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221417 prefixEnd_221417 := by exact prefixLift 221417
  have htrace : WordTrace (prefixWord ++ tailWord_221417) baseStart_221417 baseEnd_221417 := by
    simpa [prefixWord, tailWord_221417, baseEnd_221417] using wordTrace_append hprefix tailTrace_221417
  have hstable : (prefixWord ++ tailWord_221417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221417).length < 2 ^ (prefixWord ++ tailWord_221417).sum := by decide
  have hdescent : baseEnd_221417 < baseStart_221417 := by decide
  rcases family_descends (prefixWord ++ tailWord_221417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221472 : List Nat := [2, 1, 1, 5, 2, 1, 2, 4, 2]
def baseStart_221472 : Nat := 118140960795 + 221472 * 2 ^ 59
def prefixEnd_221472 : Nat := 4983230072969 + 3 ^ 40 * 221472 * 2
def baseEnd_221472 : Nat := 101085855566811309761311

theorem tailTrace_221472 : CollatzResearch.WordTrace tailWord_221472 prefixEnd_221472 101085855566811309761311 := by
  unfold tailWord_221472
  simp only [CollatzResearch.WordTrace]
  refine ⟨4038873726826121625677335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5385164969101495500903113 4038873726826121625677335)
  ·
    refine ⟨6058310590239182438516003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4038873726826121625677335 6058310590239182438516003)
    ·
      refine ⟨9087465885358773657774005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6058310590239182438516003 9087465885358773657774005)
      ·
        refine ⟨851949926752385030416313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9087465885358773657774005 851949926752385030416313)
        ·
          refine ⟨638962445064288772812235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 851949926752385030416313 638962445064288772812235)
          ·
            refine ⟨958443667596433159218353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 638962445064288772812235 958443667596433159218353)
            ·
              refine ⟨718832750697324869413765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 958443667596433159218353 718832750697324869413765)
              ·
                refine ⟨134781140755748413015081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 718832750697324869413765 134781140755748413015081)
                ·
                  refine ⟨101085855566811309761311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134781140755748413015081 101085855566811309761311)
                  ·
                    rfl

theorem cell20_221472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 2].length) (baseStart_221472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221472 prefixEnd_221472 := by exact prefixLift 221472
  have htrace : WordTrace (prefixWord ++ tailWord_221472) baseStart_221472 baseEnd_221472 := by
    simpa [prefixWord, tailWord_221472, baseEnd_221472] using wordTrace_append hprefix tailTrace_221472
  have hstable : (prefixWord ++ tailWord_221472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221472).length < 2 ^ (prefixWord ++ tailWord_221472).sum := by decide
  have hdescent : baseEnd_221472 < baseStart_221472 := by decide
  rcases family_descends (prefixWord ++ tailWord_221472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221482 : List Nat := [3, 1, 4, 2, 2, 1, 3, 1, 3]
def baseStart_221482 : Nat := 118140960795 + 221482 * 2 ^ 59
def prefixEnd_221482 : Nat := 4983230072969 + 3 ^ 40 * 221482 * 2
def baseEnd_221482 : Nat := 101090419839295719427937

theorem tailTrace_221482 : CollatzResearch.WordTrace tailWord_221482 prefixEnd_221482 101090419839295719427937 := by
  unfold tailWord_221482
  simp only [CollatzResearch.WordTrace]
  refine ⟨2019528045904003739804675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5385408122410676639479133 2019528045904003739804675)
  ·
    refine ⟨3029292068856005609707013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2019528045904003739804675 3029292068856005609707013)
    ·
      refine ⟨567992262910501051820065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3029292068856005609707013 567992262910501051820065)
      ·
        refine ⟨425994197182875788865049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 567992262910501051820065 425994197182875788865049)
        ·
          refine ⟨319495647887156841648787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 425994197182875788865049 319495647887156841648787)
          ·
            refine ⟨479243471830735262473181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319495647887156841648787 479243471830735262473181)
            ·
              refine ⟨179716301936525723427443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 479243471830735262473181 179716301936525723427443)
              ·
                refine ⟨269574452904788585141165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179716301936525723427443 269574452904788585141165)
                ·
                  refine ⟨101090419839295719427937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269574452904788585141165 101090419839295719427937)
                  ·
                    rfl

theorem cell20_221482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_221482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221482 prefixEnd_221482 := by exact prefixLift 221482
  have htrace : WordTrace (prefixWord ++ tailWord_221482) baseStart_221482 baseEnd_221482 := by
    simpa [prefixWord, tailWord_221482, baseEnd_221482] using wordTrace_append hprefix tailTrace_221482
  have hstable : (prefixWord ++ tailWord_221482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221482).length < 2 ^ (prefixWord ++ tailWord_221482).sum := by decide
  have hdescent : baseEnd_221482 < baseStart_221482 := by decide
  rcases family_descends (prefixWord ++ tailWord_221482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221521 : List Nat := [1, 2, 2, 1, 4, 2, 8]
def baseStart_221521 : Nat := 118140960795 + 221521 * 2 ^ 59
def prefixEnd_221521 : Nat := 4983230072969 + 3 ^ 40 * 221521 * 2
def baseEnd_221521 : Nat := 11234246722442768569753

theorem tailTrace_221521 : CollatzResearch.WordTrace tailWord_221521 prefixEnd_221521 11234246722442768569753 := by
  unfold tailWord_221521
  simp only [CollatzResearch.WordTrace]
  refine ⟨8079534630474724619888417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5386356420316483079925611 8079534630474724619888417)
  ·
    refine ⟨6059650972856043464916313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8079534630474724619888417 6059650972856043464916313)
    ·
      refine ⟨4544738229642032598687235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6059650972856043464916313 4544738229642032598687235)
      ·
        refine ⟨6817107344463048898030853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4544738229642032598687235 6817107344463048898030853)
        ·
          refine ⟨1278207627086821668380785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6817107344463048898030853 1278207627086821668380785)
          ·
            refine ⟨958655720315116251285589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1278207627086821668380785 958655720315116251285589)
            ·
              refine ⟨11234246722442768569753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 958655720315116251285589 11234246722442768569753)
              ·
                rfl

theorem cell20_221521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 8].length) (baseStart_221521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221521 prefixEnd_221521 := by exact prefixLift 221521
  have htrace : WordTrace (prefixWord ++ tailWord_221521) baseStart_221521 baseEnd_221521 := by
    simpa [prefixWord, tailWord_221521, baseEnd_221521] using wordTrace_append hprefix tailTrace_221521
  have hstable : (prefixWord ++ tailWord_221521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221521).length < 2 ^ (prefixWord ++ tailWord_221521).sum := by decide
  have hdescent : baseEnd_221521 < baseStart_221521 := by decide
  rcases family_descends (prefixWord ++ tailWord_221521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221538 : List Nat := [3, 3, 2, 1, 1, 2, 1, 7]
def baseStart_221538 : Nat := 118140960795 + 221538 * 2 ^ 59
def prefixEnd_221538 : Nat := 4983230072969 + 3 ^ 40 * 221538 * 2
def baseEnd_221538 : Nat := 33705326588402804520347

theorem tailTrace_221538 : CollatzResearch.WordTrace tailWord_221538 prefixEnd_221538 33705326588402804520347 := by
  unfold tailWord_221538
  simp only [CollatzResearch.WordTrace]
  refine ⟨2020038667853284130814317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5386769780942091015504845 2020038667853284130814317)
  ·
    refine ⟨757514500444981549055369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2020038667853284130814317 757514500444981549055369)
    ·
      refine ⟨568135875333736161791527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 757514500444981549055369 568135875333736161791527)
      ·
        refine ⟨852203813000604242687291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568135875333736161791527 852203813000604242687291)
        ·
          refine ⟨1278305719500906364030937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852203813000604242687291 1278305719500906364030937)
          ·
            refine ⟨958729289625679773023203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1278305719500906364030937 958729289625679773023203)
            ·
              refine ⟨1438093934438519659534805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 958729289625679773023203 1438093934438519659534805)
              ·
                refine ⟨33705326588402804520347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1438093934438519659534805 33705326588402804520347)
                ·
                  rfl

theorem cell20_221538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_221538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221538 prefixEnd_221538 := by exact prefixLift 221538
  have htrace : WordTrace (prefixWord ++ tailWord_221538) baseStart_221538 baseEnd_221538 := by
    simpa [prefixWord, tailWord_221538, baseEnd_221538] using wordTrace_append hprefix tailTrace_221538
  have hstable : (prefixWord ++ tailWord_221538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221538).length < 2 ^ (prefixWord ++ tailWord_221538).sum := by decide
  have hdescent : baseEnd_221538 < baseStart_221538 := by decide
  rcases family_descends (prefixWord ++ tailWord_221538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221541 : List Nat := [1, 3, 1, 3, 1, 5, 2, 1, 3]
def baseStart_221541 : Nat := 118140960795 + 221541 * 2 ^ 59
def prefixEnd_221541 : Nat := 4983230072969 + 3 ^ 40 * 221541 * 2
def baseEnd_221541 : Nat := 101117349046953736461029

theorem tailTrace_221541 : CollatzResearch.WordTrace tailWord_221541 prefixEnd_221541 101117349046953736461029 := by
  unfold tailWord_221541
  simp only [CollatzResearch.WordTrace]
  refine ⟨8080264090402268035616477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5386842726934845357077651 8080264090402268035616477)
  ·
    refine ⟨3030099033900850513356179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8080264090402268035616477 3030099033900850513356179)
    ·
      refine ⟨4545148550851275770034269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3030099033900850513356179 4545148550851275770034269)
      ·
        refine ⟨1704430706569228413762851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4545148550851275770034269 1704430706569228413762851)
        ·
          refine ⟨2556646059853842620644277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1704430706569228413762851 2556646059853842620644277)
          ·
            refine ⟨239685568111297745685401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2556646059853842620644277 239685568111297745685401)
            ·
              refine ⟨179764176083473309264051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239685568111297745685401 179764176083473309264051)
              ·
                refine ⟨269646264125209963896077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179764176083473309264051 269646264125209963896077)
                ·
                  refine ⟨101117349046953736461029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269646264125209963896077 101117349046953736461029)
                  ·
                    rfl

theorem cell20_221541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_221541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221541 prefixEnd_221541 := by exact prefixLift 221541
  have htrace : WordTrace (prefixWord ++ tailWord_221541) baseStart_221541 baseEnd_221541 := by
    simpa [prefixWord, tailWord_221541, baseEnd_221541] using wordTrace_append hprefix tailTrace_221541
  have hstable : (prefixWord ++ tailWord_221541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221541).length < 2 ^ (prefixWord ++ tailWord_221541).sum := by decide
  have hdescent : baseEnd_221541 < baseStart_221541 := by decide
  rcases family_descends (prefixWord ++ tailWord_221541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221545 : List Nat := [1, 2, 1, 1, 1, 3, 5, 3, 3]
def baseStart_221545 : Nat := 118140960795 + 221545 * 2 ^ 59
def prefixEnd_221545 : Nat := 4983230072969 + 3 ^ 40 * 221545 * 2
def baseEnd_221545 : Nat := 101119174755947500327679

theorem tailTrace_221545 : CollatzResearch.WordTrace tailWord_221545 prefixEnd_221545 101119174755947500327679 := by
  unfold tailWord_221545
  simp only [CollatzResearch.WordTrace]
  refine ⟨8080409982387776718762089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5386939988258517812508059 8080409982387776718762089)
  ·
    refine ⟨6060307486790832539071567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8080409982387776718762089 6060307486790832539071567)
    ·
      refine ⟨9090461230186248808607351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6060307486790832539071567 9090461230186248808607351)
      ·
        refine ⟨13635691845279373212911027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9090461230186248808607351 13635691845279373212911027)
        ·
          refine ⟨20453537767919059819366541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13635691845279373212911027 20453537767919059819366541)
          ·
            refine ⟨7670076662969647432262453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20453537767919059819366541 7670076662969647432262453)
            ·
              refine ⟨719069687153404446774605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7670076662969647432262453 719069687153404446774605)
              ·
                refine ⟨269651132682526667540477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 719069687153404446774605 269651132682526667540477)
                ·
                  refine ⟨101119174755947500327679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269651132682526667540477 101119174755947500327679)
                  ·
                    rfl

theorem cell20_221545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_221545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221545 prefixEnd_221545 := by exact prefixLift 221545
  have htrace : WordTrace (prefixWord ++ tailWord_221545) baseStart_221545 baseEnd_221545 := by
    simpa [prefixWord, tailWord_221545, baseEnd_221545] using wordTrace_append hprefix tailTrace_221545
  have hstable : (prefixWord ++ tailWord_221545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221545).length < 2 ^ (prefixWord ++ tailWord_221545).sum := by decide
  have hdescent : baseEnd_221545 < baseStart_221545 := by decide
  rcases family_descends (prefixWord ++ tailWord_221545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221582 : List Nat := [4, 1, 1, 4, 1, 3, 2, 2, 2]
def baseStart_221582 : Nat := 118140960795 + 221582 * 2 ^ 59
def prefixEnd_221582 : Nat := 4983230072969 + 3 ^ 40 * 221582 * 2
def baseEnd_221582 : Nat := 101136062564139816094195

theorem tailTrace_221582 : CollatzResearch.WordTrace tailWord_221582 prefixEnd_221582 101136062564139816094195 := by
  unfold tailWord_221582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1010219935406716504732375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5387839655502488025239333 1010219935406716504732375)
  ·
    refine ⟨1515329903110074757098563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1010219935406716504732375 1515329903110074757098563)
    ·
      refine ⟨2272994854665112135647845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1515329903110074757098563 2272994854665112135647845)
      ·
        refine ⟨426186535249708525433971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2272994854665112135647845 426186535249708525433971)
        ·
          refine ⟨639279802874562788150957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426186535249708525433971 639279802874562788150957)
          ·
            refine ⟨239729926077961045556609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 639279802874562788150957 239729926077961045556609)
            ·
              refine ⟨179797444558470784167457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239729926077961045556609 179797444558470784167457)
              ·
                refine ⟨134848083418853088125593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179797444558470784167457 134848083418853088125593)
                ·
                  refine ⟨101136062564139816094195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134848083418853088125593 101136062564139816094195)
                  ·
                    rfl

theorem cell20_221582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_221582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221582 prefixEnd_221582 := by exact prefixLift 221582
  have htrace : WordTrace (prefixWord ++ tailWord_221582) baseStart_221582 baseEnd_221582 := by
    simpa [prefixWord, tailWord_221582, baseEnd_221582] using wordTrace_append hprefix tailTrace_221582
  have hstable : (prefixWord ++ tailWord_221582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221582).length < 2 ^ (prefixWord ++ tailWord_221582).sum := by decide
  have hdescent : baseEnd_221582 < baseStart_221582 := by decide
  rcases family_descends (prefixWord ++ tailWord_221582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221607 : List Nat := [1, 1, 6, 1, 1, 3, 1, 2, 4]
def baseStart_221607 : Nat := 118140960795 + 221607 * 2 ^ 59
def prefixEnd_221607 : Nat := 4983230072969 + 3 ^ 40 * 221607 * 2
def baseEnd_221607 : Nat := 101147473245350840260759

theorem tailTrace_221607 : CollatzResearch.WordTrace tailWord_221607 prefixEnd_221607 101147473245350840260759 := by
  unfold tailWord_221607
  simp only [CollatzResearch.WordTrace]
  refine ⟨8082671308163161307519075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5388447538775440871679383 8082671308163161307519075)
  ·
    refine ⟨12124006962244741961278613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8082671308163161307519075 12124006962244741961278613)
    ·
      refine ⟨568312826355222279434935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12124006962244741961278613 568312826355222279434935)
      ·
        refine ⟨852469239532833419152403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568312826355222279434935 852469239532833419152403)
        ·
          refine ⟨1278703859299250128728605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852469239532833419152403 1278703859299250128728605)
          ·
            refine ⟨479513947237218798273227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1278703859299250128728605 479513947237218798273227)
            ·
              refine ⟨719270920855828197409841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479513947237218798273227 719270920855828197409841)
              ·
                refine ⟨539453190641871148057381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 719270920855828197409841 539453190641871148057381)
                ·
                  refine ⟨101147473245350840260759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 539453190641871148057381 101147473245350840260759)
                  ·
                    rfl

theorem cell20_221607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 4].length) (baseStart_221607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221607 prefixEnd_221607 := by exact prefixLift 221607
  have htrace : WordTrace (prefixWord ++ tailWord_221607) baseStart_221607 baseEnd_221607 := by
    simpa [prefixWord, tailWord_221607, baseEnd_221607] using wordTrace_append hprefix tailTrace_221607
  have hstable : (prefixWord ++ tailWord_221607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221607).length < 2 ^ (prefixWord ++ tailWord_221607).sum := by decide
  have hdescent : baseEnd_221607 < baseStart_221607 := by decide
  rcases family_descends (prefixWord ++ tailWord_221607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221680 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 7]
def baseStart_221680 : Nat := 118140960795 + 221680 * 2 ^ 59
def prefixEnd_221680 : Nat := 4983230072969 + 3 ^ 40 * 221680 * 2
def baseEnd_221680 : Nat := 101180792434487030827127

theorem tailTrace_221680 : CollatzResearch.WordTrace tailWord_221680 prefixEnd_221680 101180792434487030827127 := by
  unfold tailWord_221680
  simp only [CollatzResearch.WordTrace]
  refine ⟨4042666918449347387463247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5390222557932463183284329 4042666918449347387463247)
  ·
    refine ⟨6064000377674021081194871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4042666918449347387463247 6064000377674021081194871)
    ·
      refine ⟨9096000566511031621792307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6064000377674021081194871 9096000566511031621792307)
      ·
        refine ⟨13644000849766547432688461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9096000566511031621792307 13644000849766547432688461)
        ·
          refine ⟨5116500318662455287258173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13644000849766547432688461 5116500318662455287258173)
          ·
            refine ⟨1918687619498420732721815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5116500318662455287258173 1918687619498420732721815)
            ·
              refine ⟨2878031429247631099082723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1918687619498420732721815 2878031429247631099082723)
              ·
                refine ⟨4317047143871446648624085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2878031429247631099082723 4317047143871446648624085)
                ·
                  refine ⟨101180792434487030827127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4317047143871446648624085 101180792434487030827127)
                  ·
                    rfl

theorem cell20_221680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_221680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221680 prefixEnd_221680 := by exact prefixLift 221680
  have htrace : WordTrace (prefixWord ++ tailWord_221680) baseStart_221680 baseEnd_221680 := by
    simpa [prefixWord, tailWord_221680, baseEnd_221680] using wordTrace_append hprefix tailTrace_221680
  have hstable : (prefixWord ++ tailWord_221680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221680).length < 2 ^ (prefixWord ++ tailWord_221680).sum := by decide
  have hdescent : baseEnd_221680 < baseStart_221680 := by decide
  rcases family_descends (prefixWord ++ tailWord_221680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221697 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 5]
def baseStart_221697 : Nat := 118140960795 + 221697 * 2 ^ 59
def prefixEnd_221697 : Nat := 4983230072969 + 3 ^ 40 * 221697 * 2
def baseEnd_221697 : Nat := 101188551697710527260391

theorem tailTrace_221697 : CollatzResearch.WordTrace tailWord_221697 prefixEnd_221697 101188551697710527260391 := by
  unfold tailWord_221697
  simp only [CollatzResearch.WordTrace]
  refine ⟨8085953877837106678295345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5390635918558071118863563 8085953877837106678295345)
  ·
    refine ⟨6064465408377830008721509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8085953877837106678295345 6064465408377830008721509)
    ·
      refine ⟨1137087264070843126635283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6064465408377830008721509 1137087264070843126635283)
      ·
        refine ⟨1705630896106264689952925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1137087264070843126635283 1705630896106264689952925)
        ·
          refine ⟨639611586039849258732347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1705630896106264689952925 639611586039849258732347)
          ·
            refine ⟨959417379059773888098521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639611586039849258732347 959417379059773888098521)
            ·
              refine ⟨719563034294830416073891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 959417379059773888098521 719563034294830416073891)
              ·
                refine ⟨1079344551442245624110837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719563034294830416073891 1079344551442245624110837)
                ·
                  refine ⟨101188551697710527260391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1079344551442245624110837 101188551697710527260391)
                  ·
                    rfl

theorem cell20_221697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_221697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221697 prefixEnd_221697 := by exact prefixLift 221697
  have htrace : WordTrace (prefixWord ++ tailWord_221697) baseStart_221697 baseEnd_221697 := by
    simpa [prefixWord, tailWord_221697, baseEnd_221697] using wordTrace_append hprefix tailTrace_221697
  have hstable : (prefixWord ++ tailWord_221697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221697).length < 2 ^ (prefixWord ++ tailWord_221697).sum := by decide
  have hdescent : baseEnd_221697 < baseStart_221697 := by decide
  rcases family_descends (prefixWord ++ tailWord_221697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221700 : List Nat := [2, 3, 2, 3, 1, 3, 1, 1, 4]
def baseStart_221700 : Nat := 118140960795 + 221700 * 2 ^ 59
def prefixEnd_221700 : Nat := 4983230072969 + 3 ^ 40 * 221700 * 2
def baseEnd_221700 : Nat := 101189920979455850160379

theorem tailTrace_221700 : CollatzResearch.WordTrace tailWord_221700 prefixEnd_221700 101189920979455850160379 := by
  unfold tailWord_221700
  simp only [CollatzResearch.WordTrace]
  refine ⟨4043031648413119095327277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5390708864550825460436369 4043031648413119095327277)
  ·
    refine ⟨1516136868154919660747729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4043031648413119095327277 1516136868154919660747729)
    ·
      refine ⟨1137102651116189745560797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1516136868154919660747729 1137102651116189745560797)
      ·
        refine ⟨426413494168571154585299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1137102651116189745560797 426413494168571154585299)
        ·
          refine ⟨639620241252856731877949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426413494168571154585299 639620241252856731877949)
          ·
            refine ⟨239857590469821274454231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 639620241252856731877949 239857590469821274454231)
            ·
              refine ⟨359786385704731911681347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239857590469821274454231 359786385704731911681347)
              ·
                refine ⟨539679578557097867522021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359786385704731911681347 539679578557097867522021)
                ·
                  refine ⟨101189920979455850160379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 539679578557097867522021 101189920979455850160379)
                  ·
                    rfl

theorem cell20_221700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_221700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221700 prefixEnd_221700 := by exact prefixLift 221700
  have htrace : WordTrace (prefixWord ++ tailWord_221700) baseStart_221700 baseEnd_221700 := by
    simpa [prefixWord, tailWord_221700, baseEnd_221700] using wordTrace_append hprefix tailTrace_221700
  have hstable : (prefixWord ++ tailWord_221700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221700).length < 2 ^ (prefixWord ++ tailWord_221700).sum := by decide
  have hdescent : baseEnd_221700 < baseStart_221700 := by decide
  rcases family_descends (prefixWord ++ tailWord_221700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221748 : List Nat := [2, 5, 1, 3, 1, 1, 2, 2, 3]
def baseStart_221748 : Nat := 118140960795 + 221748 * 2 ^ 59
def prefixEnd_221748 : Nat := 4983230072969 + 3 ^ 40 * 221748 * 2
def baseEnd_221748 : Nat := 101211829487381016560183

theorem tailTrace_221748 : CollatzResearch.WordTrace tailWord_221748 prefixEnd_221748 101211829487381016560183 := by
  unfold tailWord_221748
  simp only [CollatzResearch.WordTrace]
  refine ⟨4043907000326171194200949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5391876000434894925601265 4043907000326171194200949)
  ·
    refine ⟨379116281280578549456339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4043907000326171194200949 379116281280578549456339)
    ·
      refine ⟨568674421920867824184509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379116281280578549456339 568674421920867824184509)
      ·
        refine ⟨213252908220325434069191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 568674421920867824184509 213252908220325434069191)
        ·
          refine ⟨319879362330488151103787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213252908220325434069191 319879362330488151103787)
          ·
            refine ⟨479819043495732226655681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319879362330488151103787 479819043495732226655681)
            ·
              refine ⟨359864282621799169991761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479819043495732226655681 359864282621799169991761)
              ·
                refine ⟨269898211966349377493821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359864282621799169991761 269898211966349377493821)
                ·
                  refine ⟨101211829487381016560183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269898211966349377493821 101211829487381016560183)
                  ·
                    rfl

theorem cell20_221748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_221748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221748 prefixEnd_221748 := by exact prefixLift 221748
  have htrace : WordTrace (prefixWord ++ tailWord_221748) baseStart_221748 baseEnd_221748 := by
    simpa [prefixWord, tailWord_221748, baseEnd_221748] using wordTrace_append hprefix tailTrace_221748
  have hstable : (prefixWord ++ tailWord_221748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221748).length < 2 ^ (prefixWord ++ tailWord_221748).sum := by decide
  have hdescent : baseEnd_221748 < baseStart_221748 := by decide
  rcases family_descends (prefixWord ++ tailWord_221748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221759 : List Nat := [1, 1, 2, 2, 3, 2, 3, 4, 2]
def baseStart_221759 : Nat := 118140960795 + 221759 * 2 ^ 59
def prefixEnd_221759 : Nat := 4983230072969 + 3 ^ 40 * 221759 * 2
def baseEnd_221759 : Nat := 101216850187113867193471

theorem tailTrace_221759 : CollatzResearch.WordTrace tailWord_221759 prefixEnd_221759 101216850187113867193471 := by
  unfold tailWord_221759
  simp only [CollatzResearch.WordTrace]
  refine ⟨8088215203612491267052331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5392143469074994178034887 8088215203612491267052331)
  ·
    refine ⟨12132322805418736900578497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8088215203612491267052331 12132322805418736900578497)
    ·
      refine ⟨9099242104064052675433873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12132322805418736900578497 9099242104064052675433873)
      ·
        refine ⟨6824431578048039506575405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9099242104064052675433873 6824431578048039506575405)
        ·
          refine ⟨2559161841768014814965777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6824431578048039506575405 2559161841768014814965777)
          ·
            refine ⟨1919371381326011111224333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2559161841768014814965777 1919371381326011111224333)
            ·
              refine ⟨719764267997254166709125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1919371381326011111224333 719764267997254166709125)
              ·
                refine ⟨134955800249485156257961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 719764267997254166709125 134955800249485156257961)
                ·
                  refine ⟨101216850187113867193471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134955800249485156257961 101216850187113867193471)
                  ·
                    rfl

theorem cell20_221759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 2].length) (baseStart_221759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221759 prefixEnd_221759 := by exact prefixLift 221759
  have htrace : WordTrace (prefixWord ++ tailWord_221759) baseStart_221759 baseEnd_221759 := by
    simpa [prefixWord, tailWord_221759, baseEnd_221759] using wordTrace_append hprefix tailTrace_221759
  have hstable : (prefixWord ++ tailWord_221759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221759).length < 2 ^ (prefixWord ++ tailWord_221759).sum := by decide
  have hdescent : baseEnd_221759 < baseStart_221759 := by decide
  rcases family_descends (prefixWord ++ tailWord_221759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221763 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 8]
def baseStart_221763 : Nat := 118140960795 + 221763 * 2 ^ 59
def prefixEnd_221763 : Nat := 4983230072969 + 3 ^ 40 * 221763 * 2
def baseEnd_221763 : Nat := 101218675896107631060121

theorem tailTrace_221763 : CollatzResearch.WordTrace tailWord_221763 prefixEnd_221763 101218675896107631060121 := by
  unfold tailWord_221763
  simp only [CollatzResearch.WordTrace]
  refine ⟨8088361095597999950197943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5392240730398666633465295 8088361095597999950197943)
  ·
    refine ⟨12132541643396999925296915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8088361095597999950197943 12132541643396999925296915)
    ·
      refine ⟨18198812465095499887945373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12132541643396999925296915 18198812465095499887945373)
      ·
        refine ⟨6824554674410812457979515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18198812465095499887945373 6824554674410812457979515)
        ·
          refine ⟨10236832011616218686969273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6824554674410812457979515 10236832011616218686969273)
          ·
            refine ⟨7677624008712164015226955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10236832011616218686969273 7677624008712164015226955)
            ·
              refine ⟨11516436013068246022840433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7677624008712164015226955 11516436013068246022840433)
              ·
                refine ⟨8637327009801184517130325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11516436013068246022840433 8637327009801184517130325)
                ·
                  refine ⟨101218675896107631060121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8637327009801184517130325 101218675896107631060121)
                  ·
                    rfl

theorem cell20_221763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_221763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221763 prefixEnd_221763 := by exact prefixLift 221763
  have htrace : WordTrace (prefixWord ++ tailWord_221763) baseStart_221763 baseEnd_221763 := by
    simpa [prefixWord, tailWord_221763, baseEnd_221763] using wordTrace_append hprefix tailTrace_221763
  have hstable : (prefixWord ++ tailWord_221763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221763).length < 2 ^ (prefixWord ++ tailWord_221763).sum := by decide
  have hdescent : baseEnd_221763 < baseStart_221763 := by decide
  rcases family_descends (prefixWord ++ tailWord_221763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221780 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 6]
def baseStart_221780 : Nat := 118140960795 + 221780 * 2 ^ 59
def prefixEnd_221780 : Nat := 4983230072969 + 3 ^ 40 * 221780 * 2
def baseEnd_221780 : Nat := 101226435159331127493385

theorem tailTrace_221780 : CollatzResearch.WordTrace tailWord_221780 prefixEnd_221780 101226435159331127493385 := by
  unfold tailWord_221780
  simp only [CollatzResearch.WordTrace]
  refine ⟨4044490568268205926783397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5392654091024274569044529 4044490568268205926783397)
  ·
    refine ⟨758341981550288611271887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4044490568268205926783397 758341981550288611271887)
    ·
      refine ⟨1137512972325432916907831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 758341981550288611271887 1137512972325432916907831)
      ·
        refine ⟨1706269458488149375361747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1137512972325432916907831 1706269458488149375361747)
        ·
          refine ⟨2559404187732224063042621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1706269458488149375361747 2559404187732224063042621)
          ·
            refine ⟨959776570399584023640983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2559404187732224063042621 959776570399584023640983)
            ·
              refine ⟨1439664855599376035461475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 959776570399584023640983 1439664855599376035461475)
              ·
                refine ⟨2159497283399064053192213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1439664855599376035461475 2159497283399064053192213)
                ·
                  refine ⟨101226435159331127493385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2159497283399064053192213 101226435159331127493385)
                  ·
                    rfl

theorem cell20_221780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_221780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221780 prefixEnd_221780 := by exact prefixLift 221780
  have htrace : WordTrace (prefixWord ++ tailWord_221780) baseStart_221780 baseEnd_221780 := by
    simpa [prefixWord, tailWord_221780, baseEnd_221780] using wordTrace_append hprefix tailTrace_221780
  have hstable : (prefixWord ++ tailWord_221780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221780).length < 2 ^ (prefixWord ++ tailWord_221780).sum := by decide
  have hdescent : baseEnd_221780 < baseStart_221780 := by decide
  rcases family_descends (prefixWord ++ tailWord_221780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221801 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 8]
def baseStart_221801 : Nat := 118140960795 + 221801 * 2 ^ 59
def prefixEnd_221801 : Nat := 4983230072969 + 3 ^ 40 * 221801 * 2
def baseEnd_221801 : Nat := 101236020131548387793299

theorem tailTrace_221801 : CollatzResearch.WordTrace tailWord_221801 prefixEnd_221801 101236020131548387793299 := by
  unfold tailWord_221801
  simp only [CollatzResearch.WordTrace]
  refine ⟨8089747069460332440081257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5393164712973554960054171 8089747069460332440081257)
  ·
    refine ⟨6067310302095249330060943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8089747069460332440081257 6067310302095249330060943)
    ·
      refine ⟨9100965453142873995091415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6067310302095249330060943 9100965453142873995091415)
      ·
        refine ⟨13651448179714310992637123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9100965453142873995091415 13651448179714310992637123)
        ·
          refine ⟨20477172269571466488955685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13651448179714310992637123 20477172269571466488955685)
          ·
            refine ⟨3839469800544649966679191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20477172269571466488955685 3839469800544649966679191)
            ·
              refine ⟨5759204700816974950018787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3839469800544649966679191 5759204700816974950018787)
              ·
                refine ⟨8638807051225462425028181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5759204700816974950018787 8638807051225462425028181)
                ·
                  refine ⟨101236020131548387793299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8638807051225462425028181 101236020131548387793299)
                  ·
                    rfl

theorem cell20_221801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_221801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221801 prefixEnd_221801 := by exact prefixLift 221801
  have htrace : WordTrace (prefixWord ++ tailWord_221801) baseStart_221801 baseEnd_221801 := by
    simpa [prefixWord, tailWord_221801, baseEnd_221801] using wordTrace_append hprefix tailTrace_221801
  have hstable : (prefixWord ++ tailWord_221801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221801).length < 2 ^ (prefixWord ++ tailWord_221801).sum := by decide
  have hdescent : baseEnd_221801 < baseStart_221801 := by decide
  rcases family_descends (prefixWord ++ tailWord_221801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221814 : List Nat := [5, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_221814 : Nat := 118140960795 + 221814 * 2 ^ 59
def prefixEnd_221814 : Nat := 4983230072969 + 3 ^ 40 * 221814 * 2
def baseEnd_221814 : Nat := 101241953685778120359913

theorem tailTrace_221814 : CollatzResearch.WordTrace tailWord_221814 prefixEnd_221814 101241953685778120359913 := by
  unfold tailWord_221814
  simp only [CollatzResearch.WordTrace]
  refine ⟨505638826150827228769031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5393480812275490440202997 505638826150827228769031)
  ·
    refine ⟨758458239226240843153547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 505638826150827228769031 758458239226240843153547)
    ·
      refine ⟨1137687358839361264730321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 758458239226240843153547 1137687358839361264730321)
      ·
        refine ⟨853265519129520948547741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1137687358839361264730321 853265519129520948547741)
        ·
          refine ⟨319974569673570355705403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 853265519129520948547741 319974569673570355705403)
          ·
            refine ⟨479961854510355533558105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319974569673570355705403 479961854510355533558105)
            ·
              refine ⟨359971390882766650168579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479961854510355533558105 359971390882766650168579)
              ·
                refine ⟨539957086324149975252869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359971390882766650168579 539957086324149975252869)
                ·
                  refine ⟨101241953685778120359913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 539957086324149975252869 101241953685778120359913)
                  ·
                    rfl

theorem cell20_221814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_221814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221814 prefixEnd_221814 := by exact prefixLift 221814
  have htrace : WordTrace (prefixWord ++ tailWord_221814) baseStart_221814 baseEnd_221814 := by
    simpa [prefixWord, tailWord_221814, baseEnd_221814] using wordTrace_append hprefix tailTrace_221814
  have hstable : (prefixWord ++ tailWord_221814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221814).length < 2 ^ (prefixWord ++ tailWord_221814).sum := by decide
  have hdescent : baseEnd_221814 < baseStart_221814 := by decide
  rcases family_descends (prefixWord ++ tailWord_221814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221825 : List Nat := [1, 2, 4, 2, 1, 1, 2, 7]
def baseStart_221825 : Nat := 118140960795 + 221825 * 2 ^ 59
def prefixEnd_221825 : Nat := 4983230072969 + 3 ^ 40 * 221825 * 2
def baseEnd_221825 : Nat := 33748991461836990331067

theorem tailTrace_221825 : CollatzResearch.WordTrace tailWord_221825 prefixEnd_221825 33748991461836990331067 := by
  unfold tailWord_221825
  simp only [CollatzResearch.WordTrace]
  refine ⟨8090622421373384538954929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5393748280915589692636619 8090622421373384538954929)
  ·
    refine ⟨6067966816030038404216197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8090622421373384538954929 6067966816030038404216197)
    ·
      refine ⟨1137743778005632200790537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6067966816030038404216197 1137743778005632200790537)
      ·
        refine ⟨853307833504224150592903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1137743778005632200790537 853307833504224150592903)
        ·
          refine ⟨1279961750256336225889355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853307833504224150592903 1279961750256336225889355)
          ·
            refine ⟨1919942625384504338834033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279961750256336225889355 1919942625384504338834033)
            ·
              refine ⟨1439956969038378254125525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1919942625384504338834033 1439956969038378254125525)
              ·
                refine ⟨33748991461836990331067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1439956969038378254125525 33748991461836990331067)
                ·
                  rfl

theorem cell20_221825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 7].length) (baseStart_221825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221825 prefixEnd_221825 := by exact prefixLift 221825
  have htrace : WordTrace (prefixWord ++ tailWord_221825) baseStart_221825 baseEnd_221825 := by
    simpa [prefixWord, tailWord_221825, baseEnd_221825] using wordTrace_append hprefix tailTrace_221825
  have hstable : (prefixWord ++ tailWord_221825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221825).length < 2 ^ (prefixWord ++ tailWord_221825).sum := by decide
  have hdescent : baseEnd_221825 < baseStart_221825 := by decide
  rcases family_descends (prefixWord ++ tailWord_221825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221842 : List Nat := [3, 2, 3, 1, 2, 2, 1, 6]
def baseStart_221842 : Nat := 118140960795 + 221842 * 2 ^ 59
def prefixEnd_221842 : Nat := 4983230072969 + 3 ^ 40 * 221842 * 2
def baseEnd_221842 : Nat := 33751577882911489142155

theorem tailTrace_221842 : CollatzResearch.WordTrace tailWord_221842 prefixEnd_221842 33751577882911489142155 := by
  unfold tailWord_221842
  simp only [CollatzResearch.WordTrace]
  refine ⟨2022810615577949110580945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5394161641541197628215853 2022810615577949110580945)
  ·
    refine ⟨1517107961683461832935709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2022810615577949110580945 1517107961683461832935709)
    ·
      refine ⟨568915485631298187350891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1517107961683461832935709 568915485631298187350891)
      ·
        refine ⟨853373228446947281026337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568915485631298187350891 853373228446947281026337)
        ·
          refine ⟨640029921335210460769753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 853373228446947281026337 640029921335210460769753)
          ·
            refine ⟨480022441001407845577315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640029921335210460769753 480022441001407845577315)
            ·
              refine ⟨720033661502111768365973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480022441001407845577315 720033661502111768365973)
              ·
                refine ⟨33751577882911489142155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 720033661502111768365973 33751577882911489142155)
                ·
                  rfl

theorem cell20_221842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_221842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221842 prefixEnd_221842 := by exact prefixLift 221842
  have htrace : WordTrace (prefixWord ++ tailWord_221842) baseStart_221842 baseEnd_221842 := by
    simpa [prefixWord, tailWord_221842, baseEnd_221842] using wordTrace_append hprefix tailTrace_221842
  have hstable : (prefixWord ++ tailWord_221842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221842).length < 2 ^ (prefixWord ++ tailWord_221842).sum := by decide
  have hdescent : baseEnd_221842 < baseStart_221842 := by decide
  rcases family_descends (prefixWord ++ tailWord_221842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221852 : List Nat := [2, 2, 3, 2, 2, 1, 3, 3, 2]
def baseStart_221852 : Nat := 118140960795 + 221852 * 2 ^ 59
def prefixEnd_221852 : Nat := 4983230072969 + 3 ^ 40 * 221852 * 2
def baseEnd_221852 : Nat := 101259297921218877093091

theorem tailTrace_221852 : CollatzResearch.WordTrace tailWord_221852 prefixEnd_221852 101259297921218877093091 := by
  unfold tailWord_221852
  simp only [CollatzResearch.WordTrace]
  refine ⟨4045803596137784075093905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5394404794850378766791873 4045803596137784075093905)
  ·
    refine ⟨3034352697103338056320429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4045803596137784075093905 3034352697103338056320429)
    ·
      refine ⟨1137882261413751771120161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3034352697103338056320429 1137882261413751771120161)
      ·
        refine ⟨853411696060313828340121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1137882261413751771120161 853411696060313828340121)
        ·
          refine ⟨640058772045235371255091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 853411696060313828340121 640058772045235371255091)
          ·
            refine ⟨960088158067853056882637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640058772045235371255091 960088158067853056882637)
            ·
              refine ⟨360033059275444896330989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 960088158067853056882637 360033059275444896330989)
              ·
                refine ⟨135012397228291836124121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360033059275444896330989 135012397228291836124121)
                ·
                  refine ⟨101259297921218877093091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135012397228291836124121 101259297921218877093091)
                  ·
                    rfl

theorem cell20_221852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_221852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221852 prefixEnd_221852 := by exact prefixLift 221852
  have htrace : WordTrace (prefixWord ++ tailWord_221852) baseStart_221852 baseEnd_221852 := by
    simpa [prefixWord, tailWord_221852, baseEnd_221852] using wordTrace_append hprefix tailTrace_221852
  have hstable : (prefixWord ++ tailWord_221852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221852).length < 2 ^ (prefixWord ++ tailWord_221852).sum := by decide
  have hdescent : baseEnd_221852 < baseStart_221852 := by decide
  rcases family_descends (prefixWord ++ tailWord_221852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221869 : List Nat := [1, 5, 2, 1, 1, 3, 3, 2, 2]
def baseStart_221869 : Nat := 118140960795 + 221869 * 2 ^ 59
def prefixEnd_221869 : Nat := 4983230072969 + 3 ^ 40 * 221869 * 2
def baseEnd_221869 : Nat := 101267057184442373526355

theorem tailTrace_221869 : CollatzResearch.WordTrace tailWord_221869 prefixEnd_221869 101267057184442373526355 := by
  unfold tailWord_221869
  simp only [CollatzResearch.WordTrace]
  refine ⟨8092227233213980053556661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5394818155475986702371107 8092227233213980053556661)
  ·
    refine ⟨758646303113810630020937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8092227233213980053556661 758646303113810630020937)
    ·
      refine ⟨568984727335357972515703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 758646303113810630020937 568984727335357972515703)
      ·
        refine ⟨853477091003036958773555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568984727335357972515703 853477091003036958773555)
        ·
          refine ⟨1280215636504555438160333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853477091003036958773555 1280215636504555438160333)
          ·
            refine ⟨480080863689208289310125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1280215636504555438160333 480080863689208289310125)
            ·
              refine ⟨180030323883453108491297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 480080863689208289310125 180030323883453108491297)
              ·
                refine ⟨135022742912589831368473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180030323883453108491297 135022742912589831368473)
                ·
                  refine ⟨101267057184442373526355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135022742912589831368473 101267057184442373526355)
                  ·
                    rfl

theorem cell20_221869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_221869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221869 prefixEnd_221869 := by exact prefixLift 221869
  have htrace : WordTrace (prefixWord ++ tailWord_221869) baseStart_221869 baseEnd_221869 := by
    simpa [prefixWord, tailWord_221869, baseEnd_221869] using wordTrace_append hprefix tailTrace_221869
  have hstable : (prefixWord ++ tailWord_221869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221869).length < 2 ^ (prefixWord ++ tailWord_221869).sum := by decide
  have hdescent : baseEnd_221869 < baseStart_221869 := by decide
  rcases family_descends (prefixWord ++ tailWord_221869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221887 : List Nat := [1, 1, 2, 2, 2, 5, 1, 3, 3]
def baseStart_221887 : Nat := 118140960795 + 221887 * 2 ^ 59
def prefixEnd_221887 : Nat := 4983230072969 + 3 ^ 40 * 221887 * 2
def baseEnd_221887 : Nat := 101275272874914310926281

theorem tailTrace_221887 : CollatzResearch.WordTrace tailWord_221887 prefixEnd_221887 101275272874914310926281 := by
  unfold tailWord_221887
  simp only [CollatzResearch.WordTrace]
  refine ⟨8092883747148769127711915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5395255831432512751807943 8092883747148769127711915)
  ·
    refine ⟨12139325620723153691567873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8092883747148769127711915 12139325620723153691567873)
    ·
      refine ⟨9104494215542365268675905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12139325620723153691567873 9104494215542365268675905)
      ·
        refine ⟨6828370661656773951506929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9104494215542365268675905 6828370661656773951506929)
        ·
          refine ⟨5121277996242580463630197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6828370661656773951506929 5121277996242580463630197)
          ·
            refine ⟨480119812147741918465331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5121277996242580463630197 480119812147741918465331)
            ·
              refine ⟨720179718221612877697997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480119812147741918465331 720179718221612877697997)
              ·
                refine ⟨270067394333104829136749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 720179718221612877697997 270067394333104829136749)
                ·
                  refine ⟨101275272874914310926281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270067394333104829136749 101275272874914310926281)
                  ·
                    rfl

theorem cell20_221887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 3].length) (baseStart_221887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221887 prefixEnd_221887 := by exact prefixLift 221887
  have htrace : WordTrace (prefixWord ++ tailWord_221887) baseStart_221887 baseEnd_221887 := by
    simpa [prefixWord, tailWord_221887, baseEnd_221887] using wordTrace_append hprefix tailTrace_221887
  have hstable : (prefixWord ++ tailWord_221887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221887).length < 2 ^ (prefixWord ++ tailWord_221887).sum := by decide
  have hdescent : baseEnd_221887 < baseStart_221887 := by decide
  rcases family_descends (prefixWord ++ tailWord_221887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221925 : List Nat := [1, 3, 1, 4, 1, 2, 1, 4, 3]
def baseStart_221925 : Nat := 118140960795 + 221925 * 2 ^ 59
def prefixEnd_221925 : Nat := 4983230072969 + 3 ^ 40 * 221925 * 2
def baseEnd_221925 : Nat := 101292617110355067659459

theorem tailTrace_221925 : CollatzResearch.WordTrace tailWord_221925 prefixEnd_221925 101292617110355067659459 := by
  unfold tailWord_221925
  simp only [CollatzResearch.WordTrace]
  refine ⟨8094269721011101617595229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5396179814007401078396819 8094269721011101617595229)
  ·
    refine ⟨3035351145379163106598211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8094269721011101617595229 3035351145379163106598211)
    ·
      refine ⟨4553026718068744659897317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3035351145379163106598211 4553026718068744659897317)
      ·
        refine ⟨853692509637889623730747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4553026718068744659897317 853692509637889623730747)
        ·
          refine ⟨1280538764456834435596121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853692509637889623730747 1280538764456834435596121)
          ·
            refine ⟨960404073342625826697091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1280538764456834435596121 960404073342625826697091)
            ·
              refine ⟨1440606110013938740045637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 960404073342625826697091 1440606110013938740045637)
              ·
                refine ⟨270113645627613513758557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1440606110013938740045637 270113645627613513758557)
                ·
                  refine ⟨101292617110355067659459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270113645627613513758557 101292617110355067659459)
                  ·
                    rfl

theorem cell20_221925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_221925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221925 prefixEnd_221925 := by exact prefixLift 221925
  have htrace : WordTrace (prefixWord ++ tailWord_221925) baseStart_221925 baseEnd_221925 := by
    simpa [prefixWord, tailWord_221925, baseEnd_221925] using wordTrace_append hprefix tailTrace_221925
  have hstable : (prefixWord ++ tailWord_221925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221925).length < 2 ^ (prefixWord ++ tailWord_221925).sum := by decide
  have hdescent : baseEnd_221925 < baseStart_221925 := by decide
  rcases family_descends (prefixWord ++ tailWord_221925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221928 : List Nat := [2, 1, 4, 1, 4, 1, 1, 4, 2]
def baseStart_221928 : Nat := 118140960795 + 221928 * 2 ^ 59
def prefixEnd_221928 : Nat := 4983230072969 + 3 ^ 40 * 221928 * 2
def baseEnd_221928 : Nat := 101293986392100390559447

theorem tailTrace_221928 : CollatzResearch.WordTrace tailWord_221928 prefixEnd_221928 101293986392100390559447 := by
  unfold tailWord_221928
  simp only [CollatzResearch.WordTrace]
  refine ⟨4047189570000116564977219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5396252760000155419969625 4047189570000116564977219)
  ·
    refine ⟨6070784355000174847465829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4047189570000116564977219 6070784355000174847465829)
    ·
      refine ⟨1138272066562532783899843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6070784355000174847465829 1138272066562532783899843)
      ·
        refine ⟨1707408099843799175849765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1138272066562532783899843 1707408099843799175849765)
        ·
          refine ⟨320139018720712345471831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1707408099843799175849765 320139018720712345471831)
          ·
            refine ⟨480208528081068518207747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320139018720712345471831 480208528081068518207747)
            ·
              refine ⟨720312792121602777311621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480208528081068518207747 720312792121602777311621)
              ·
                refine ⟨135058648522800520745929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 720312792121602777311621 135058648522800520745929)
                ·
                  refine ⟨101293986392100390559447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135058648522800520745929 101293986392100390559447)
                  ·
                    rfl

theorem cell20_221928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 2].length) (baseStart_221928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221928 prefixEnd_221928 := by exact prefixLift 221928
  have htrace : WordTrace (prefixWord ++ tailWord_221928) baseStart_221928 baseEnd_221928 := by
    simpa [prefixWord, tailWord_221928, baseEnd_221928] using wordTrace_append hprefix tailTrace_221928
  have hstable : (prefixWord ++ tailWord_221928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221928).length < 2 ^ (prefixWord ++ tailWord_221928).sum := by decide
  have hdescent : baseEnd_221928 < baseStart_221928 := by decide
  rcases family_descends (prefixWord ++ tailWord_221928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221956 : List Nat := [2, 3, 2, 2, 1, 1, 5, 4]
def baseStart_221956 : Nat := 118140960795 + 221956 * 2 ^ 59
def prefixEnd_221956 : Nat := 4983230072969 + 3 ^ 40 * 221956 * 2
def baseEnd_221956 : Nat := 33768922118352245875333

theorem tailTrace_221956 : CollatzResearch.WordTrace tailWord_221956 prefixEnd_221956 33768922118352245875333 := by
  unfold tailWord_221956
  simp only [CollatzResearch.WordTrace]
  refine ⟨4047700191949396955986861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5396933589265862607982481 4047700191949396955986861)
  ·
    refine ⟨1517887571981023858495073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4047700191949396955986861 1517887571981023858495073)
    ·
      refine ⟨1138415678985767893871305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1517887571981023858495073 1138415678985767893871305)
      ·
        refine ⟨853811759239325920403479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1138415678985767893871305 853811759239325920403479)
        ·
          refine ⟨1280717638858988880605219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853811759239325920403479 1280717638858988880605219)
          ·
            refine ⟨1921076458288483320907829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1280717638858988880605219 1921076458288483320907829)
            ·
              refine ⟨180100917964545311335109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1921076458288483320907829 180100917964545311335109)
              ·
                refine ⟨33768922118352245875333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180100917964545311335109 33768922118352245875333)
                ·
                  rfl

theorem cell20_221956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 4].length) (baseStart_221956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221956 prefixEnd_221956 := by exact prefixLift 221956
  have htrace : WordTrace (prefixWord ++ tailWord_221956) baseStart_221956 baseEnd_221956 := by
    simpa [prefixWord, tailWord_221956, baseEnd_221956] using wordTrace_append hprefix tailTrace_221956
  have hstable : (prefixWord ++ tailWord_221956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221956).length < 2 ^ (prefixWord ++ tailWord_221956).sum := by decide
  have hdescent : baseEnd_221956 < baseStart_221956 := by decide
  rcases family_descends (prefixWord ++ tailWord_221956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221980 : List Nat := [2, 2, 3, 1, 1, 5, 1, 2, 3]
def baseStart_221980 : Nat := 118140960795 + 221980 * 2 ^ 59
def prefixEnd_221980 : Nat := 4983230072969 + 3 ^ 40 * 221980 * 2
def baseEnd_221980 : Nat := 101317720609019320825901

theorem tailTrace_221980 : CollatzResearch.WordTrace tailWord_221980 prefixEnd_221980 101317720609019320825901 := by
  unfold tailWord_221980
  simp only [CollatzResearch.WordTrace]
  refine ⟨4048137867905923005423697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5397517157207897340564929 4048137867905923005423697)
  ·
    refine ⟨3036103400929442254067773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4048137867905923005423697 3036103400929442254067773)
    ·
      refine ⟨1138538775348540845275415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3036103400929442254067773 1138538775348540845275415)
      ·
        refine ⟨1707808163022811267913123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1138538775348540845275415 1707808163022811267913123)
        ·
          refine ⟨2561712244534216901869685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1707808163022811267913123 2561712244534216901869685)
          ·
            refine ⟨240160522925082834550283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2561712244534216901869685 240160522925082834550283)
            ·
              refine ⟨360240784387624251825425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240160522925082834550283 360240784387624251825425)
              ·
                refine ⟨270180588290718188869069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360240784387624251825425 270180588290718188869069)
                ·
                  refine ⟨101317720609019320825901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270180588290718188869069 101317720609019320825901)
                  ·
                    rfl

theorem cell20_221980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_221980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_221980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_221980 prefixEnd_221980 := by exact prefixLift 221980
  have htrace : WordTrace (prefixWord ++ tailWord_221980) baseStart_221980 baseEnd_221980 := by
    simpa [prefixWord, tailWord_221980, baseEnd_221980] using wordTrace_append hprefix tailTrace_221980
  have hstable : (prefixWord ++ tailWord_221980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221980).length < 2 ^ (prefixWord ++ tailWord_221980).sum := by decide
  have hdescent : baseEnd_221980 < baseStart_221980 := by decide
  rcases family_descends (prefixWord ++ tailWord_221980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222015 : List Nat := [1, 1, 2, 2, 5, 2, 1, 6]
def baseStart_222015 : Nat := 118140960795 + 222015 * 2 ^ 59
def prefixEnd_222015 : Nat := 4983230072969 + 3 ^ 40 * 222015 * 2
def baseEnd_222015 : Nat := 33777898520904918219697

theorem tailTrace_222015 : CollatzResearch.WordTrace tailWord_222015 prefixEnd_222015 33777898520904918219697 := by
  unfold tailWord_222015
  simp only [CollatzResearch.WordTrace]
  refine ⟨8097552290685046988371499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5398368193790031325580999 8097552290685046988371499)
  ·
    refine ⟨12146328436027570482557249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8097552290685046988371499 12146328436027570482557249)
    ·
      refine ⟨9109746327020677861917937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12146328436027570482557249 9109746327020677861917937)
      ·
        refine ⟨6832309745265508396438453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9109746327020677861917937 6832309745265508396438453)
        ·
          refine ⟨640529038618641412166105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6832309745265508396438453 640529038618641412166105)
          ·
            refine ⟨480396778963981059124579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640529038618641412166105 480396778963981059124579)
            ·
              refine ⟨720595168445971588686869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480396778963981059124579 720595168445971588686869)
              ·
                refine ⟨33777898520904918219697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 720595168445971588686869 33777898520904918219697)
                ·
                  rfl

theorem cell20_222015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 6].length) (baseStart_222015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222015 prefixEnd_222015 := by exact prefixLift 222015
  have htrace : WordTrace (prefixWord ++ tailWord_222015) baseStart_222015 baseEnd_222015 := by
    simpa [prefixWord, tailWord_222015, baseEnd_222015] using wordTrace_append hprefix tailTrace_222015
  have hstable : (prefixWord ++ tailWord_222015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222015).length < 2 ^ (prefixWord ++ tailWord_222015).sum := by decide
  have hdescent : baseEnd_222015 < baseStart_222015 := by decide
  rcases family_descends (prefixWord ++ tailWord_222015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222025 : List Nat := [1, 2, 1, 1, 2, 5, 3, 3, 2]
def baseStart_222025 : Nat := 118140960795 + 222025 * 2 ^ 59
def prefixEnd_222025 : Nat := 4983230072969 + 3 ^ 40 * 222025 * 2
def baseEnd_222025 : Nat := 101338259835199164325717

theorem tailTrace_222025 : CollatzResearch.WordTrace tailWord_222025 prefixEnd_222025 101338259835199164325717 := by
  unfold tailWord_222025
  simp only [CollatzResearch.WordTrace]
  refine ⟨8097917020648818696235529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5398611347099212464157019 8097917020648818696235529)
  ·
    refine ⟨6073437765486614022176647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8097917020648818696235529 6073437765486614022176647)
    ·
      refine ⟨9110156648229921033264971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6073437765486614022176647 9110156648229921033264971)
      ·
        refine ⟨13665234972344881549897457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9110156648229921033264971 13665234972344881549897457)
        ·
          refine ⟨10248926229258661162423093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13665234972344881549897457 10248926229258661162423093)
          ·
            refine ⟨960836833992999483977165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10248926229258661162423093 960836833992999483977165)
            ·
              refine ⟨360313812747374806491437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 960836833992999483977165 360313812747374806491437)
              ·
                refine ⟨135117679780265552434289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360313812747374806491437 135117679780265552434289)
                ·
                  refine ⟨101338259835199164325717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135117679780265552434289 101338259835199164325717)
                  ·
                    rfl

theorem cell20_222025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 2].length) (baseStart_222025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222025 prefixEnd_222025 := by exact prefixLift 222025
  have htrace : WordTrace (prefixWord ++ tailWord_222025) baseStart_222025 baseEnd_222025 := by
    simpa [prefixWord, tailWord_222025, baseEnd_222025] using wordTrace_append hprefix tailTrace_222025
  have hstable : (prefixWord ++ tailWord_222025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222025).length < 2 ^ (prefixWord ++ tailWord_222025).sum := by decide
  have hdescent : baseEnd_222025 < baseStart_222025 := by decide
  rcases family_descends (prefixWord ++ tailWord_222025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222042 : List Nat := [3, 1, 1, 2, 1, 5, 3, 2, 2]
def baseStart_222042 : Nat := 118140960795 + 222042 * 2 ^ 59
def prefixEnd_222042 : Nat := 4983230072969 + 3 ^ 40 * 222042 * 2
def baseEnd_222042 : Nat := 101346019098422660758981

theorem tailTrace_222042 : CollatzResearch.WordTrace tailWord_222042 prefixEnd_222042 101346019098422660758981 := by
  unfold tailWord_222042
  simp only [CollatzResearch.WordTrace]
  refine ⟨2024634265396807649901095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5399024707724820399736253 2024634265396807649901095)
  ·
    refine ⟨3036951398095211474851643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2024634265396807649901095 3036951398095211474851643)
    ·
      refine ⟨4555427097142817212277465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3036951398095211474851643 4555427097142817212277465)
      ·
        refine ⟨3416570322857112909208099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4555427097142817212277465 3416570322857112909208099)
        ·
          refine ⟨5124855484285669363812149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3416570322857112909208099 5124855484285669363812149)
          ·
            refine ⟨480455201651781502857389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5124855484285669363812149 480455201651781502857389)
            ·
              refine ⟨180170700619418063571521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 480455201651781502857389 180170700619418063571521)
              ·
                refine ⟨135128025464563547678641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180170700619418063571521 135128025464563547678641)
                ·
                  refine ⟨101346019098422660758981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135128025464563547678641 101346019098422660758981)
                  ·
                    rfl

theorem cell20_222042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_222042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222042 prefixEnd_222042 := by exact prefixLift 222042
  have htrace : WordTrace (prefixWord ++ tailWord_222042) baseStart_222042 baseEnd_222042 := by
    simpa [prefixWord, tailWord_222042, baseEnd_222042] using wordTrace_append hprefix tailTrace_222042
  have hstable : (prefixWord ++ tailWord_222042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222042).length < 2 ^ (prefixWord ++ tailWord_222042).sum := by decide
  have hdescent : baseEnd_222042 < baseStart_222042 := by decide
  rcases family_descends (prefixWord ++ tailWord_222042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222056 : List Nat := [2, 1, 4, 2, 1, 2, 4, 1, 3]
def baseStart_222056 : Nat := 118140960795 + 222056 * 2 ^ 59
def prefixEnd_222056 : Nat := 4983230072969 + 3 ^ 40 * 222056 * 2
def baseEnd_222056 : Nat := 101352409079900834292257

theorem tailTrace_222056 : CollatzResearch.WordTrace tailWord_222056 prefixEnd_222056 101352409079900834292257 := by
  unfold tailWord_222056
  simp only [CollatzResearch.WordTrace]
  refine ⟨4049523841768255495307011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5399365122357673993742681 4049523841768255495307011)
  ·
    refine ⟨6074285762652383242960517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4049523841768255495307011 6074285762652383242960517)
    ·
      refine ⟨1138928580497321858055097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6074285762652383242960517 1138928580497321858055097)
      ·
        refine ⟨854196435372991393541323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1138928580497321858055097 854196435372991393541323)
        ·
          refine ⟨1281294653059487090311985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 854196435372991393541323 1281294653059487090311985)
          ·
            refine ⟨960970989794615317733989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1281294653059487090311985 960970989794615317733989)
            ·
              refine ⟨180182060586490372075123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 960970989794615317733989 180182060586490372075123)
              ·
                refine ⟨270273090879735558112685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180182060586490372075123 270273090879735558112685)
                ·
                  refine ⟨101352409079900834292257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270273090879735558112685 101352409079900834292257)
                  ·
                    rfl

theorem cell20_222056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 3].length) (baseStart_222056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222056 prefixEnd_222056 := by exact prefixLift 222056
  have htrace : WordTrace (prefixWord ++ tailWord_222056) baseStart_222056 baseEnd_222056 := by
    simpa [prefixWord, tailWord_222056, baseEnd_222056] using wordTrace_append hprefix tailTrace_222056
  have hstable : (prefixWord ++ tailWord_222056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222056).length < 2 ^ (prefixWord ++ tailWord_222056).sum := by decide
  have hdescent : baseEnd_222056 < baseStart_222056 := by decide
  rcases family_descends (prefixWord ++ tailWord_222056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222067 : List Nat := [1, 1, 1, 2, 2, 1, 4, 4, 4]
def baseStart_222067 : Nat := 118140960795 + 222067 * 2 ^ 59
def prefixEnd_222067 : Nat := 4983230072969 + 3 ^ 40 * 222067 * 2
def baseEnd_222067 : Nat := 101357429779633684925545

theorem tailTrace_222067 : CollatzResearch.WordTrace tailWord_222067 prefixEnd_222067 101357429779633684925545 := by
  unfold tailWord_222067
  simp only [CollatzResearch.WordTrace]
  refine ⟨8099448886496659869264455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5399632590997773246176303 8099448886496659869264455)
  ·
    refine ⟨12149173329744989803896683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8099448886496659869264455 12149173329744989803896683)
    ·
      refine ⟨18223759994617484705845025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12149173329744989803896683 18223759994617484705845025)
      ·
        refine ⟨13667819995963113529383769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18223759994617484705845025 13667819995963113529383769)
        ·
          refine ⟨10250864996972335147037827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13667819995963113529383769 10250864996972335147037827)
          ·
            refine ⟨15376297495458502720556741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10250864996972335147037827 15376297495458502720556741)
            ·
              refine ⟨2883055780398469260104389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15376297495458502720556741 2883055780398469260104389)
              ·
                refine ⟨540572958824712986269573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2883055780398469260104389 540572958824712986269573)
                ·
                  refine ⟨101357429779633684925545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 540572958824712986269573 101357429779633684925545)
                  ·
                    rfl

theorem cell20_222067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 4].length) (baseStart_222067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222067 prefixEnd_222067 := by exact prefixLift 222067
  have htrace : WordTrace (prefixWord ++ tailWord_222067) baseStart_222067 baseEnd_222067 := by
    simpa [prefixWord, tailWord_222067, baseEnd_222067] using wordTrace_append hprefix tailTrace_222067
  have hstable : (prefixWord ++ tailWord_222067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222067).length < 2 ^ (prefixWord ++ tailWord_222067).sum := by decide
  have hdescent : baseEnd_222067 < baseStart_222067 := by decide
  rcases family_descends (prefixWord ++ tailWord_222067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222070 : List Nat := [5, 1, 1, 3, 1, 1, 2, 6]
def baseStart_222070 : Nat := 118140960795 + 222070 * 2 ^ 59
def prefixEnd_222070 : Nat := 4983230072969 + 3 ^ 40 * 222070 * 2
def baseEnd_222070 : Nat := 33786266353793002608511

theorem tailTrace_222070 : CollatzResearch.WordTrace tailWord_222070 prefixEnd_222070 33786266353793002608511 := by
  unfold tailWord_222070
  simp only [CollatzResearch.WordTrace]
  refine ⟨506222394092861961351479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5399705536990527587749109 506222394092861961351479)
  ·
    refine ⟨759333591139292942027219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 506222394092861961351479 759333591139292942027219)
    ·
      refine ⟨1139000386708939413040829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 759333591139292942027219 1139000386708939413040829)
      ·
        refine ⟨427125145015852279890311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1139000386708939413040829 427125145015852279890311)
        ·
          refine ⟨640687717523778419835467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427125145015852279890311 640687717523778419835467)
          ·
            refine ⟨961031576285667629753201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 640687717523778419835467 961031576285667629753201)
            ·
              refine ⟨720773682214250722314901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 961031576285667629753201 720773682214250722314901)
              ·
                refine ⟨33786266353793002608511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 720773682214250722314901 33786266353793002608511)
                ·
                  rfl

theorem cell20_222070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_222070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222070 prefixEnd_222070 := by exact prefixLift 222070
  have htrace : WordTrace (prefixWord ++ tailWord_222070) baseStart_222070 baseEnd_222070 := by
    simpa [prefixWord, tailWord_222070, baseEnd_222070] using wordTrace_append hprefix tailTrace_222070
  have hstable : (prefixWord ++ tailWord_222070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222070).length < 2 ^ (prefixWord ++ tailWord_222070).sum := by decide
  have hdescent : baseEnd_222070 < baseStart_222070 := by decide
  rcases family_descends (prefixWord ++ tailWord_222070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222101 : List Nat := [1, 3, 2, 1, 1, 5, 1, 4, 2]
def baseStart_222101 : Nat := 118140960795 + 222101 * 2 ^ 59
def prefixEnd_222101 : Nat := 4983230072969 + 3 ^ 40 * 222101 * 2
def baseEnd_222101 : Nat := 101372948306080677792073

theorem tailTrace_222101 : CollatzResearch.WordTrace tailWord_222101 prefixEnd_222101 101372948306080677792073 := by
  unfold tailWord_222101
  simp only [CollatzResearch.WordTrace]
  refine ⟨8100688968373483676002157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5400459312248989117334771 8100688968373483676002157)
  ·
    refine ⟨3037758363140056378500809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8100688968373483676002157 3037758363140056378500809)
    ·
      refine ⟨2278318772355042283875607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3037758363140056378500809 2278318772355042283875607)
      ·
        refine ⟨3417478158532563425813411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2278318772355042283875607 3417478158532563425813411)
        ·
          refine ⟨5126217237798845138720117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3417478158532563425813411 5126217237798845138720117)
          ·
            refine ⟨480582866043641731755011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5126217237798845138720117 480582866043641731755011)
            ·
              refine ⟨720874299065462597632517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480582866043641731755011 720874299065462597632517)
              ·
                refine ⟨135163931074774237056097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 720874299065462597632517 135163931074774237056097)
                ·
                  refine ⟨101372948306080677792073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135163931074774237056097 101372948306080677792073)
                  ·
                    rfl

theorem cell20_222101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_222101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222101 prefixEnd_222101 := by exact prefixLift 222101
  have htrace : WordTrace (prefixWord ++ tailWord_222101) baseStart_222101 baseEnd_222101 := by
    simpa [prefixWord, tailWord_222101, baseEnd_222101] using wordTrace_append hprefix tailTrace_222101
  have hstable : (prefixWord ++ tailWord_222101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222101).length < 2 ^ (prefixWord ++ tailWord_222101).sum := by decide
  have hdescent : baseEnd_222101 < baseStart_222101 := by decide
  rcases family_descends (prefixWord ++ tailWord_222101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222105 : List Nat := [1, 2, 1, 2, 1, 3, 1, 5, 4]
def baseStart_222105 : Nat := 118140960795 + 222105 * 2 ^ 59
def prefixEnd_222105 : Nat := 4983230072969 + 3 ^ 40 * 222105 * 2
def baseEnd_222105 : Nat := 101374774015074441658723

theorem tailTrace_222105 : CollatzResearch.WordTrace tailWord_222105 prefixEnd_222105 101374774015074441658723 := by
  unfold tailWord_222105
  simp only [CollatzResearch.WordTrace]
  refine ⟨8100834860358992359147769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5400556573572661572765179 8100834860358992359147769)
  ·
    refine ⟨6075626145269244269360827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8100834860358992359147769 6075626145269244269360827)
    ·
      refine ⟨9113439217903866404041241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6075626145269244269360827 9113439217903866404041241)
      ·
        refine ⟨6835079413427899803030931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9113439217903866404041241 6835079413427899803030931)
        ·
          refine ⟨10252619120141849704546397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6835079413427899803030931 10252619120141849704546397)
          ·
            refine ⟨3844732170053193639204899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10252619120141849704546397 3844732170053193639204899)
            ·
              refine ⟨5767098255079790458807349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3844732170053193639204899 5767098255079790458807349)
              ·
                refine ⟨540665461413730355513189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5767098255079790458807349 540665461413730355513189)
                ·
                  refine ⟨101374774015074441658723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 540665461413730355513189 101374774015074441658723)
                  ·
                    rfl

theorem cell20_222105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_222105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222105 prefixEnd_222105 := by exact prefixLift 222105
  have htrace : WordTrace (prefixWord ++ tailWord_222105) baseStart_222105 baseEnd_222105 := by
    simpa [prefixWord, tailWord_222105, baseEnd_222105] using wordTrace_append hprefix tailTrace_222105
  have hstable : (prefixWord ++ tailWord_222105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222105).length < 2 ^ (prefixWord ++ tailWord_222105).sum := by decide
  have hdescent : baseEnd_222105 < baseStart_222105 := by decide
  rcases family_descends (prefixWord ++ tailWord_222105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222170 : List Nat := [3, 1, 1, 2, 4, 2, 3, 1, 3]
def baseStart_222170 : Nat := 118140960795 + 222170 * 2 ^ 59
def prefixEnd_222170 : Nat := 4983230072969 + 3 ^ 40 * 222170 * 2
def baseEnd_222170 : Nat := 101404441786223104491791

theorem tailTrace_222170 : CollatzResearch.WordTrace tailWord_222170 prefixEnd_222170 101404441786223104491791 := by
  unfold tailWord_222170
  simp only [CollatzResearch.WordTrace]
  refine ⟨2025801401280877115065991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5402137070082338973509309 2025801401280877115065991)
  ·
    refine ⟨3038702101921315672598987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2025801401280877115065991 3038702101921315672598987)
    ·
      refine ⟨4558053152881973508898481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3038702101921315672598987 4558053152881973508898481)
      ·
        refine ⟨3418539864661480131673861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4558053152881973508898481 3418539864661480131673861)
        ·
          refine ⟨640976224624027524688849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3418539864661480131673861 640976224624027524688849)
          ·
            refine ⟨480732168468020643516637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 640976224624027524688849 480732168468020643516637)
            ·
              refine ⟨180274563175507741318739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 480732168468020643516637 180274563175507741318739)
              ·
                refine ⟨270411844763261611978109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180274563175507741318739 270411844763261611978109)
                ·
                  refine ⟨101404441786223104491791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270411844763261611978109 101404441786223104491791)
                  ·
                    rfl

theorem cell20_222170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_222170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222170 prefixEnd_222170 := by exact prefixLift 222170
  have htrace : WordTrace (prefixWord ++ tailWord_222170) baseStart_222170 baseEnd_222170 := by
    simpa [prefixWord, tailWord_222170, baseEnd_222170] using wordTrace_append hprefix tailTrace_222170
  have hstable : (prefixWord ++ tailWord_222170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222170).length < 2 ^ (prefixWord ++ tailWord_222170).sum := by decide
  have hdescent : baseEnd_222170 < baseStart_222170 := by decide
  rcases family_descends (prefixWord ++ tailWord_222170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222229 : List Nat := [1, 3, 2, 1, 4, 2, 1, 3, 3]
def baseStart_222229 : Nat := 118140960795 + 222229 * 2 ^ 59
def prefixEnd_222229 : Nat := 4983230072969 + 3 ^ 40 * 222229 * 2
def baseEnd_222229 : Nat := 101431370993881121524883

theorem tailTrace_222229 : CollatzResearch.WordTrace tailWord_222229 prefixEnd_222229 101431370993881121524883 := by
  unfold tailWord_222229
  simp only [CollatzResearch.WordTrace]
  refine ⟨8105357511909761536661741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5403571674606507691107827 8105357511909761536661741)
  ·
    refine ⟨3039509066966160576248153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8105357511909761536661741 3039509066966160576248153)
    ·
      refine ⟨2279631800224620432186115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3039509066966160576248153 2279631800224620432186115)
      ·
        refine ⟨3419447700336930648279173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2279631800224620432186115 3419447700336930648279173)
        ·
          refine ⟨641146443813174496552345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3419447700336930648279173 641146443813174496552345)
          ·
            refine ⟨480859832859880872414259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 641146443813174496552345 480859832859880872414259)
            ·
              refine ⟨721289749289821308621389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480859832859880872414259 721289749289821308621389)
              ·
                refine ⟨270483655983682990733021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 721289749289821308621389 270483655983682990733021)
                ·
                  refine ⟨101431370993881121524883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270483655983682990733021 101431370993881121524883)
                  ·
                    rfl

theorem cell20_222229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_222229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222229 prefixEnd_222229 := by exact prefixLift 222229
  have htrace : WordTrace (prefixWord ++ tailWord_222229) baseStart_222229 baseEnd_222229 := by
    simpa [prefixWord, tailWord_222229, baseEnd_222229] using wordTrace_append hprefix tailTrace_222229
  have hstable : (prefixWord ++ tailWord_222229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222229).length < 2 ^ (prefixWord ++ tailWord_222229).sum := by decide
  have hdescent : baseEnd_222229 < baseStart_222229 := by decide
  rcases family_descends (prefixWord ++ tailWord_222229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222264 : List Nat := [2, 1, 2, 1, 5, 9]
def baseStart_222264 : Nat := 118140960795 + 222264 * 2 ^ 59
def prefixEnd_222264 : Nat := 4983230072969 + 3 ^ 40 * 222264 * 2
def baseEnd_222264 : Nat := 3757309109169502050299

theorem tailTrace_222264 : CollatzResearch.WordTrace tailWord_222264 prefixEnd_222264 3757309109169502050299 := by
  unfold tailWord_222264
  simp only [CollatzResearch.WordTrace]
  refine ⟨4053317033391481257092923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5404422711188641676123897 4053317033391481257092923)
  ·
    refine ⟨6079975550087221885639385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4053317033391481257092923 6079975550087221885639385)
    ·
      refine ⟨4559981662565416414229539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6079975550087221885639385 4559981662565416414229539)
      ·
        refine ⟨6839972493848124621344309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4559981662565416414229539 6839972493848124621344309)
        ·
          refine ⟨641247421298261683251029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6839972493848124621344309 641247421298261683251029)
          ·
            refine ⟨3757309109169502050299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 641247421298261683251029 3757309109169502050299)
            ·
              rfl

theorem cell20_222264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 9].length) (baseStart_222264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222264 prefixEnd_222264 := by exact prefixLift 222264
  have htrace : WordTrace (prefixWord ++ tailWord_222264) baseStart_222264 baseEnd_222264 := by
    simpa [prefixWord, tailWord_222264, baseEnd_222264] using wordTrace_append hprefix tailTrace_222264
  have hstable : (prefixWord ++ tailWord_222264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222264).length < 2 ^ (prefixWord ++ tailWord_222264).sum := by decide
  have hdescent : baseEnd_222264 < baseStart_222264 := by decide
  rcases family_descends (prefixWord ++ tailWord_222264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222270 : List Nat := [4, 2, 1, 3, 1, 2, 1, 4, 2]
def baseStart_222270 : Nat := 118140960795 + 222270 * 2 ^ 59
def prefixEnd_222270 : Nat := 4983230072969 + 3 ^ 40 * 222270 * 2
def baseEnd_222270 : Nat := 101450084511067201158049

theorem tailTrace_222270 : CollatzResearch.WordTrace tailWord_222270 prefixEnd_222270 101450084511067201158049 := by
  unfold tailWord_222270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1013356613095153192363033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5404568603174150359269509 1013356613095153192363033)
  ·
    refine ⟨760017459821364894272275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1013356613095153192363033 760017459821364894272275)
    ·
      refine ⟨1140026189732047341408413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 760017459821364894272275 1140026189732047341408413)
      ·
        refine ⟨427509821149517753028155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1140026189732047341408413 427509821149517753028155)
        ·
          refine ⟨641264731724276629542233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427509821149517753028155 641264731724276629542233)
          ·
            refine ⟨480948548793207472156675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 641264731724276629542233 480948548793207472156675)
            ·
              refine ⟨721422823189811208235013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480948548793207472156675 721422823189811208235013)
              ·
                refine ⟨135266779348089601544065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 721422823189811208235013 135266779348089601544065)
                ·
                  refine ⟨101450084511067201158049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135266779348089601544065 101450084511067201158049)
                  ·
                    rfl

theorem cell20_222270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_222270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222270 prefixEnd_222270 := by exact prefixLift 222270
  have htrace : WordTrace (prefixWord ++ tailWord_222270) baseStart_222270 baseEnd_222270 := by
    simpa [prefixWord, tailWord_222270, baseEnd_222270] using wordTrace_append hprefix tailTrace_222270
  have hstable : (prefixWord ++ tailWord_222270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222270).length < 2 ^ (prefixWord ++ tailWord_222270).sum := by decide
  have hdescent : baseEnd_222270 < baseStart_222270 := by decide
  rcases family_descends (prefixWord ++ tailWord_222270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222294 : List Nat := [5, 2, 2, 1, 2, 1, 3, 4]
def baseStart_222294 : Nat := 118140960795 + 222294 * 2 ^ 59
def prefixEnd_222294 : Nat := 4983230072969 + 3 ^ 40 * 222294 * 2
def baseEnd_222294 : Nat := 33820346255009928119317

theorem tailTrace_222294 : CollatzResearch.WordTrace tailWord_222294 prefixEnd_222294 33820346255009928119317 := by
  unfold tailWord_222294
  simp only [CollatzResearch.WordTrace]
  refine ⟨506733016042142352361121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5405152171116185091851957 506733016042142352361121)
  ·
    refine ⟨380049762031606764270841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 506733016042142352361121 380049762031606764270841)
    ·
      refine ⟨285037321523705073203131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380049762031606764270841 285037321523705073203131)
      ·
        refine ⟨427555982285557609804697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285037321523705073203131 427555982285557609804697)
        ·
          refine ⟨320666986714168207353523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427555982285557609804697 320666986714168207353523)
          ·
            refine ⟨481000480071252311030285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320666986714168207353523 481000480071252311030285)
            ·
              refine ⟨180375180026719616636357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 481000480071252311030285 180375180026719616636357)
              ·
                refine ⟨33820346255009928119317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180375180026719616636357 33820346255009928119317)
                ·
                  rfl

theorem cell20_222294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_222294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222294 prefixEnd_222294 := by exact prefixLift 222294
  have htrace : WordTrace (prefixWord ++ tailWord_222294) baseStart_222294 baseEnd_222294 := by
    simpa [prefixWord, tailWord_222294, baseEnd_222294] using wordTrace_append hprefix tailTrace_222294
  have hstable : (prefixWord ++ tailWord_222294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222294).length < 2 ^ (prefixWord ++ tailWord_222294).sum := by decide
  have hdescent : baseEnd_222294 < baseStart_222294 := by decide
  rcases family_descends (prefixWord ++ tailWord_222294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222350 : List Nat := [4, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_222350 : Nat := 118140960795 + 222350 * 2 ^ 59
def prefixEnd_222350 : Nat := 4983230072969 + 3 ^ 40 * 222350 * 2
def baseEnd_222350 : Nat := 101486598690942478491055

theorem tailTrace_222350 : CollatzResearch.WordTrace tailWord_222350 prefixEnd_222350 101486598690942478491055 := by
  unfold tailWord_222350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1013721343058924900227063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5406513829647599467877669 1013721343058924900227063)
  ·
    refine ⟨1520582014588387350340595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1013721343058924900227063 1520582014588387350340595)
    ·
      refine ⟨2280873021882581025510893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1520582014588387350340595 2280873021882581025510893)
      ·
        refine ⟨855327383205967884566585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2280873021882581025510893 855327383205967884566585)
        ·
          refine ⟨641495537404475913424939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 855327383205967884566585 641495537404475913424939)
          ·
            refine ⟨962243306106713870137409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641495537404475913424939 962243306106713870137409)
            ·
              refine ⟨721682479580035402603057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 962243306106713870137409 721682479580035402603057)
              ·
                refine ⟨541261859685026551952293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 721682479580035402603057 541261859685026551952293)
                ·
                  refine ⟨101486598690942478491055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 541261859685026551952293 101486598690942478491055)
                  ·
                    rfl

theorem cell20_222350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_222350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222350 prefixEnd_222350 := by exact prefixLift 222350
  have htrace : WordTrace (prefixWord ++ tailWord_222350) baseStart_222350 baseEnd_222350 := by
    simpa [prefixWord, tailWord_222350, baseEnd_222350] using wordTrace_append hprefix tailTrace_222350
  have hstable : (prefixWord ++ tailWord_222350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222350).length < 2 ^ (prefixWord ++ tailWord_222350).sum := by decide
  have hdescent : baseEnd_222350 < baseStart_222350 := by decide
  rcases family_descends (prefixWord ++ tailWord_222350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222364 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 5]
def baseStart_222364 : Nat := 118140960795 + 222364 * 2 ^ 59
def prefixEnd_222364 : Nat := 4983230072969 + 3 ^ 40 * 222364 * 2
def baseEnd_222364 : Nat := 101492988672420652024331

theorem tailTrace_222364 : CollatzResearch.WordTrace tailWord_222364 prefixEnd_222364 101492988672420652024331 := by
  unfold tailWord_222364
  simp only [CollatzResearch.WordTrace]
  refine ⟨4055140683210339796413073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5406854244280453061884097 4055140683210339796413073)
  ·
    refine ⟨3041355512407754847309805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4055140683210339796413073 3041355512407754847309805)
    ·
      refine ⟨1140508317152908067741177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3041355512407754847309805 1140508317152908067741177)
      ·
        refine ⟨855381237864681050805883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1140508317152908067741177 855381237864681050805883)
        ·
          refine ⟨1283071856797021576208825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855381237864681050805883 1283071856797021576208825)
          ·
            refine ⟨962303892597766182156619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1283071856797021576208825 962303892597766182156619)
            ·
              refine ⟨1443455838896649273234929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962303892597766182156619 1443455838896649273234929)
              ·
                refine ⟨1082591879172486954926197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1443455838896649273234929 1082591879172486954926197)
                ·
                  refine ⟨101492988672420652024331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1082591879172486954926197 101492988672420652024331)
                  ·
                    rfl

theorem cell20_222364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_222364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222364 prefixEnd_222364 := by exact prefixLift 222364
  have htrace : WordTrace (prefixWord ++ tailWord_222364) baseStart_222364 baseEnd_222364 := by
    simpa [prefixWord, tailWord_222364, baseEnd_222364] using wordTrace_append hprefix tailTrace_222364
  have hstable : (prefixWord ++ tailWord_222364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222364).length < 2 ^ (prefixWord ++ tailWord_222364).sum := by decide
  have hdescent : baseEnd_222364 < baseStart_222364 := by decide
  rcases family_descends (prefixWord ++ tailWord_222364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222398 : List Nat := [4, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_222398 : Nat := 118140960795 + 222398 * 2 ^ 59
def prefixEnd_222398 : Nat := 4983230072969 + 3 ^ 40 * 222398 * 2
def baseEnd_222398 : Nat := 101508507198867644890859

theorem tailTrace_222398 : CollatzResearch.WordTrace tailWord_222398 prefixEnd_222398 101508507198867644890859 := by
  unfold tailWord_222398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1013940181037187924945481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5407680965531668933042565 1013940181037187924945481)
  ·
    refine ⟨760455135777890943709111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1013940181037187924945481 760455135777890943709111)
    ·
      refine ⟨1140682703666836415563667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 760455135777890943709111 1140682703666836415563667)
      ·
        refine ⟨1711024055500254623345501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1140682703666836415563667 1711024055500254623345501)
        ·
          refine ⟨641634020812595483754563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1711024055500254623345501 641634020812595483754563)
          ·
            refine ⟨962451031218893225631845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641634020812595483754563 962451031218893225631845)
            ·
              refine ⟨180459568353542479805971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 962451031218893225631845 180459568353542479805971)
              ·
                refine ⟨270689352530313719708957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180459568353542479805971 270689352530313719708957)
                ·
                  refine ⟨101508507198867644890859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270689352530313719708957 101508507198867644890859)
                  ·
                    rfl

theorem cell20_222398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_222398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222398 prefixEnd_222398 := by exact prefixLift 222398
  have htrace : WordTrace (prefixWord ++ tailWord_222398) baseStart_222398 baseEnd_222398 := by
    simpa [prefixWord, tailWord_222398, baseEnd_222398] using wordTrace_append hprefix tailTrace_222398
  have hstable : (prefixWord ++ tailWord_222398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222398).length < 2 ^ (prefixWord ++ tailWord_222398).sum := by decide
  have hdescent : baseEnd_222398 < baseStart_222398 := by decide
  rcases family_descends (prefixWord ++ tailWord_222398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222423 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 7]
def baseStart_222423 : Nat := 118140960795 + 222423 * 2 ^ 59
def prefixEnd_222423 : Nat := 4983230072969 + 3 ^ 40 * 222423 * 2
def baseEnd_222423 : Nat := 101519917880078669057423

theorem tailTrace_222423 : CollatzResearch.WordTrace tailWord_222423 prefixEnd_222423 101519917880078669057423 := by
  unfold tailWord_222423
  simp only [CollatzResearch.WordTrace]
  refine ⟨8112433273206932669223923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5408288848804621779482615 8112433273206932669223923)
  ·
    refine ⟨12168649909810399003835885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8112433273206932669223923 12168649909810399003835885)
    ·
      refine ⟨4563243716178899626438457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12168649909810399003835885 4563243716178899626438457)
      ·
        refine ⟨3422432787134174719828843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4563243716178899626438457 3422432787134174719828843)
        ·
          refine ⟨5133649180701262079743265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3422432787134174719828843 5133649180701262079743265)
          ·
            refine ⟨3850236885525946559807449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5133649180701262079743265 3850236885525946559807449)
            ·
              refine ⟨2887677664144459919855587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3850236885525946559807449 2887677664144459919855587)
              ·
                refine ⟨4331516496216689879783381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2887677664144459919855587 4331516496216689879783381)
                ·
                  refine ⟨101519917880078669057423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4331516496216689879783381 101519917880078669057423)
                  ·
                    rfl

theorem cell20_222423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_222423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222423 prefixEnd_222423 := by exact prefixLift 222423
  have htrace : WordTrace (prefixWord ++ tailWord_222423) baseStart_222423 baseEnd_222423 := by
    simpa [prefixWord, tailWord_222423, baseEnd_222423] using wordTrace_append hprefix tailTrace_222423
  have hstable : (prefixWord ++ tailWord_222423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222423).length < 2 ^ (prefixWord ++ tailWord_222423).sum := by decide
  have hdescent : baseEnd_222423 < baseStart_222423 := by decide
  rcases family_descends (prefixWord ++ tailWord_222423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222426 : List Nat := [3, 1, 1, 2, 2, 1, 1, 7, 2]
def baseStart_222426 : Nat := 118140960795 + 222426 * 2 ^ 59
def prefixEnd_222426 : Nat := 4983230072969 + 3 ^ 40 * 222426 * 2
def baseEnd_222426 : Nat := 101521287161823991957411

theorem tailTrace_222426 : CollatzResearch.WordTrace tailWord_222426 prefixEnd_222426 101521287161823991957411 := by
  unfold tailWord_222426
  simp only [CollatzResearch.WordTrace]
  refine ⟨2028135673049016045395783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5408361794797376121055421 2028135673049016045395783)
  ·
    refine ⟨3042203509573524068093675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2028135673049016045395783 3042203509573524068093675)
    ·
      refine ⟨4563305264360286102140513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3042203509573524068093675 4563305264360286102140513)
      ·
        refine ⟨3422478948270214576605385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4563305264360286102140513 3422478948270214576605385)
        ·
          refine ⟨2566859211202660932454039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3422478948270214576605385 2566859211202660932454039)
          ·
            refine ⟨3850288816803991398681059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2566859211202660932454039 3850288816803991398681059)
            ·
              refine ⟨5775433225205987098021589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3850288816803991398681059 5775433225205987098021589)
              ·
                refine ⟨135361716215765322609881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5775433225205987098021589 135361716215765322609881)
                ·
                  refine ⟨101521287161823991957411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135361716215765322609881 101521287161823991957411)
                  ·
                    rfl

theorem cell20_222426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 2].length) (baseStart_222426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222426 prefixEnd_222426 := by exact prefixLift 222426
  have htrace : WordTrace (prefixWord ++ tailWord_222426) baseStart_222426 baseEnd_222426 := by
    simpa [prefixWord, tailWord_222426, baseEnd_222426] using wordTrace_append hprefix tailTrace_222426
  have hstable : (prefixWord ++ tailWord_222426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222426).length < 2 ^ (prefixWord ++ tailWord_222426).sum := by decide
  have hdescent : baseEnd_222426 < baseStart_222426 := by decide
  rcases family_descends (prefixWord ++ tailWord_222426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222439 : List Nat := [1, 1, 5, 3, 2, 2, 2, 2, 2]
def baseStart_222439 : Nat := 118140960795 + 222439 * 2 ^ 59
def prefixEnd_222439 : Nat := 4983230072969 + 3 ^ 40 * 222439 * 2
def baseEnd_222439 : Nat := 101527220716053724524025

theorem tailTrace_222439 : CollatzResearch.WordTrace tailWord_222439 prefixEnd_222439 101527220716053724524025 := by
  unfold tailWord_222439
  simp only [CollatzResearch.WordTrace]
  refine ⟨8113016841148967401806371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5408677894099311601204247 8113016841148967401806371)
  ·
    refine ⟨12169525261723451102709557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8113016841148967401806371 12169525261723451102709557)
    ·
      refine ⟨1140892993286573540879021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12169525261723451102709557 1140892993286573540879021)
      ·
        refine ⟨427834872482465077829633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1140892993286573540879021 427834872482465077829633)
        ·
          refine ⟨320876154361848808372225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427834872482465077829633 320876154361848808372225)
          ·
            refine ⟨240657115771386606279169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320876154361848808372225 240657115771386606279169)
            ·
              refine ⟨180492836828539954709377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240657115771386606279169 180492836828539954709377)
              ·
                refine ⟨135369627621404966032033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180492836828539954709377 135369627621404966032033)
                ·
                  refine ⟨101527220716053724524025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135369627621404966032033 101527220716053724524025)
                  ·
                    rfl

theorem cell20_222439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 2].length) (baseStart_222439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222439 prefixEnd_222439 := by exact prefixLift 222439
  have htrace : WordTrace (prefixWord ++ tailWord_222439) baseStart_222439 baseEnd_222439 := by
    simpa [prefixWord, tailWord_222439, baseEnd_222439] using wordTrace_append hprefix tailTrace_222439
  have hstable : (prefixWord ++ tailWord_222439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222439).length < 2 ^ (prefixWord ++ tailWord_222439).sum := by decide
  have hdescent : baseEnd_222439 < baseStart_222439 := by decide
  rcases family_descends (prefixWord ++ tailWord_222439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222443 : List Nat := [1, 1, 1, 1, 2, 6, 4, 2, 2]
def baseStart_222443 : Nat := 118140960795 + 222443 * 2 ^ 59
def prefixEnd_222443 : Nat := 4983230072969 + 3 ^ 40 * 222443 * 2
def baseEnd_222443 : Nat := 101529046425047488390675

theorem tailTrace_222443 : CollatzResearch.WordTrace tailWord_222443 prefixEnd_222443 101529046425047488390675 := by
  unfold tailWord_222443
  simp only [CollatzResearch.WordTrace]
  refine ⟨8113162733134476084951983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5408775155422984056634655 8113162733134476084951983)
  ·
    refine ⟨12169744099701714127427975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8113162733134476084951983 12169744099701714127427975)
    ·
      refine ⟨18254616149552571191141963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12169744099701714127427975 18254616149552571191141963)
      ·
        refine ⟨27381924224328856786712945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18254616149552571191141963 27381924224328856786712945)
        ·
          refine ⟨20536443168246642590034709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27381924224328856786712945 20536443168246642590034709)
          ·
            refine ⟨962645773511561371407877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20536443168246642590034709 962645773511561371407877)
            ·
              refine ⟨180496082533417757138977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 962645773511561371407877 180496082533417757138977)
              ·
                refine ⟨135372061900063317854233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180496082533417757138977 135372061900063317854233)
                ·
                  refine ⟨101529046425047488390675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135372061900063317854233 101529046425047488390675)
                  ·
                    rfl

theorem cell20_222443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 2].length) (baseStart_222443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222443 prefixEnd_222443 := by exact prefixLift 222443
  have htrace : WordTrace (prefixWord ++ tailWord_222443) baseStart_222443 baseEnd_222443 := by
    simpa [prefixWord, tailWord_222443, baseEnd_222443] using wordTrace_append hprefix tailTrace_222443
  have hstable : (prefixWord ++ tailWord_222443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222443).length < 2 ^ (prefixWord ++ tailWord_222443).sum := by decide
  have hdescent : baseEnd_222443 < baseStart_222443 := by decide
  rcases family_descends (prefixWord ++ tailWord_222443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222450 : List Nat := [3, 2, 1, 3, 3, 2, 1, 5]
def baseStart_222450 : Nat := 118140960795 + 222450 * 2 ^ 59
def prefixEnd_222450 : Nat := 4983230072969 + 3 ^ 40 * 222450 * 2
def baseEnd_222450 : Nat := 33844080471928858385771

theorem tailTrace_222450 : CollatzResearch.WordTrace tailWord_222450 prefixEnd_222450 33844080471928858385771 := by
  unfold tailWord_222450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2028354511027279070114201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5408945362739410853637869 2028354511027279070114201)
  ·
    refine ⟨1521265883270459302585651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2028354511027279070114201 1521265883270459302585651)
    ·
      refine ⟨2281898824905688953878477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1521265883270459302585651 2281898824905688953878477)
      ·
        refine ⟨855712059339633357704429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2281898824905688953878477 855712059339633357704429)
        ·
          refine ⟨320892022252362509139161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 855712059339633357704429 320892022252362509139161)
          ·
            refine ⟨240669016689271881854371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320892022252362509139161 240669016689271881854371)
            ·
              refine ⟨361003525033907822781557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240669016689271881854371 361003525033907822781557)
              ·
                refine ⟨33844080471928858385771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 361003525033907822781557 33844080471928858385771)
                ·
                  rfl

theorem cell20_222450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_222450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222450 prefixEnd_222450 := by exact prefixLift 222450
  have htrace : WordTrace (prefixWord ++ tailWord_222450) baseStart_222450 baseEnd_222450 := by
    simpa [prefixWord, tailWord_222450, baseEnd_222450] using wordTrace_append hprefix tailTrace_222450
  have hstable : (prefixWord ++ tailWord_222450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222450).length < 2 ^ (prefixWord ++ tailWord_222450).sum := by decide
  have hdescent : baseEnd_222450 < baseStart_222450 := by decide
  rcases family_descends (prefixWord ++ tailWord_222450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222461 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 9]
def baseStart_222461 : Nat := 118140960795 + 222461 * 2 ^ 59
def prefixEnd_222461 : Nat := 4983230072969 + 3 ^ 40 * 222461 * 2
def baseEnd_222461 : Nat := 101537262115519425790601

theorem tailTrace_222461 : CollatzResearch.WordTrace tailWord_222461 prefixEnd_222461 101537262115519425790601 := by
  unfold tailWord_222461
  simp only [CollatzResearch.WordTrace]
  refine ⟨8113819247069265159107237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5409212831379510106071491 8113819247069265159107237)
  ·
    refine ⟨1521341108825487217332607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8113819247069265159107237 1521341108825487217332607)
    ·
      refine ⟨2282011663238230825998911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1521341108825487217332607 2282011663238230825998911)
      ·
        refine ⟨3423017494857346238998367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2282011663238230825998911 3423017494857346238998367)
        ·
          refine ⟨5134526242286019358497551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3423017494857346238998367 5134526242286019358497551)
          ·
            refine ⟨7701789363429029037746327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5134526242286019358497551 7701789363429029037746327)
            ·
              refine ⟨11552684045143543556619491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7701789363429029037746327 11552684045143543556619491)
              ·
                refine ⟨17329026067715315334929237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11552684045143543556619491 17329026067715315334929237)
                ·
                  refine ⟨101537262115519425790601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17329026067715315334929237 101537262115519425790601)
                  ·
                    rfl

theorem cell20_222461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_222461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222461 prefixEnd_222461 := by exact prefixLift 222461
  have htrace : WordTrace (prefixWord ++ tailWord_222461) baseStart_222461 baseEnd_222461 := by
    simpa [prefixWord, tailWord_222461, baseEnd_222461] using wordTrace_append hprefix tailTrace_222461
  have hstable : (prefixWord ++ tailWord_222461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222461).length < 2 ^ (prefixWord ++ tailWord_222461).sum := by decide
  have hdescent : baseEnd_222461 < baseStart_222461 := by decide
  rcases family_descends (prefixWord ++ tailWord_222461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222537 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 5]
def baseStart_222537 : Nat := 118140960795 + 222537 * 2 ^ 59
def prefixEnd_222537 : Nat := 4983230072969 + 3 ^ 40 * 222537 * 2
def baseEnd_222537 : Nat := 101571950586400939256957

theorem tailTrace_222537 : CollatzResearch.WordTrace tailWord_222537 prefixEnd_222537 101571950586400939256957 := by
  unfold tailWord_222537
  simp only [CollatzResearch.WordTrace]
  refine ⟨8116591194793930138873865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5411060796529286759249243 8116591194793930138873865)
  ·
    refine ⟨6087443396095447604155399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8116591194793930138873865 6087443396095447604155399)
    ·
      refine ⟨9131165094143171406233099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6087443396095447604155399 9131165094143171406233099)
      ·
        refine ⟨13696747641214757109349649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9131165094143171406233099 13696747641214757109349649)
        ·
          refine ⟨10272560730911067832012237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13696747641214757109349649 10272560730911067832012237)
          ·
            refine ⟨3852210274091650437004589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10272560730911067832012237 3852210274091650437004589)
            ·
              refine ⟨1444578852784368913876721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3852210274091650437004589 1444578852784368913876721)
              ·
                refine ⟨1083434139588276685407541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1444578852784368913876721 1083434139588276685407541)
                ·
                  refine ⟨101571950586400939256957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1083434139588276685407541 101571950586400939256957)
                  ·
                    rfl

theorem cell20_222537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_222537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222537 prefixEnd_222537 := by exact prefixLift 222537
  have htrace : WordTrace (prefixWord ++ tailWord_222537) baseStart_222537 baseEnd_222537 := by
    simpa [prefixWord, tailWord_222537, baseEnd_222537] using wordTrace_append hprefix tailTrace_222537
  have hstable : (prefixWord ++ tailWord_222537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222537).length < 2 ^ (prefixWord ++ tailWord_222537).sum := by decide
  have hdescent : baseEnd_222537 < baseStart_222537 := by decide
  rcases family_descends (prefixWord ++ tailWord_222537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222567 : List Nat := [1, 1, 5, 1, 5, 1, 2, 1, 3]
def baseStart_222567 : Nat := 118140960795 + 222567 * 2 ^ 59
def prefixEnd_222567 : Nat := 4983230072969 + 3 ^ 40 * 222567 * 2
def baseEnd_222567 : Nat := 101585643403854168256835

theorem tailTrace_222567 : CollatzResearch.WordTrace tailWord_222567 prefixEnd_222567 101585643403854168256835 := by
  unfold tailWord_222567
  simp only [CollatzResearch.WordTrace]
  refine ⟨8117685384685245262465955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5411790256456830174977303 8117685384685245262465955)
  ·
    refine ⟨12176528077027867893698933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8117685384685245262465955 12176528077027867893698933)
    ·
      refine ⟨1141549507221362615034275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12176528077027867893698933 1141549507221362615034275)
      ·
        refine ⟨1712324260832043922551413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1141549507221362615034275 1712324260832043922551413)
        ·
          refine ⟨160530399453004117739195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1712324260832043922551413 160530399453004117739195)
          ·
            refine ⟨240795599179506176608793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160530399453004117739195 240795599179506176608793)
            ·
              refine ⟨180596699384629632456595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240795599179506176608793 180596699384629632456595)
              ·
                refine ⟨270895049076944448684893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180596699384629632456595 270895049076944448684893)
                ·
                  refine ⟨101585643403854168256835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270895049076944448684893 101585643403854168256835)
                  ·
                    rfl

theorem cell20_222567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 3].length) (baseStart_222567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222567 prefixEnd_222567 := by exact prefixLift 222567
  have htrace : WordTrace (prefixWord ++ tailWord_222567) baseStart_222567 baseEnd_222567 := by
    simpa [prefixWord, tailWord_222567, baseEnd_222567] using wordTrace_append hprefix tailTrace_222567
  have hstable : (prefixWord ++ tailWord_222567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222567).length < 2 ^ (prefixWord ++ tailWord_222567).sum := by decide
  have hdescent : baseEnd_222567 < baseStart_222567 := by decide
  rcases family_descends (prefixWord ++ tailWord_222567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222606 : List Nat := [4, 1, 1, 4, 10]
def baseStart_222606 : Nat := 118140960795 + 222606 * 2 ^ 59
def prefixEnd_222606 : Nat := 4983230072969 + 3 ^ 40 * 222606 * 2
def baseEnd_222606 : Nat := 1254363506994362542675

theorem tailTrace_222606 : CollatzResearch.WordTrace tailWord_222606 prefixEnd_222606 1254363506994362542675 := by
  unfold tailWord_222606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1014888478942994365391959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5412738554362636615423781 1014888478942994365391959)
  ·
    refine ⟨1522332718414491548087939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1014888478942994365391959 1522332718414491548087939)
    ·
      refine ⟨2283499077621737322131909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1522332718414491548087939 2283499077621737322131909)
      ·
        refine ⟨428156077054075747899733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2283499077621737322131909 428156077054075747899733)
        ·
          refine ⟨1254363506994362542675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 428156077054075747899733 1254363506994362542675)
          ·
            rfl

theorem cell20_222606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 10].length) (baseStart_222606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222606 prefixEnd_222606 := by exact prefixLift 222606
  have htrace : WordTrace (prefixWord ++ tailWord_222606) baseStart_222606 baseEnd_222606 := by
    simpa [prefixWord, tailWord_222606, baseEnd_222606] using wordTrace_append hprefix tailTrace_222606
  have hstable : (prefixWord ++ tailWord_222606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222606).length < 2 ^ (prefixWord ++ tailWord_222606).sum := by decide
  have hdescent : baseEnd_222606 < baseStart_222606 := by decide
  rcases family_descends (prefixWord ++ tailWord_222606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222612 : List Nat := [2, 4, 2, 1, 2, 1, 4, 2, 2]
def baseStart_222612 : Nat := 118140960795 + 222612 * 2 ^ 59
def prefixEnd_222612 : Nat := 4983230072969 + 3 ^ 40 * 222612 * 2
def baseEnd_222612 : Nat := 101606182630034011756651

theorem tailTrace_222612 : CollatzResearch.WordTrace tailWord_222612 prefixEnd_222612 101606182630034011756651 := by
  unfold tailWord_222612
  simp only [CollatzResearch.WordTrace]
  refine ⟨4059663334761108973927045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5412884446348145298569393 4059663334761108973927045)
  ·
    refine ⟨761186875267707932611321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4059663334761108973927045 761186875267707932611321)
    ·
      refine ⟨570890156450780949458491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 761186875267707932611321 570890156450780949458491)
      ·
        refine ⟨856335234676171424187737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570890156450780949458491 856335234676171424187737)
        ·
          refine ⟨642251426007128568140803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 856335234676171424187737 642251426007128568140803)
          ·
            refine ⟨963377139010692852211205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642251426007128568140803 963377139010692852211205)
            ·
              refine ⟨180633213564504909789601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 963377139010692852211205 180633213564504909789601)
              ·
                refine ⟨135474910173378682342201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180633213564504909789601 135474910173378682342201)
                ·
                  refine ⟨101606182630034011756651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135474910173378682342201 101606182630034011756651)
                  ·
                    rfl

theorem cell20_222612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_222612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222612 prefixEnd_222612 := by exact prefixLift 222612
  have htrace : WordTrace (prefixWord ++ tailWord_222612) baseStart_222612 baseEnd_222612 := by
    simpa [prefixWord, tailWord_222612, baseEnd_222612] using wordTrace_append hprefix tailTrace_222612
  have hstable : (prefixWord ++ tailWord_222612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222612).length < 2 ^ (prefixWord ++ tailWord_222612).sum := by decide
  have hdescent : baseEnd_222612 < baseStart_222612 := by decide
  rcases family_descends (prefixWord ++ tailWord_222612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222613 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 5]
def baseStart_222613 : Nat := 118140960795 + 222613 * 2 ^ 59
def prefixEnd_222613 : Nat := 4983230072969 + 3 ^ 40 * 222613 * 2
def baseEnd_222613 : Nat := 101606639057282452723313

theorem tailTrace_222613 : CollatzResearch.WordTrace tailWord_222613 prefixEnd_222613 101606639057282452723313 := by
  unfold tailWord_222613
  simp only [CollatzResearch.WordTrace]
  refine ⟨8119363142518595118640493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5412908761679063412426995 8119363142518595118640493)
  ·
    refine ⟨3044761178444473169490185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8119363142518595118640493 3044761178444473169490185)
    ·
      refine ⟨2283570883833354877117639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3044761178444473169490185 2283570883833354877117639)
      ·
        refine ⟨3425356325750032315676459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2283570883833354877117639 3425356325750032315676459)
        ·
          refine ⟨5138034488625048473514689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3425356325750032315676459 5138034488625048473514689)
          ·
            refine ⟨3853525866468786355136017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5138034488625048473514689 3853525866468786355136017)
            ·
              refine ⟨2890144399851589766352013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3853525866468786355136017 2890144399851589766352013)
              ·
                refine ⟨1083804149944346162382005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2890144399851589766352013 1083804149944346162382005)
                ·
                  refine ⟨101606639057282452723313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1083804149944346162382005 101606639057282452723313)
                  ·
                    rfl

theorem cell20_222613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_222613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222613 prefixEnd_222613 := by exact prefixLift 222613
  have htrace : WordTrace (prefixWord ++ tailWord_222613) baseStart_222613 baseEnd_222613 := by
    simpa [prefixWord, tailWord_222613, baseEnd_222613] using wordTrace_append hprefix tailTrace_222613
  have hstable : (prefixWord ++ tailWord_222613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222613).length < 2 ^ (prefixWord ++ tailWord_222613).sum := by decide
  have hdescent : baseEnd_222613 < baseStart_222613 := by decide
  rcases family_descends (prefixWord ++ tailWord_222613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222623 : List Nat := [1, 1, 2, 5, 1, 4, 1, 5]
def baseStart_222623 : Nat := 118140960795 + 222623 * 2 ^ 59
def prefixEnd_222623 : Nat := 4983230072969 + 3 ^ 40 * 222623 * 2
def baseEnd_222623 : Nat := 33870401109922287463313

theorem tailTrace_222623 : CollatzResearch.WordTrace tailWord_222623 prefixEnd_222623 33870401109922287463313 := by
  unfold tailWord_222623
  simp only [CollatzResearch.WordTrace]
  refine ⟨8119727872482366826504523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5413151914988244551003015 8119727872482366826504523)
  ·
    refine ⟨12179591808723550239756785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8119727872482366826504523 12179591808723550239756785)
    ·
      refine ⟨9134693856542662679817589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12179591808723550239756785 9134693856542662679817589)
      ·
        refine ⟨856377549050874626232899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9134693856542662679817589 856377549050874626232899)
        ·
          refine ⟨1284566323576311939349349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 856377549050874626232899 1284566323576311939349349)
          ·
            refine ⟨240856185670558488628003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1284566323576311939349349 240856185670558488628003)
            ·
              refine ⟨361284278505837732942005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240856185670558488628003 361284278505837732942005)
              ·
                refine ⟨33870401109922287463313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 361284278505837732942005 33870401109922287463313)
                ·
                  rfl

theorem cell20_222623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 5].length) (baseStart_222623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222623 prefixEnd_222623 := by exact prefixLift 222623
  have htrace : WordTrace (prefixWord ++ tailWord_222623) baseStart_222623 baseEnd_222623 := by
    simpa [prefixWord, tailWord_222623, baseEnd_222623] using wordTrace_append hprefix tailTrace_222623
  have hstable : (prefixWord ++ tailWord_222623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222623).length < 2 ^ (prefixWord ++ tailWord_222623).sum := by decide
  have hdescent : baseEnd_222623 < baseStart_222623 := by decide
  rcases family_descends (prefixWord ++ tailWord_222623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222668 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 5]
def baseStart_222668 : Nat := 118140960795 + 222668 * 2 ^ 59
def prefixEnd_222668 : Nat := 4983230072969 + 3 ^ 40 * 222668 * 2
def baseEnd_222668 : Nat := 101631742555946705889755

theorem tailTrace_222668 : CollatzResearch.WordTrace tailWord_222668 prefixEnd_222668 101631742555946705889755 := by
  unfold tailWord_222668
  simp only [CollatzResearch.WordTrace]
  refine ⟨4060684578659669755946329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5414246104879559674595105 4060684578659669755946329)
  ·
    refine ⟨3045513433994752316959747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4060684578659669755946329 3045513433994752316959747)
    ·
      refine ⟨4568270150992128475439621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3045513433994752316959747 4568270150992128475439621)
      ·
        refine ⟨856550653311024089144929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4568270150992128475439621 856550653311024089144929)
        ·
          refine ⟨642412989983268066858697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 856550653311024089144929 642412989983268066858697)
          ·
            refine ⟨481809742487451050144023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 642412989983268066858697 481809742487451050144023)
            ·
              refine ⟨722714613731176575216035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481809742487451050144023 722714613731176575216035)
              ·
                refine ⟨1084071920596764862824053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 722714613731176575216035 1084071920596764862824053)
                ·
                  refine ⟨101631742555946705889755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1084071920596764862824053 101631742555946705889755)
                  ·
                    rfl

theorem cell20_222668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_222668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222668 prefixEnd_222668 := by exact prefixLift 222668
  have htrace : WordTrace (prefixWord ++ tailWord_222668) baseStart_222668 baseEnd_222668 := by
    simpa [prefixWord, tailWord_222668, baseEnd_222668] using wordTrace_append hprefix tailTrace_222668
  have hstable : (prefixWord ++ tailWord_222668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222668).length < 2 ^ (prefixWord ++ tailWord_222668).sum := by decide
  have hdescent : baseEnd_222668 < baseStart_222668 := by decide
  rcases family_descends (prefixWord ++ tailWord_222668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222706 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_222706 : Nat := 118140960795 + 222706 * 2 ^ 59
def prefixEnd_222706 : Nat := 4983230072969 + 3 ^ 40 * 222706 * 2
def baseEnd_222706 : Nat := 101649086791387462622933

theorem tailTrace_222706 : CollatzResearch.WordTrace tailWord_222706 prefixEnd_222706 101649086791387462622933 := by
  unfold tailWord_222706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2030688782795418000443993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5415170087454448001183981 2030688782795418000443993)
  ·
    refine ⟨1523016587096563500332995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2030688782795418000443993 1523016587096563500332995)
    ·
      refine ⟨2284524880644845250499493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1523016587096563500332995 2284524880644845250499493)
      ·
        refine ⟨428348415120908484468655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2284524880644845250499493 428348415120908484468655)
        ·
          refine ⟨642522622681362726702983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428348415120908484468655 642522622681362726702983)
          ·
            refine ⟨963783934022044090054475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642522622681362726702983 963783934022044090054475)
            ·
              refine ⟨1445675901033066135081713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 963783934022044090054475 1445675901033066135081713)
              ·
                refine ⟨1084256925774799601311285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1445675901033066135081713 1084256925774799601311285)
                ·
                  refine ⟨101649086791387462622933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1084256925774799601311285 101649086791387462622933)
                  ·
                    rfl

theorem cell20_222706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_222706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222706 prefixEnd_222706 := by exact prefixLift 222706
  have htrace : WordTrace (prefixWord ++ tailWord_222706) baseStart_222706 baseEnd_222706 := by
    simpa [prefixWord, tailWord_222706, baseEnd_222706] using wordTrace_append hprefix tailTrace_222706
  have hstable : (prefixWord ++ tailWord_222706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222706).length < 2 ^ (prefixWord ++ tailWord_222706).sum := by decide
  have hdescent : baseEnd_222706 < baseStart_222706 := by decide
  rcases family_descends (prefixWord ++ tailWord_222706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222730 : List Nat := [3, 1, 2, 2, 2, 4, 1, 1, 4]
def baseStart_222730 : Nat := 118140960795 + 222730 * 2 ^ 59
def prefixEnd_222730 : Nat := 4983230072969 + 3 ^ 40 * 222730 * 2
def baseEnd_222730 : Nat := 101660041045350045822835

theorem tailTrace_222730 : CollatzResearch.WordTrace tailWord_222730 prefixEnd_222730 101660041045350045822835 := by
  unfold tailWord_222730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2030907620773681025162411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5415753655396482733766429 2030907620773681025162411)
  ·
    refine ⟨3046361431160521537743617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2030907620773681025162411 3046361431160521537743617)
    ·
      refine ⟨2284771073370391153307713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3046361431160521537743617 2284771073370391153307713)
      ·
        refine ⟨1713578305027793364980785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2284771073370391153307713 1713578305027793364980785)
        ·
          refine ⟨1285183728770845023735589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1713578305027793364980785 1285183728770845023735589)
          ·
            refine ⟨240971949144533441950423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1285183728770845023735589 240971949144533441950423)
            ·
              refine ⟨361457923716800162925635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240971949144533441950423 361457923716800162925635)
              ·
                refine ⟨542186885575200244388453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361457923716800162925635 542186885575200244388453)
                ·
                  refine ⟨101660041045350045822835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 542186885575200244388453 101660041045350045822835)
                  ·
                    rfl

theorem cell20_222730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_222730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222730 prefixEnd_222730 := by exact prefixLift 222730
  have htrace : WordTrace (prefixWord ++ tailWord_222730) baseStart_222730 baseEnd_222730 := by
    simpa [prefixWord, tailWord_222730, baseEnd_222730] using wordTrace_append hprefix tailTrace_222730
  have hstable : (prefixWord ++ tailWord_222730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222730).length < 2 ^ (prefixWord ++ tailWord_222730).sum := by decide
  have hdescent : baseEnd_222730 < baseStart_222730 := by decide
  rcases family_descends (prefixWord ++ tailWord_222730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222733 : List Nat := [1, 7, 1, 1, 2, 1, 2, 5]
def baseStart_222733 : Nat := 118140960795 + 222733 * 2 ^ 59
def prefixEnd_222733 : Nat := 4983230072969 + 3 ^ 40 * 222733 * 2
def baseEnd_222733 : Nat := 33887136775698456240941

theorem tailTrace_222733 : CollatzResearch.WordTrace tailWord_222733 prefixEnd_222733 33887136775698456240941 := by
  unfold tailWord_222733
  simp only [CollatzResearch.WordTrace]
  refine ⟨8123739902083855613008853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5415826601389237075339235 8123739902083855613008853)
  ·
    refine ⟨190400153955090365929895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 8123739902083855613008853 190400153955090365929895)
    ·
      refine ⟨285600230932635548894843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190400153955090365929895 285600230932635548894843)
      ·
        refine ⟨428400346398953323342265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285600230932635548894843 428400346398953323342265)
        ·
          refine ⟨321300259799214992506699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428400346398953323342265 321300259799214992506699)
          ·
            refine ⟨481950389698822488760049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321300259799214992506699 481950389698822488760049)
            ·
              refine ⟨361462792274116866570037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481950389698822488760049 361462792274116866570037)
              ·
                refine ⟨33887136775698456240941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 361462792274116866570037 33887136775698456240941)
                ·
                  rfl

theorem cell20_222733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 5].length) (baseStart_222733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222733 prefixEnd_222733 := by exact prefixLift 222733
  have htrace : WordTrace (prefixWord ++ tailWord_222733) baseStart_222733 baseEnd_222733 := by
    simpa [prefixWord, tailWord_222733, baseEnd_222733] using wordTrace_append hprefix tailTrace_222733
  have hstable : (prefixWord ++ tailWord_222733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222733).length < 2 ^ (prefixWord ++ tailWord_222733).sum := by decide
  have hdescent : baseEnd_222733 < baseStart_222733 := by decide
  rcases family_descends (prefixWord ++ tailWord_222733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222740 : List Nat := [2, 4, 3, 1, 2, 1, 1, 3, 3]
def baseStart_222740 : Nat := 118140960795 + 222740 * 2 ^ 59
def prefixEnd_222740 : Nat := 4983230072969 + 3 ^ 40 * 222740 * 2
def baseEnd_222740 : Nat := 101664605317834455489461

theorem tailTrace_222740 : CollatzResearch.WordTrace tailWord_222740 prefixEnd_222740 101664605317834455489461 := by
  unfold tailWord_222740
  simp only [CollatzResearch.WordTrace]
  refine ⟨4061997606529247904256837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5415996808705663872342449 4061997606529247904256837)
  ·
    refine ⟨761624551224233982048157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4061997606529247904256837 761624551224233982048157)
    ·
      refine ⟨285609206709087743268059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 761624551224233982048157 285609206709087743268059)
      ·
        refine ⟨428413810063631614902089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285609206709087743268059 428413810063631614902089)
        ·
          refine ⟨321310357547723711176567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 428413810063631614902089 321310357547723711176567)
          ·
            refine ⟨481965536321585566764851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321310357547723711176567 481965536321585566764851)
            ·
              refine ⟨722948304482378350147277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481965536321585566764851 722948304482378350147277)
              ·
                refine ⟨271105614180891881305229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 722948304482378350147277 271105614180891881305229)
                ·
                  refine ⟨101664605317834455489461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271105614180891881305229 101664605317834455489461)
                  ·
                    rfl

theorem cell20_222740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_222740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222740 prefixEnd_222740 := by exact prefixLift 222740
  have htrace : WordTrace (prefixWord ++ tailWord_222740) baseStart_222740 baseEnd_222740 := by
    simpa [prefixWord, tailWord_222740, baseEnd_222740] using wordTrace_append hprefix tailTrace_222740
  have hstable : (prefixWord ++ tailWord_222740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222740).length < 2 ^ (prefixWord ++ tailWord_222740).sum := by decide
  have hdescent : baseEnd_222740 < baseStart_222740 := by decide
  rcases family_descends (prefixWord ++ tailWord_222740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222781 : List Nat := [1, 4, 1, 3, 4, 1, 2, 2, 2]
def baseStart_222781 : Nat := 118140960795 + 222781 * 2 ^ 59
def prefixEnd_222781 : Nat := 4983230072969 + 3 ^ 40 * 222781 * 2
def baseEnd_222781 : Nat := 101683318835020535122627

theorem tailTrace_222781 : CollatzResearch.WordTrace tailWord_222781 prefixEnd_222781 101683318835020535122627 := by
  unfold tailWord_222781
  simp only [CollatzResearch.WordTrace]
  refine ⟨8125490605909959810756197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5416993737273306540504131 8125490605909959810756197)
  ·
    refine ⟨1523529488608117464516787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8125490605909959810756197 1523529488608117464516787)
    ·
      refine ⟨2285294232912176196775181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1523529488608117464516787 2285294232912176196775181)
      ·
        refine ⟨856985337342066073790693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2285294232912176196775181 856985337342066073790693)
        ·
          refine ⟨160684750751637388835755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 856985337342066073790693 160684750751637388835755)
          ·
            refine ⟨241027126127456083253633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160684750751637388835755 241027126127456083253633)
            ·
              refine ⟨180770344595592062440225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241027126127456083253633 180770344595592062440225)
              ·
                refine ⟨135577758446694046830169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180770344595592062440225 135577758446694046830169)
                ·
                  refine ⟨101683318835020535122627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135577758446694046830169 101683318835020535122627)
                  ·
                    rfl

theorem cell20_222781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_222781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222781 prefixEnd_222781 := by exact prefixLift 222781
  have htrace : WordTrace (prefixWord ++ tailWord_222781) baseStart_222781 baseEnd_222781 := by
    simpa [prefixWord, tailWord_222781, baseEnd_222781] using wordTrace_append hprefix tailTrace_222781
  have hstable : (prefixWord ++ tailWord_222781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222781).length < 2 ^ (prefixWord ++ tailWord_222781).sum := by decide
  have hdescent : baseEnd_222781 < baseStart_222781 := by decide
  rcases family_descends (prefixWord ++ tailWord_222781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222796 : List Nat := [2, 2, 1, 3, 1, 3, 3, 5]
def baseStart_222796 : Nat := 118140960795 + 222796 * 2 ^ 59
def prefixEnd_222796 : Nat := 4983230072969 + 3 ^ 40 * 222796 * 2
def baseEnd_222796 : Nat := 33896721747915716540855

theorem tailTrace_222796 : CollatzResearch.WordTrace tailWord_222796 prefixEnd_222796 33896721747915716540855 := by
  unfold tailWord_222796
  simp only [CollatzResearch.WordTrace]
  refine ⟨4063018850427808686276121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5417358467237078248368161 4063018850427808686276121)
  ·
    refine ⟨3047264137820856514707091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4063018850427808686276121 3047264137820856514707091)
    ·
      refine ⟨4570896206731284772060637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3047264137820856514707091 4570896206731284772060637)
      ·
        refine ⟨1714086077524231789522739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4570896206731284772060637 1714086077524231789522739)
        ·
          refine ⟨2571129116286347684284109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1714086077524231789522739 2571129116286347684284109)
          ·
            refine ⟨964173418607380381606541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2571129116286347684284109 964173418607380381606541)
            ·
              refine ⟨361565031977767643102453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 964173418607380381606541 361565031977767643102453)
              ·
                refine ⟨33896721747915716540855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 361565031977767643102453 33896721747915716540855)
                ·
                  rfl

theorem cell20_222796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_222796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222796 prefixEnd_222796 := by exact prefixLift 222796
  have htrace : WordTrace (prefixWord ++ tailWord_222796) baseStart_222796 baseEnd_222796 := by
    simpa [prefixWord, tailWord_222796, baseEnd_222796] using wordTrace_append hprefix tailTrace_222796
  have hstable : (prefixWord ++ tailWord_222796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222796).length < 2 ^ (prefixWord ++ tailWord_222796).sum := by decide
  have hdescent : baseEnd_222796 < baseStart_222796 := by decide
  rcases family_descends (prefixWord ++ tailWord_222796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222834 : List Nat := [3, 2, 1, 2, 3, 2, 7]
def baseStart_222834 : Nat := 118140960795 + 222834 * 2 ^ 59
def prefixEnd_222834 : Nat := 4983230072969 + 3 ^ 40 * 222834 * 2
def baseEnd_222834 : Nat := 11300834386576434039527

theorem tailTrace_222834 : CollatzResearch.WordTrace tailWord_222834 prefixEnd_222834 11300834386576434039527 := by
  unfold tailWord_222834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2031855918679487465608889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5418282449811966574957037 2031855918679487465608889)
  ·
    refine ⟨1523891939009615599206667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2031855918679487465608889 1523891939009615599206667)
    ·
      refine ⟨2285837908514423398810001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1523891939009615599206667 2285837908514423398810001)
      ·
        refine ⟨1714378431385817549107501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2285837908514423398810001 1714378431385817549107501)
        ·
          refine ⟨642891911769681580915313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1714378431385817549107501 642891911769681580915313)
          ·
            refine ⟨482168933827261185686485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 642891911769681580915313 482168933827261185686485)
            ·
              refine ⟨11300834386576434039527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 482168933827261185686485 11300834386576434039527)
              ·
                rfl

theorem cell20_222834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 7].length) (baseStart_222834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222834 prefixEnd_222834 := by exact prefixLift 222834
  have htrace : WordTrace (prefixWord ++ tailWord_222834) baseStart_222834 baseEnd_222834 := by
    simpa [prefixWord, tailWord_222834, baseEnd_222834] using wordTrace_append hprefix tailTrace_222834
  have hstable : (prefixWord ++ tailWord_222834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222834).length < 2 ^ (prefixWord ++ tailWord_222834).sum := by decide
  have hdescent : baseEnd_222834 < baseStart_222834 := by decide
  rcases family_descends (prefixWord ++ tailWord_222834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222837 : List Nat := [1, 3, 4, 2, 1, 1, 3, 2, 3]
def baseStart_222837 : Nat := 118140960795 + 222837 * 2 ^ 59
def prefixEnd_222837 : Nat := 4983230072969 + 3 ^ 40 * 222837 * 2
def baseEnd_222837 : Nat := 101708878760933229255731

theorem tailTrace_222837 : CollatzResearch.WordTrace tailWord_222837 prefixEnd_222837 101708878760933229255731 := by
  unfold tailWord_222837
  simp only [CollatzResearch.WordTrace]
  refine ⟨8127533093707081374794765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5418355395804720916529843 8127533093707081374794765)
  ·
    refine ⟨3047824910140155515548037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8127533093707081374794765 3047824910140155515548037)
    ·
      refine ⟨571467170651279159165257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3047824910140155515548037 571467170651279159165257)
      ·
        refine ⟨428600377988459369373943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 571467170651279159165257 428600377988459369373943)
        ·
          refine ⟨642900566982689054060915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 428600377988459369373943 642900566982689054060915)
          ·
            refine ⟨964350850474033581091373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 642900566982689054060915 964350850474033581091373)
            ·
              refine ⟨361631568927762592909265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 964350850474033581091373 361631568927762592909265)
              ·
                refine ⟨271223676695821944681949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 361631568927762592909265 271223676695821944681949)
                ·
                  refine ⟨101708878760933229255731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271223676695821944681949 101708878760933229255731)
                  ·
                    rfl

theorem cell20_222837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_222837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222837 prefixEnd_222837 := by exact prefixLift 222837
  have htrace : WordTrace (prefixWord ++ tailWord_222837) baseStart_222837 baseEnd_222837 := by
    simpa [prefixWord, tailWord_222837, baseEnd_222837] using wordTrace_append hprefix tailTrace_222837
  have hstable : (prefixWord ++ tailWord_222837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222837).length < 2 ^ (prefixWord ++ tailWord_222837).sum := by decide
  have hdescent : baseEnd_222837 < baseStart_222837 := by decide
  rcases family_descends (prefixWord ++ tailWord_222837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222841 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 5]
def baseStart_222841 : Nat := 118140960795 + 222841 * 2 ^ 59
def prefixEnd_222841 : Nat := 4983230072969 + 3 ^ 40 * 222841 * 2
def baseEnd_222841 : Nat := 101710704469926993122381

theorem tailTrace_222841 : CollatzResearch.WordTrace tailWord_222841 prefixEnd_222841 101710704469926993122381 := by
  unfold tailWord_222841
  simp only [CollatzResearch.WordTrace]
  refine ⟨8127678985692590057940377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5418452657128393371960251 8127678985692590057940377)
  ·
    refine ⟨6095759239269442543455283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8127678985692590057940377 6095759239269442543455283)
    ·
      refine ⟨9143638858904163815182925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6095759239269442543455283 9143638858904163815182925)
      ·
        refine ⟨3428864572089061430693597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9143638858904163815182925 3428864572089061430693597)
        ·
          refine ⟨1285824214533398036510099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3428864572089061430693597 1285824214533398036510099)
          ·
            refine ⟨1928736321800097054765149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1285824214533398036510099 1928736321800097054765149)
            ·
              refine ⟨723276120675036395536931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1928736321800097054765149 723276120675036395536931)
              ·
                refine ⟨1084914181012554593305397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723276120675036395536931 1084914181012554593305397)
                ·
                  refine ⟨101710704469926993122381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1084914181012554593305397 101710704469926993122381)
                  ·
                    rfl

theorem cell20_222841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_222841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222841 prefixEnd_222841 := by exact prefixLift 222841
  have htrace : WordTrace (prefixWord ++ tailWord_222841) baseStart_222841 baseEnd_222841 := by
    simpa [prefixWord, tailWord_222841, baseEnd_222841] using wordTrace_append hprefix tailTrace_222841
  have hstable : (prefixWord ++ tailWord_222841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222841).length < 2 ^ (prefixWord ++ tailWord_222841).sum := by decide
  have hdescent : baseEnd_222841 < baseStart_222841 := by decide
  rcases family_descends (prefixWord ++ tailWord_222841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222872 : List Nat := [2, 1, 2, 4, 1, 3, 1, 6]
def baseStart_222872 : Nat := 118140960795 + 222872 * 2 ^ 59
def prefixEnd_222872 : Nat := 4983230072969 + 3 ^ 40 * 222872 * 2
def baseEnd_222872 : Nat := 33908284571542887696307

theorem tailTrace_222872 : CollatzResearch.WordTrace tailWord_222872 prefixEnd_222872 33908284571542887696307 := by
  unfold tailWord_222872
  simp only [CollatzResearch.WordTrace]
  refine ⟨4064404824290141176159435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5419206432386854901545913 4064404824290141176159435)
  ·
    refine ⟨6096607236435211764239153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4064404824290141176159435 6096607236435211764239153)
    ·
      refine ⟨4572455427326408823179365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6096607236435211764239153 4572455427326408823179365)
      ·
        refine ⟨857335392623701654346131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4572455427326408823179365 857335392623701654346131)
        ·
          refine ⟨1286003088935552481519197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857335392623701654346131 1286003088935552481519197)
          ·
            refine ⟨482251158350832180569699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1286003088935552481519197 482251158350832180569699)
            ·
              refine ⟨723376737526248270854549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482251158350832180569699 723376737526248270854549)
              ·
                refine ⟨33908284571542887696307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 723376737526248270854549 33908284571542887696307)
                ·
                  rfl

theorem cell20_222872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_222872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222872 prefixEnd_222872 := by exact prefixLift 222872
  have htrace : WordTrace (prefixWord ++ tailWord_222872) baseStart_222872 baseEnd_222872 := by
    simpa [prefixWord, tailWord_222872, baseEnd_222872] using wordTrace_append hprefix tailTrace_222872
  have hstable : (prefixWord ++ tailWord_222872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222872).length < 2 ^ (prefixWord ++ tailWord_222872).sum := by decide
  have hdescent : baseEnd_222872 < baseStart_222872 := by decide
  rcases family_descends (prefixWord ++ tailWord_222872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222878 : List Nat := [4, 3, 1, 1, 1, 4, 1, 3, 2]
def baseStart_222878 : Nat := 118140960795 + 222878 * 2 ^ 59
def prefixEnd_222878 : Nat := 4983230072969 + 3 ^ 40 * 222878 * 2
def baseEnd_222878 : Nat := 101727592278119308888897

theorem tailTrace_222878 : CollatzResearch.WordTrace tailWord_222878 prefixEnd_222878 101727592278119308888897 := by
  unfold tailWord_222878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1016128560819818172129661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5419352324372363584691525 1016128560819818172129661)
  ·
    refine ⟨381048210307431814548623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1016128560819818172129661 381048210307431814548623)
    ·
      refine ⟨571572315461147721822935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381048210307431814548623 571572315461147721822935)
      ·
        refine ⟨857358473191721582734403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 571572315461147721822935 857358473191721582734403)
        ·
          refine ⟨1286037709787582374101605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 857358473191721582734403 1286037709787582374101605)
          ·
            refine ⟨241132070585171695144051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1286037709787582374101605 241132070585171695144051)
            ·
              refine ⟨361698105877757542716077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241132070585171695144051 361698105877757542716077)
              ·
                refine ⟨135636789704159078518529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 361698105877757542716077 135636789704159078518529)
                ·
                  refine ⟨101727592278119308888897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135636789704159078518529 101727592278119308888897)
                  ·
                    rfl

theorem cell20_222878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_222878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222878 prefixEnd_222878 := by exact prefixLift 222878
  have htrace : WordTrace (prefixWord ++ tailWord_222878) baseStart_222878 baseEnd_222878 := by
    simpa [prefixWord, tailWord_222878, baseEnd_222878] using wordTrace_append hprefix tailTrace_222878
  have hstable : (prefixWord ++ tailWord_222878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222878).length < 2 ^ (prefixWord ++ tailWord_222878).sum := by decide
  have hdescent : baseEnd_222878 < baseStart_222878 := by decide
  rcases family_descends (prefixWord ++ tailWord_222878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222903 : List Nat := [1, 1, 3, 1, 5, 1, 3, 1, 4]
def baseStart_222903 : Nat := 118140960795 + 222903 * 2 ^ 59
def prefixEnd_222903 : Nat := 4983230072969 + 3 ^ 40 * 222903 * 2
def baseEnd_222903 : Nat := 101739002959330333055461

theorem tailTrace_222903 : CollatzResearch.WordTrace tailWord_222903 prefixEnd_222903 101739002959330333055461 := by
  unfold tailWord_222903
  simp only [CollatzResearch.WordTrace]
  refine ⟨8129940311467974646697363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5419960207645316431131575 8129940311467974646697363)
  ·
    refine ⟨12194910467201961970046045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8129940311467974646697363 12194910467201961970046045)
    ·
      refine ⟨4573091425200735738767267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12194910467201961970046045 4573091425200735738767267)
      ·
        refine ⟨6859637137801103608150901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4573091425200735738767267 6859637137801103608150901)
        ·
          refine ⟨643090981668853463264147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6859637137801103608150901 643090981668853463264147)
          ·
            refine ⟨964636472503280194896221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 643090981668853463264147 964636472503280194896221)
            ·
              refine ⟨361738677188730073086083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 964636472503280194896221 361738677188730073086083)
              ·
                refine ⟨542608015783095109629125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 361738677188730073086083 542608015783095109629125)
                ·
                  refine ⟨101739002959330333055461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 542608015783095109629125 101739002959330333055461)
                  ·
                    rfl

theorem cell20_222903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 4].length) (baseStart_222903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222903 prefixEnd_222903 := by exact prefixLift 222903
  have htrace : WordTrace (prefixWord ++ tailWord_222903) baseStart_222903 baseEnd_222903 := by
    simpa [prefixWord, tailWord_222903, baseEnd_222903] using wordTrace_append hprefix tailTrace_222903
  have hstable : (prefixWord ++ tailWord_222903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222903).length < 2 ^ (prefixWord ++ tailWord_222903).sum := by decide
  have hdescent : baseEnd_222903 < baseStart_222903 := by decide
  rcases family_descends (prefixWord ++ tailWord_222903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222910 : List Nat := [4, 2, 1, 1, 2, 2, 1, 7]
def baseStart_222910 : Nat := 118140960795 + 222910 * 2 ^ 59
def prefixEnd_222910 : Nat := 4983230072969 + 3 ^ 40 * 222910 * 2
def baseEnd_222910 : Nat := 33914065983356473274033

theorem tailTrace_222910 : CollatzResearch.WordTrace tailWord_222910 prefixEnd_222910 33914065983356473274033 := by
  unfold tailWord_222910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1016274452805326855275273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5420130414961743228134789 1016274452805326855275273)
  ·
    refine ⟨762205839603995141456455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1016274452805326855275273 762205839603995141456455)
    ·
      refine ⟨1143308759405992712184683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 762205839603995141456455 1143308759405992712184683)
      ·
        refine ⟨1714963139108989068277025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1143308759405992712184683 1714963139108989068277025)
        ·
          refine ⟨1286222354331741801207769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1714963139108989068277025 1286222354331741801207769)
          ·
            refine ⟨964666765748806350905827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1286222354331741801207769 964666765748806350905827)
            ·
              refine ⟨1447000148623209526358741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 964666765748806350905827 1447000148623209526358741)
              ·
                refine ⟨33914065983356473274033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1447000148623209526358741 33914065983356473274033)
                ·
                  rfl

theorem cell20_222910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_222910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222910 prefixEnd_222910 := by exact prefixLift 222910
  have htrace : WordTrace (prefixWord ++ tailWord_222910) baseStart_222910 baseEnd_222910 := by
    simpa [prefixWord, tailWord_222910, baseEnd_222910] using wordTrace_append hprefix tailTrace_222910
  have hstable : (prefixWord ++ tailWord_222910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222910).length < 2 ^ (prefixWord ++ tailWord_222910).sum := by decide
  have hdescent : baseEnd_222910 < baseStart_222910 := by decide
  rcases family_descends (prefixWord ++ tailWord_222910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222917 : List Nat := [1, 3, 1, 1, 1, 1, 2, 7, 3]
def baseStart_222917 : Nat := 118140960795 + 222917 * 2 ^ 59
def prefixEnd_222917 : Nat := 4983230072969 + 3 ^ 40 * 222917 * 2
def baseEnd_222917 : Nat := 101745392940808506588737

theorem tailTrace_222917 : CollatzResearch.WordTrace tailWord_222917 prefixEnd_222917 101745392940808506588737 := by
  unfold tailWord_222917
  simp only [CollatzResearch.WordTrace]
  refine ⟨8130450933417255037707005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5420300622278170025138003 8130450933417255037707005)
  ·
    refine ⟨3048919100031470639140127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8130450933417255037707005 3048919100031470639140127)
    ·
      refine ⟨4573378650047205958710191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3048919100031470639140127 4573378650047205958710191)
      ·
        refine ⟨6860067975070808938065287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4573378650047205958710191 6860067975070808938065287)
        ·
          refine ⟨10290101962606213407097931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6860067975070808938065287 10290101962606213407097931)
          ·
            refine ⟨15435152943909320110646897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10290101962606213407097931 15435152943909320110646897)
            ·
              refine ⟨11576364707931990082985173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15435152943909320110646897 11576364707931990082985173)
              ·
                refine ⟨271321047842156017569965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11576364707931990082985173 271321047842156017569965)
                ·
                  refine ⟨101745392940808506588737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271321047842156017569965 101745392940808506588737)
                  ·
                    rfl

theorem cell20_222917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_222917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222917 prefixEnd_222917 := by exact prefixLift 222917
  have htrace : WordTrace (prefixWord ++ tailWord_222917) baseStart_222917 baseEnd_222917 := by
    simpa [prefixWord, tailWord_222917, baseEnd_222917] using wordTrace_append hprefix tailTrace_222917
  have hstable : (prefixWord ++ tailWord_222917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222917).length < 2 ^ (prefixWord ++ tailWord_222917).sum := by decide
  have hdescent : baseEnd_222917 < baseStart_222917 := by decide
  rcases family_descends (prefixWord ++ tailWord_222917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222955 : List Nat := [1, 1, 1, 1, 2, 4, 3, 4, 3]
def baseStart_222955 : Nat := 118140960795 + 222955 * 2 ^ 59
def prefixEnd_222955 : Nat := 4983230072969 + 3 ^ 40 * 222955 * 2
def baseEnd_222955 : Nat := 101762737176249263321915

theorem tailTrace_222955 : CollatzResearch.WordTrace tailWord_222955 prefixEnd_222955 101762737176249263321915 := by
  unfold tailWord_222955
  simp only [CollatzResearch.WordTrace]
  refine ⟨8131836907279587527590319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5421224604853058351726879 8131836907279587527590319)
  ·
    refine ⟨12197755360919381291385479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8131836907279587527590319 12197755360919381291385479)
    ·
      refine ⟨18296633041379071937078219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12197755360919381291385479 18296633041379071937078219)
      ·
        refine ⟨27444949562068607905617329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18296633041379071937078219 27444949562068607905617329)
        ·
          refine ⟨20583712171551455929212997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27444949562068607905617329 20583712171551455929212997)
          ·
            refine ⟨3859446032165897986727437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20583712171551455929212997 3859446032165897986727437)
            ·
              refine ⟨1447292262062211745022789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3859446032165897986727437 1447292262062211745022789)
              ·
                refine ⟨271367299136664702191773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1447292262062211745022789 271367299136664702191773)
                ·
                  refine ⟨101762737176249263321915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271367299136664702191773 101762737176249263321915)
                  ·
                    rfl

theorem cell20_222955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 3].length) (baseStart_222955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222955 prefixEnd_222955 := by exact prefixLift 222955
  have htrace : WordTrace (prefixWord ++ tailWord_222955) baseStart_222955 baseEnd_222955 := by
    simpa [prefixWord, tailWord_222955, baseEnd_222955] using wordTrace_append hprefix tailTrace_222955
  have hstable : (prefixWord ++ tailWord_222955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222955).length < 2 ^ (prefixWord ++ tailWord_222955).sum := by decide
  have hdescent : baseEnd_222955 < baseStart_222955 := by decide
  rcases family_descends (prefixWord ++ tailWord_222955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_222958 : List Nat := [4, 1, 2, 1, 1, 2, 3, 4, 2]
def baseStart_222958 : Nat := 118140960795 + 222958 * 2 ^ 59
def prefixEnd_222958 : Nat := 4983230072969 + 3 ^ 40 * 222958 * 2
def baseEnd_222958 : Nat := 101764106457994586221903

theorem tailTrace_222958 : CollatzResearch.WordTrace tailWord_222958 prefixEnd_222958 101764106457994586221903 := by
  unfold tailWord_222958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1016493290783589879993691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5421297550845812693299685 1016493290783589879993691)
  ·
    refine ⟨1524739936175384819990537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1016493290783589879993691 1524739936175384819990537)
    ·
      refine ⟨1143554952131538614992903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1524739936175384819990537 1143554952131538614992903)
      ·
        refine ⟨1715332428197307922489355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1143554952131538614992903 1715332428197307922489355)
        ·
          refine ⟨2572998642295961883734033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1715332428197307922489355 2572998642295961883734033)
          ·
            refine ⟨1929748981721971412800525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2572998642295961883734033 1929748981721971412800525)
            ·
              refine ⟨723655868145739279800197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1929748981721971412800525 723655868145739279800197)
              ·
                refine ⟨135685475277326114962537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 723655868145739279800197 135685475277326114962537)
                ·
                  refine ⟨101764106457994586221903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135685475277326114962537 101764106457994586221903)
                  ·
                    rfl

theorem cell20_222958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_222958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_222958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_222958 prefixEnd_222958 := by exact prefixLift 222958
  have htrace : WordTrace (prefixWord ++ tailWord_222958) baseStart_222958 baseEnd_222958 := by
    simpa [prefixWord, tailWord_222958, baseEnd_222958] using wordTrace_append hprefix tailTrace_222958
  have hstable : (prefixWord ++ tailWord_222958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_222958).length < 2 ^ (prefixWord ++ tailWord_222958).sum := by decide
  have hdescent : baseEnd_222958 < baseStart_222958 := by decide
  rcases family_descends (prefixWord ++ tailWord_222958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223006 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_223006 : Nat := 118140960795 + 223006 * 2 ^ 59
def prefixEnd_223006 : Nat := 4983230072969 + 3 ^ 40 * 223006 * 2
def baseEnd_223006 : Nat := 101786014965919752621707

theorem tailTrace_223006 : CollatzResearch.WordTrace tailWord_223006 prefixEnd_223006 101786014965919752621707 := by
  unfold tailWord_223006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1016712128761852904712109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5422464686729882158464581 1016712128761852904712109)
  ·
    refine ⟨381267048285694839267041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1016712128761852904712109 381267048285694839267041)
    ·
      refine ⟨285950286214271129450281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 381267048285694839267041 285950286214271129450281)
      ·
        refine ⟨214462714660703347087711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285950286214271129450281 214462714660703347087711)
        ·
          refine ⟨321694071991055020631567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214462714660703347087711 321694071991055020631567)
          ·
            refine ⟨482541107986582530947351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321694071991055020631567 482541107986582530947351)
            ·
              refine ⟨723811661979873796421027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482541107986582530947351 723811661979873796421027)
              ·
                refine ⟨1085717492969810694631541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 723811661979873796421027 1085717492969810694631541)
                ·
                  refine ⟨101786014965919752621707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1085717492969810694631541 101786014965919752621707)
                  ·
                    rfl

theorem cell20_223006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_223006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223006 prefixEnd_223006 := by exact prefixLift 223006
  have htrace : WordTrace (prefixWord ++ tailWord_223006) baseStart_223006 baseEnd_223006 := by
    simpa [prefixWord, tailWord_223006, baseEnd_223006] using wordTrace_append hprefix tailTrace_223006
  have hstable : (prefixWord ++ tailWord_223006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223006).length < 2 ^ (prefixWord ++ tailWord_223006).sum := by decide
  have hdescent : baseEnd_223006 < baseStart_223006 := by decide
  rcases family_descends (prefixWord ++ tailWord_223006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223007 : List Nat := [1, 1, 2, 4, 2, 1, 9]
def baseStart_223007 : Nat := 118140960795 + 223007 * 2 ^ 59
def prefixEnd_223007 : Nat := 4983230072969 + 3 ^ 40 * 223007 * 2
def baseEnd_223007 : Nat := 11309607932574243732041

theorem tailTrace_223007 : CollatzResearch.WordTrace tailWord_223007 prefixEnd_223007 11309607932574243732041 := by
  unfold tailWord_223007
  simp only [CollatzResearch.WordTrace]
  refine ⟨8133733503091200408483275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5422489002060800272322183 8133733503091200408483275)
  ·
    refine ⟨12200600254636800612724913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8133733503091200408483275 12200600254636800612724913)
    ·
      refine ⟨9150450190977600459543685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12200600254636800612724913 9150450190977600459543685)
      ·
        refine ⟨1715709410808300086164441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9150450190977600459543685 1715709410808300086164441)
        ·
          refine ⟨1286782058106225064623331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1715709410808300086164441 1286782058106225064623331)
          ·
            refine ⟨1930173087159337596934997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1286782058106225064623331 1930173087159337596934997)
            ·
              refine ⟨11309607932574243732041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1930173087159337596934997 11309607932574243732041)
              ·
                rfl

theorem cell20_223007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 9].length) (baseStart_223007 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223007 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223007 prefixEnd_223007 := by exact prefixLift 223007
  have htrace : WordTrace (prefixWord ++ tailWord_223007) baseStart_223007 baseEnd_223007 := by
    simpa [prefixWord, tailWord_223007, baseEnd_223007] using wordTrace_append hprefix tailTrace_223007
  have hstable : (prefixWord ++ tailWord_223007).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223007).length < 2 ^ (prefixWord ++ tailWord_223007).sum := by decide
  have hdescent : baseEnd_223007 < baseStart_223007 := by decide
  rcases family_descends (prefixWord ++ tailWord_223007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223027 : List Nat := [1, 1, 1, 2, 7, 1, 3, 1, 3]
def baseStart_223027 : Nat := 118140960795 + 223027 * 2 ^ 59
def prefixEnd_223027 : Nat := 4983230072969 + 3 ^ 40 * 223027 * 2
def baseEnd_223027 : Nat := 101795599938137012921621

theorem tailTrace_223027 : CollatzResearch.WordTrace tailWord_223027 prefixEnd_223027 101795599938137012921621 := by
  unfold tailWord_223027
  simp only [CollatzResearch.WordTrace]
  refine ⟨8134462963018743824211335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5422975308679162549474223 8134462963018743824211335)
  ·
    refine ⟨12201694444528115736317003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8134462963018743824211335 12201694444528115736317003)
    ·
      refine ⟨18302541666792173604475505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12201694444528115736317003 18302541666792173604475505)
      ·
        refine ⟨13726906250094130203356629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18302541666792173604475505 13726906250094130203356629)
        ·
          refine ⟨321724365236581176641171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 13726906250094130203356629 321724365236581176641171)
          ·
            refine ⟨482586547854871764961757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321724365236581176641171 482586547854871764961757)
            ·
              refine ⟨180969955445576911860659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 482586547854871764961757 180969955445576911860659)
              ·
                refine ⟨271454933168365367790989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180969955445576911860659 271454933168365367790989)
                ·
                  refine ⟨101795599938137012921621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271454933168365367790989 101795599938137012921621)
                  ·
                    rfl

theorem cell20_223027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 3].length) (baseStart_223027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223027 prefixEnd_223027 := by exact prefixLift 223027
  have htrace : WordTrace (prefixWord ++ tailWord_223027) baseStart_223027 baseEnd_223027 := by
    simpa [prefixWord, tailWord_223027, baseEnd_223027] using wordTrace_append hprefix tailTrace_223027
  have hstable : (prefixWord ++ tailWord_223027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223027).length < 2 ^ (prefixWord ++ tailWord_223027).sum := by decide
  have hdescent : baseEnd_223027 < baseStart_223027 := by decide
  rcases family_descends (prefixWord ++ tailWord_223027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223045 : List Nat := [1, 3, 1, 1, 1, 2, 5, 6]
def baseStart_223045 : Nat := 118140960795 + 223045 * 2 ^ 59
def prefixEnd_223045 : Nat := 4983230072969 + 3 ^ 40 * 223045 * 2
def baseEnd_223045 : Nat := 33934605209536316773849

theorem tailTrace_223045 : CollatzResearch.WordTrace tailWord_223045 prefixEnd_223045 33934605209536316773849 := by
  unfold tailWord_223045
  simp only [CollatzResearch.WordTrace]
  refine ⟨8135119476953532898366589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5423412984635688598911059 8135119476953532898366589)
  ·
    refine ⟨3050669803857574836887471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8135119476953532898366589 3050669803857574836887471)
    ·
      refine ⟨4576004705786362255331207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3050669803857574836887471 4576004705786362255331207)
      ·
        refine ⟨6864007058679543382996811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4576004705786362255331207 6864007058679543382996811)
        ·
          refine ⟨10296010588019315074495217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6864007058679543382996811 10296010588019315074495217)
          ·
            refine ⟨7722007941014486305871413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10296010588019315074495217 7722007941014486305871413)
            ·
              refine ⟨723938244470108091175445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7722007941014486305871413 723938244470108091175445)
              ·
                refine ⟨33934605209536316773849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 723938244470108091175445 33934605209536316773849)
                ·
                  rfl

theorem cell20_223045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 6].length) (baseStart_223045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223045 prefixEnd_223045 := by exact prefixLift 223045
  have htrace : WordTrace (prefixWord ++ tailWord_223045) baseStart_223045 baseEnd_223045 := by
    simpa [prefixWord, tailWord_223045, baseEnd_223045] using wordTrace_append hprefix tailTrace_223045
  have hstable : (prefixWord ++ tailWord_223045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223045).length < 2 ^ (prefixWord ++ tailWord_223045).sum := by decide
  have hdescent : baseEnd_223045 < baseStart_223045 := by decide
  rcases family_descends (prefixWord ++ tailWord_223045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223068 : List Nat := [2, 2, 4, 2, 2, 1, 3, 2, 2]
def baseStart_223068 : Nat := 118140960795 + 223068 * 2 ^ 59
def prefixEnd_223068 : Nat := 4983230072969 + 3 ^ 40 * 223068 * 2
def baseEnd_223068 : Nat := 101814313455323092554787

theorem tailTrace_223068 : CollatzResearch.WordTrace tailWord_223068 prefixEnd_223068 101814313455323092554787 := by
  unfold tailWord_223068
  simp only [CollatzResearch.WordTrace]
  refine ⟨4067979177935103913226929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5423972237246805217635905 4067979177935103913226929)
  ·
    refine ⟨3050984383451327934920197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4067979177935103913226929 3050984383451327934920197)
    ·
      refine ⟨572059571897123987797537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3050984383451327934920197 572059571897123987797537)
      ·
        refine ⟨429044678922842990848153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 572059571897123987797537 429044678922842990848153)
        ·
          refine ⟨321783509192132243136115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429044678922842990848153 321783509192132243136115)
          ·
            refine ⟨482675263788198364704173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321783509192132243136115 482675263788198364704173)
            ·
              refine ⟨181003223920574386764065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 482675263788198364704173 181003223920574386764065)
              ·
                refine ⟨135752417940430790073049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181003223920574386764065 135752417940430790073049)
                ·
                  refine ⟨101814313455323092554787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135752417940430790073049 101814313455323092554787)
                  ·
                    rfl

theorem cell20_223068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_223068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223068 prefixEnd_223068 := by exact prefixLift 223068
  have htrace : WordTrace (prefixWord ++ tailWord_223068) baseStart_223068 baseEnd_223068 := by
    simpa [prefixWord, tailWord_223068, baseEnd_223068] using wordTrace_append hprefix tailTrace_223068
  have hstable : (prefixWord ++ tailWord_223068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223068).length < 2 ^ (prefixWord ++ tailWord_223068).sum := by decide
  have hdescent : baseEnd_223068 < baseStart_223068 := by decide
  rcases family_descends (prefixWord ++ tailWord_223068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223124 : List Nat := [2, 4, 2, 1, 1, 2, 1, 4, 3]
def baseStart_223124 : Nat := 118140960795 + 223124 * 2 ^ 59
def prefixEnd_223124 : Nat := 4983230072969 + 3 ^ 40 * 223124 * 2
def baseEnd_223124 : Nat := 101839873381235786687891

theorem tailTrace_223124 : CollatzResearch.WordTrace tailWord_223124 prefixEnd_223124 101839873381235786687891 := by
  unfold tailWord_223124
  simp only [CollatzResearch.WordTrace]
  refine ⟨4069000421833664695246213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5425333895778219593661617 4069000421833664695246213)
  ·
    refine ⟨762937579093812130358665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4069000421833664695246213 762937579093812130358665)
    ·
      refine ⟨572203184320359097768999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 762937579093812130358665 572203184320359097768999)
      ·
        refine ⟨858304776480538646653499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572203184320359097768999 858304776480538646653499)
        ·
          refine ⟨1287457164720807969980249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 858304776480538646653499 1287457164720807969980249)
          ·
            refine ⟨965592873540605977485187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1287457164720807969980249 965592873540605977485187)
            ·
              refine ⟨1448389310310908966227781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 965592873540605977485187 1448389310310908966227781)
              ·
                refine ⟨271572995683295431167709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1448389310310908966227781 271572995683295431167709)
                ·
                  refine ⟨101839873381235786687891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271572995683295431167709 101839873381235786687891)
                  ·
                    rfl

theorem cell20_223124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_223124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223124 prefixEnd_223124 := by exact prefixLift 223124
  have htrace : WordTrace (prefixWord ++ tailWord_223124) baseStart_223124 baseEnd_223124 := by
    simpa [prefixWord, tailWord_223124, baseEnd_223124] using wordTrace_append hprefix tailTrace_223124
  have hstable : (prefixWord ++ tailWord_223124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223124).length < 2 ^ (prefixWord ++ tailWord_223124).sum := by decide
  have hdescent : baseEnd_223124 < baseStart_223124 := by decide
  rcases family_descends (prefixWord ++ tailWord_223124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223127 : List Nat := [1, 1, 3, 3, 1, 5, 2, 2, 2]
def baseStart_223127 : Nat := 118140960795 + 223127 * 2 ^ 59
def prefixEnd_223127 : Nat := 4983230072969 + 3 ^ 40 * 223127 * 2
def baseEnd_223127 : Nat := 101841242662981109587879

theorem tailTrace_223127 : CollatzResearch.WordTrace tailWord_223127 prefixEnd_223127 101841242662981109587879 := by
  unfold tailWord_223127
  simp only [CollatzResearch.WordTrace]
  refine ⟨8138110262656460902851635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5425406841770973935234423 8138110262656460902851635)
  ·
    refine ⟨12207165393984691354277453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8138110262656460902851635 12207165393984691354277453)
    ·
      refine ⟨4577687022744259257854045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12207165393984691354277453 4577687022744259257854045)
      ·
        refine ⟨1716632633529097221695267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4577687022744259257854045 1716632633529097221695267)
        ·
          refine ⟨2574948950293645832542901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1716632633529097221695267 2574948950293645832542901)
          ·
            refine ⟨241401464090029296800897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2574948950293645832542901 241401464090029296800897)
            ·
              refine ⟨181051098067521972600673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241401464090029296800897 181051098067521972600673)
              ·
                refine ⟨135788323550641479450505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181051098067521972600673 135788323550641479450505)
                ·
                  refine ⟨101841242662981109587879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135788323550641479450505 101841242662981109587879)
                  ·
                    rfl

theorem cell20_223127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 2].length) (baseStart_223127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223127 prefixEnd_223127 := by exact prefixLift 223127
  have htrace : WordTrace (prefixWord ++ tailWord_223127) baseStart_223127 baseEnd_223127 := by
    simpa [prefixWord, tailWord_223127, baseEnd_223127] using wordTrace_append hprefix tailTrace_223127
  have hstable : (prefixWord ++ tailWord_223127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223127).length < 2 ^ (prefixWord ++ tailWord_223127).sum := by decide
  have hdescent : baseEnd_223127 < baseStart_223127 := by decide
  rcases family_descends (prefixWord ++ tailWord_223127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223186 : List Nat := [3, 2, 2, 3, 2, 1, 2, 1, 4]
def baseStart_223186 : Nat := 118140960795 + 223186 * 2 ^ 59
def prefixEnd_223186 : Nat := 4983230072969 + 3 ^ 40 * 223186 * 2
def baseEnd_223186 : Nat := 101868171870639126620971

theorem tailTrace_223186 : CollatzResearch.WordTrace tailWord_223186 prefixEnd_223186 101868171870639126620971 := by
  unfold tailWord_223186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2035065542360678494812353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5426841446295142652832941 2035065542360678494812353)
  ·
    refine ⟨1526299156770508871109265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2035065542360678494812353 1526299156770508871109265)
    ·
      refine ⟨1144724367577881653331949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1526299156770508871109265 1144724367577881653331949)
      ·
        refine ⟨429271637841705619999481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1144724367577881653331949 429271637841705619999481)
        ·
          refine ⟨321953728381279214999611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 429271637841705619999481 321953728381279214999611)
          ·
            refine ⟨482930592571918822499417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 321953728381279214999611 482930592571918822499417)
            ·
              refine ⟨362197944428939116874563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 482930592571918822499417 362197944428939116874563)
              ·
                refine ⟨543296916643408675311845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362197944428939116874563 543296916643408675311845)
                ·
                  refine ⟨101868171870639126620971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 543296916643408675311845 101868171870639126620971)
                  ·
                    rfl

theorem cell20_223186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_223186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223186 prefixEnd_223186 := by exact prefixLift 223186
  have htrace : WordTrace (prefixWord ++ tailWord_223186) baseStart_223186 baseEnd_223186 := by
    simpa [prefixWord, tailWord_223186, baseEnd_223186] using wordTrace_append hprefix tailTrace_223186
  have hstable : (prefixWord ++ tailWord_223186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223186).length < 2 ^ (prefixWord ++ tailWord_223186).sum := by decide
  have hdescent : baseEnd_223186 < baseStart_223186 := by decide
  rcases family_descends (prefixWord ++ tailWord_223186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223214 : List Nat := [4, 1, 2, 1, 3, 2, 1, 6]
def baseStart_223214 : Nat := 118140960795 + 223214 * 2 ^ 59
def prefixEnd_223214 : Nat := 4983230072969 + 3 ^ 40 * 223214 * 2
def baseEnd_223214 : Nat := 33960317277865157895841

theorem tailTrace_223214 : CollatzResearch.WordTrace tailWord_223214 prefixEnd_223214 33960317277865157895841 := by
  unfold tailWord_223214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1017660426667659345158587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5427522275560849840845797 1017660426667659345158587)
  ·
    refine ⟨1526490640001489017737881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1017660426667659345158587 1526490640001489017737881)
    ·
      refine ⟨1144867980001116763303411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1526490640001489017737881 1144867980001116763303411)
      ·
        refine ⟨1717301970001675144955117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1144867980001116763303411 1717301970001675144955117)
        ·
          refine ⟨643988238750628179358169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1717301970001675144955117 643988238750628179358169)
          ·
            refine ⟨482991179062971134518627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 643988238750628179358169 482991179062971134518627)
            ·
              refine ⟨724486768594456701777941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 482991179062971134518627 724486768594456701777941)
              ·
                refine ⟨33960317277865157895841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 724486768594456701777941 33960317277865157895841)
                ·
                  rfl

theorem cell20_223214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_223214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223214 prefixEnd_223214 := by exact prefixLift 223214
  have htrace : WordTrace (prefixWord ++ tailWord_223214) baseStart_223214 baseEnd_223214 := by
    simpa [prefixWord, tailWord_223214, baseEnd_223214] using wordTrace_append hprefix tailTrace_223214
  have hstable : (prefixWord ++ tailWord_223214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223214).length < 2 ^ (prefixWord ++ tailWord_223214).sum := by decide
  have hdescent : baseEnd_223214 < baseStart_223214 := by decide
  rcases family_descends (prefixWord ++ tailWord_223214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223266 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_223266 : Nat := 118140960795 + 223266 * 2 ^ 59
def prefixEnd_223266 : Nat := 4983230072969 + 3 ^ 40 * 223266 * 2
def baseEnd_223266 : Nat := 101904686050514403953977

theorem tailTrace_223266 : CollatzResearch.WordTrace tailWord_223266 prefixEnd_223266 101904686050514403953977 := by
  unfold tailWord_223266
  simp only [CollatzResearch.WordTrace]
  refine ⟨2035795002288221910540413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5428786672768591761441101 2035795002288221910540413)
  ·
    refine ⟨763423125858083216452655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2035795002288221910540413 763423125858083216452655)
    ·
      refine ⟨1145134688787124824678983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 763423125858083216452655 1145134688787124824678983)
      ·
        refine ⟨1717702033180687237018475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1145134688787124824678983 1717702033180687237018475)
        ·
          refine ⟨2576553049771030855527713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1717702033180687237018475 2576553049771030855527713)
          ·
            refine ⟨1932414787328273141645785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2576553049771030855527713 1932414787328273141645785)
            ·
              refine ⟨1449311090496204856234339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1932414787328273141645785 1449311090496204856234339)
              ·
                refine ⟨2173966635744307284351509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1449311090496204856234339 2173966635744307284351509)
                ·
                  refine ⟨101904686050514403953977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2173966635744307284351509 101904686050514403953977)
                  ·
                    rfl

theorem cell20_223266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_223266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223266 prefixEnd_223266 := by exact prefixLift 223266
  have htrace : WordTrace (prefixWord ++ tailWord_223266) baseStart_223266 baseEnd_223266 := by
    simpa [prefixWord, tailWord_223266, baseEnd_223266] using wordTrace_append hprefix tailTrace_223266
  have hstable : (prefixWord ++ tailWord_223266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223266).length < 2 ^ (prefixWord ++ tailWord_223266).sum := by decide
  have hdescent : baseEnd_223266 < baseStart_223266 := by decide
  rcases family_descends (prefixWord ++ tailWord_223266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223328 : List Nat := [2, 1, 1, 3, 2, 4, 3, 4]
def baseStart_223328 : Nat := 118140960795 + 223328 * 2 ^ 59
def prefixEnd_223328 : Nat := 4983230072969 + 3 ^ 40 * 223328 * 2
def baseEnd_223328 : Nat := 33977661513305914629019

theorem tailTrace_223328 : CollatzResearch.WordTrace tailWord_223328 prefixEnd_223328 33977661513305914629019 := by
  unfold tailWord_223328
  simp only [CollatzResearch.WordTrace]
  refine ⟨4072720667464136115459319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5430294223285514820612425 4072720667464136115459319)
  ·
    refine ⟨6109081001196204173188979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4072720667464136115459319 6109081001196204173188979)
    ·
      refine ⟨9163621501794306259783469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6109081001196204173188979 9163621501794306259783469)
      ·
        refine ⟨3436358063172864847418801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9163621501794306259783469 3436358063172864847418801)
        ·
          refine ⟨2577268547379648635564101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3436358063172864847418801 2577268547379648635564101)
          ·
            refine ⟨483237852633684119168269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2577268547379648635564101 483237852633684119168269)
            ·
              refine ⟨181214194737631544688101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 483237852633684119168269 181214194737631544688101)
              ·
                refine ⟨33977661513305914629019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181214194737631544688101 33977661513305914629019)
                ·
                  rfl

theorem cell20_223328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_223328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223328 prefixEnd_223328 := by exact prefixLift 223328
  have htrace : WordTrace (prefixWord ++ tailWord_223328) baseStart_223328 baseEnd_223328 := by
    simpa [prefixWord, tailWord_223328, baseEnd_223328] using wordTrace_append hprefix tailTrace_223328
  have hstable : (prefixWord ++ tailWord_223328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223328).length < 2 ^ (prefixWord ++ tailWord_223328).sum := by decide
  have hdescent : baseEnd_223328 < baseStart_223328 := by decide
  rcases family_descends (prefixWord ++ tailWord_223328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223342 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_223342 : Nat := 118140960795 + 223342 * 2 ^ 59
def prefixEnd_223342 : Nat := 4983230072969 + 3 ^ 40 * 223342 * 2
def baseEnd_223342 : Nat := 101939374521395917420333

theorem tailTrace_223342 : CollatzResearch.WordTrace tailWord_223342 prefixEnd_223342 101939374521395917420333 := by
  unfold tailWord_223342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1018243994609694077741035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5430634637918368414618853 1018243994609694077741035)
  ·
    refine ⟨1527365991914541116611553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1018243994609694077741035 1527365991914541116611553)
    ·
      refine ⟨1145524493935905837458665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1527365991914541116611553 1145524493935905837458665)
      ·
        refine ⟨859143370451929378093999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1145524493935905837458665 859143370451929378093999)
        ·
          refine ⟨1288715055677894067140999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859143370451929378093999 1288715055677894067140999)
          ·
            refine ⟨1933072583516841100711499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1288715055677894067140999 1933072583516841100711499)
            ·
              refine ⟨2899608875275261651067249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1933072583516841100711499 2899608875275261651067249)
              ·
                refine ⟨2174706656456446238300437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2899608875275261651067249 2174706656456446238300437)
                ·
                  refine ⟨101939374521395917420333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2174706656456446238300437 101939374521395917420333)
                  ·
                    rfl

theorem cell20_223342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_223342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223342 prefixEnd_223342 := by exact prefixLift 223342
  have htrace : WordTrace (prefixWord ++ tailWord_223342) baseStart_223342 baseEnd_223342 := by
    simpa [prefixWord, tailWord_223342, baseEnd_223342] using wordTrace_append hprefix tailTrace_223342
  have hstable : (prefixWord ++ tailWord_223342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223342).length < 2 ^ (prefixWord ++ tailWord_223342).sum := by decide
  have hdescent : baseEnd_223342 < baseStart_223342 := by decide
  rcases family_descends (prefixWord ++ tailWord_223342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223383 : List Nat := [1, 1, 3, 3, 4, 2, 2, 4]
def baseStart_223383 : Nat := 118140960795 + 223383 * 2 ^ 59
def prefixEnd_223383 : Nat := 4983230072969 + 3 ^ 40 * 223383 * 2
def baseEnd_223383 : Nat := 33986029346193999017833

theorem tailTrace_223383 : CollatzResearch.WordTrace tailWord_223383 prefixEnd_223383 33986029346193999017833 := by
  unfold tailWord_223383
  simp only [CollatzResearch.WordTrace]
  refine ⟨8147447349729016624170803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5431631566486011082780535 8147447349729016624170803)
  ·
    refine ⟨12221171024593524936256205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8147447349729016624170803 12221171024593524936256205)
    ·
      refine ⟨4582939134222571851096077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12221171024593524936256205 4582939134222571851096077)
      ·
        refine ⟨1718602175333464444161029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4582939134222571851096077 1718602175333464444161029)
        ·
          refine ⟨322237907875024583280193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1718602175333464444161029 322237907875024583280193)
          ·
            refine ⟨241678430906268437460145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322237907875024583280193 241678430906268437460145)
            ·
              refine ⟨181258823179701328095109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241678430906268437460145 181258823179701328095109)
              ·
                refine ⟨33986029346193999017833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181258823179701328095109 33986029346193999017833)
                ·
                  rfl

theorem cell20_223383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 4].length) (baseStart_223383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223383 prefixEnd_223383 := by exact prefixLift 223383
  have htrace : WordTrace (prefixWord ++ tailWord_223383) baseStart_223383 baseEnd_223383 := by
    simpa [prefixWord, tailWord_223383, baseEnd_223383] using wordTrace_append hprefix tailTrace_223383
  have hstable : (prefixWord ++ tailWord_223383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223383).length < 2 ^ (prefixWord ++ tailWord_223383).sum := by decide
  have hdescent : baseEnd_223383 < baseStart_223383 := by decide
  rcases family_descends (prefixWord ++ tailWord_223383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223418 : List Nat := [3, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_223418 : Nat := 118140960795 + 223418 * 2 ^ 59
def prefixEnd_223418 : Nat := 4983230072969 + 3 ^ 40 * 223418 * 2
def baseEnd_223418 : Nat := 101974062992277430886689

theorem tailTrace_223418 : CollatzResearch.WordTrace tailWord_223418 prefixEnd_223418 101974062992277430886689 := by
  unfold tailWord_223418
  simp only [CollatzResearch.WordTrace]
  refine ⟨2037180976150554400423727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5432482603068145067796605 2037180976150554400423727)
  ·
    refine ⟨3055771464225831600635591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2037180976150554400423727 3055771464225831600635591)
    ·
      refine ⟨4583657196338747400953387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3055771464225831600635591 4583657196338747400953387)
      ·
        refine ⟨6875485794508121101430081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4583657196338747400953387 6875485794508121101430081)
        ·
          refine ⟨5156614345881090826072561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6875485794508121101430081 5156614345881090826072561)
          ·
            refine ⟨3867460759410818119554421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5156614345881090826072561 3867460759410818119554421)
            ·
              refine ⟨362574446194764198708227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3867460759410818119554421 362574446194764198708227)
              ·
                refine ⟨543861669292146298062341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 362574446194764198708227 543861669292146298062341)
                ·
                  refine ⟨101974062992277430886689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 543861669292146298062341 101974062992277430886689)
                  ·
                    rfl

theorem cell20_223418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_223418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223418 prefixEnd_223418 := by exact prefixLift 223418
  have htrace : WordTrace (prefixWord ++ tailWord_223418) baseStart_223418 baseEnd_223418 := by
    simpa [prefixWord, tailWord_223418, baseEnd_223418] using wordTrace_append hprefix tailTrace_223418
  have hstable : (prefixWord ++ tailWord_223418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223418).length < 2 ^ (prefixWord ++ tailWord_223418).sum := by decide
  have hdescent : baseEnd_223418 < baseStart_223418 := by decide
  rcases family_descends (prefixWord ++ tailWord_223418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223428 : List Nat := [2, 3, 3, 1, 2, 2, 1, 3, 3]
def baseStart_223428 : Nat := 118140960795 + 223428 * 2 ^ 59
def prefixEnd_223428 : Nat := 4983230072969 + 3 ^ 40 * 223428 * 2
def baseEnd_223428 : Nat := 101978627264761840553315

theorem tailTrace_223428 : CollatzResearch.WordTrace tailWord_223428 prefixEnd_223428 101978627264761840553315 := by
  unfold tailWord_223428
  simp only [CollatzResearch.WordTrace]
  refine ⟨4074544317282994654779469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5432725756377326206372625 4074544317282994654779469)
  ·
    refine ⟨1527954118981122995542301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4074544317282994654779469 1527954118981122995542301)
    ·
      refine ⟨572982794617921123328363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1527954118981122995542301 572982794617921123328363)
      ·
        refine ⟨859474191926881684992545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572982794617921123328363 859474191926881684992545)
        ·
          refine ⟨644605643945161263744409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 859474191926881684992545 644605643945161263744409)
          ·
            refine ⟨483454232958870947808307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 644605643945161263744409 483454232958870947808307)
            ·
              refine ⟨725181349438306421712461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483454232958870947808307 725181349438306421712461)
              ·
                refine ⟨271943006039364908142173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 725181349438306421712461 271943006039364908142173)
                ·
                  refine ⟨101978627264761840553315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 271943006039364908142173 101978627264761840553315)
                  ·
                    rfl

theorem cell20_223428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_223428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223428 prefixEnd_223428 := by exact prefixLift 223428
  have htrace : WordTrace (prefixWord ++ tailWord_223428) baseStart_223428 baseEnd_223428 := by
    simpa [prefixWord, tailWord_223428, baseEnd_223428] using wordTrace_append hprefix tailTrace_223428
  have hstable : (prefixWord ++ tailWord_223428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223428).length < 2 ^ (prefixWord ++ tailWord_223428).sum := by decide
  have hdescent : baseEnd_223428 < baseStart_223428 := by decide
  rcases family_descends (prefixWord ++ tailWord_223428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223439 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 6]
def baseStart_223439 : Nat := 118140960795 + 223439 * 2 ^ 59
def prefixEnd_223439 : Nat := 4983230072969 + 3 ^ 40 * 223439 * 2
def baseEnd_223439 : Nat := 101983647964494691186603

theorem tailTrace_223439 : CollatzResearch.WordTrace tailWord_223439 prefixEnd_223439 101983647964494691186603 := by
  unfold tailWord_223439
  simp only [CollatzResearch.WordTrace]
  refine ⟨8149489837526138188209371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5432993225017425458806247 8149489837526138188209371)
  ·
    refine ⟨12224234756289207282314057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8149489837526138188209371 12224234756289207282314057)
    ·
      refine ⟨9168176067216905461735543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12224234756289207282314057 9168176067216905461735543)
      ·
        refine ⟨13752264100825358192603315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9168176067216905461735543 13752264100825358192603315)
        ·
          refine ⟨20628396151238037288904973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13752264100825358192603315 20628396151238037288904973)
          ·
            refine ⟨7735648556714263983339365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20628396151238037288904973 7735648556714263983339365)
            ·
              refine ⟨1450434104383924496876131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7735648556714263983339365 1450434104383924496876131)
              ·
                refine ⟨2175651156575886745314197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1450434104383924496876131 2175651156575886745314197)
                ·
                  refine ⟨101983647964494691186603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2175651156575886745314197 101983647964494691186603)
                  ·
                    rfl

theorem cell20_223439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_223439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223439 prefixEnd_223439 := by exact prefixLift 223439
  have htrace : WordTrace (prefixWord ++ tailWord_223439) baseStart_223439 baseEnd_223439 := by
    simpa [prefixWord, tailWord_223439, baseEnd_223439] using wordTrace_append hprefix tailTrace_223439
  have hstable : (prefixWord ++ tailWord_223439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223439).length < 2 ^ (prefixWord ++ tailWord_223439).sum := by decide
  have hdescent : baseEnd_223439 < baseStart_223439 := by decide
  rcases family_descends (prefixWord ++ tailWord_223439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223463 : List Nat := [1, 1, 5, 3, 1, 9]
def baseStart_223463 : Nat := 118140960795 + 223463 * 2 ^ 59
def prefixEnd_223463 : Nat := 4983230072969 + 3 ^ 40 * 223463 * 2
def baseEnd_223463 : Nat := 3777577859942862014315

theorem tailTrace_223463 : CollatzResearch.WordTrace tailWord_223463 prefixEnd_223463 3777577859942862014315 := by
  unfold tailWord_223463
  simp only [CollatzResearch.WordTrace]
  refine ⟨8150365189439190287083043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5433576792959460191388695 8150365189439190287083043)
  ·
    refine ⟨12225547784158785430624565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8150365189439190287083043 12225547784158785430624565)
    ·
      refine ⟨1146145104764886134121053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12225547784158785430624565 1146145104764886134121053)
      ·
        refine ⟨429804414286832300295395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1146145104764886134121053 429804414286832300295395)
        ·
          refine ⟨644706621430248450443093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 429804414286832300295395 644706621430248450443093)
          ·
            refine ⟨3777577859942862014315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 644706621430248450443093 3777577859942862014315)
            ·
              rfl

theorem cell20_223463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 9].length) (baseStart_223463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223463 prefixEnd_223463 := by exact prefixLift 223463
  have htrace : WordTrace (prefixWord ++ tailWord_223463) baseStart_223463 baseEnd_223463 := by
    simpa [prefixWord, tailWord_223463, baseEnd_223463] using wordTrace_append hprefix tailTrace_223463
  have hstable : (prefixWord ++ tailWord_223463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223463).length < 2 ^ (prefixWord ++ tailWord_223463).sum := by decide
  have hdescent : baseEnd_223463 < baseStart_223463 := by decide
  rcases family_descends (prefixWord ++ tailWord_223463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223511 : List Nat := [1, 1, 3, 4, 1, 2, 1, 5, 2]
def baseStart_223511 : Nat := 118140960795 + 223511 * 2 ^ 59
def prefixEnd_223511 : Nat := 4983230072969 + 3 ^ 40 * 223511 * 2
def baseEnd_223511 : Nat := 102016510726382440786309

theorem tailTrace_223511 : CollatzResearch.WordTrace tailWord_223511 prefixEnd_223511 102016510726382440786309 := by
  unfold tailWord_223511
  simp only [CollatzResearch.WordTrace]
  refine ⟨8152115893265294484830387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5434743928843529656553591 8152115893265294484830387)
  ·
    refine ⟨12228173839897941727245581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8152115893265294484830387 12228173839897941727245581)
    ·
      refine ⟨4585565189961728147717093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12228173839897941727245581 4585565189961728147717093)
      ·
        refine ⟨859793473117824027696955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4585565189961728147717093 859793473117824027696955)
        ·
          refine ⟨1289690209676736041545433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 859793473117824027696955 1289690209676736041545433)
          ·
            refine ⟨967267657257552031159075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1289690209676736041545433 967267657257552031159075)
            ·
              refine ⟨1450901485886328046738613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 967267657257552031159075 1450901485886328046738613)
              ·
                refine ⟨136022014301843254381745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1450901485886328046738613 136022014301843254381745)
                ·
                  refine ⟨102016510726382440786309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136022014301843254381745 102016510726382440786309)
                  ·
                    rfl

theorem cell20_223511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 5, 2].length) (baseStart_223511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223511 prefixEnd_223511 := by exact prefixLift 223511
  have htrace : WordTrace (prefixWord ++ tailWord_223511) baseStart_223511 baseEnd_223511 := by
    simpa [prefixWord, tailWord_223511, baseEnd_223511] using wordTrace_append hprefix tailTrace_223511
  have hstable : (prefixWord ++ tailWord_223511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223511).length < 2 ^ (prefixWord ++ tailWord_223511).sum := by decide
  have hdescent : baseEnd_223511 < baseStart_223511 := by decide
  rcases family_descends (prefixWord ++ tailWord_223511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223525 : List Nat := [1, 3, 1, 2, 5, 1, 1, 1, 5]
def baseStart_223525 : Nat := 118140960795 + 223525 * 2 ^ 59
def prefixEnd_223525 : Nat := 4983230072969 + 3 ^ 40 * 223525 * 2
def baseEnd_223525 : Nat := 102022900707860614319585

theorem tailTrace_223525 : CollatzResearch.WordTrace tailWord_223525 prefixEnd_223525 102022900707860614319585 := by
  unfold tailWord_223525
  simp only [CollatzResearch.WordTrace]
  refine ⟨8152626515214574875840029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5435084343476383250560019 8152626515214574875840029)
  ·
    refine ⟨3057234943205465578440011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8152626515214574875840029 3057234943205465578440011)
    ·
      refine ⟨4585852414808198367660017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3057234943205465578440011 4585852414808198367660017)
      ·
        refine ⟨3439389311106148775745013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4585852414808198367660017 3439389311106148775745013)
        ·
          refine ⟨322442747916201447726095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3439389311106148775745013 322442747916201447726095)
          ·
            refine ⟨483664121874302171589143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322442747916201447726095 483664121874302171589143)
            ·
              refine ⟨725496182811453257383715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 483664121874302171589143 725496182811453257383715)
              ·
                refine ⟨1088244274217179886075573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 725496182811453257383715 1088244274217179886075573)
                ·
                  refine ⟨102022900707860614319585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1088244274217179886075573 102022900707860614319585)
                  ·
                    rfl

theorem cell20_223525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_223525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223525 prefixEnd_223525 := by exact prefixLift 223525
  have htrace : WordTrace (prefixWord ++ tailWord_223525) baseStart_223525 baseEnd_223525 := by
    simpa [prefixWord, tailWord_223525, baseEnd_223525] using wordTrace_append hprefix tailTrace_223525
  have hstable : (prefixWord ++ tailWord_223525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223525).length < 2 ^ (prefixWord ++ tailWord_223525).sum := by decide
  have hdescent : baseEnd_223525 < baseStart_223525 := by decide
  rcases family_descends (prefixWord ++ tailWord_223525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223594 : List Nat := [3, 1, 3, 3, 1, 2, 2, 5]
def baseStart_223594 : Nat := 118140960795 + 223594 * 2 ^ 59
def prefixEnd_223594 : Nat := 4983230072969 + 3 ^ 40 * 223594 * 2
def baseEnd_223594 : Nat := 34018131396001013673101

theorem tailTrace_223594 : CollatzResearch.WordTrace tailWord_223594 prefixEnd_223594 34018131396001013673101 := by
  unfold tailWord_223594
  simp only [CollatzResearch.WordTrace]
  refine ⟨2038785787991149915025459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5436762101309733106734557 2038785787991149915025459)
  ·
    refine ⟨3058178681986724872538189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2038785787991149915025459 3058178681986724872538189)
    ·
      refine ⟨1146817005745021827201821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3058178681986724872538189 1146817005745021827201821)
      ·
        refine ⟨430056377154383185200683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1146817005745021827201821 430056377154383185200683)
        ·
          refine ⟨645084565731574777801025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430056377154383185200683 645084565731574777801025)
          ·
            refine ⟨483813424298681083350769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645084565731574777801025 483813424298681083350769)
            ·
              refine ⟨362860068224010812513077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 483813424298681083350769 362860068224010812513077)
              ·
                refine ⟨34018131396001013673101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 362860068224010812513077 34018131396001013673101)
                ·
                  rfl

theorem cell20_223594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 5].length) (baseStart_223594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223594 prefixEnd_223594 := by exact prefixLift 223594
  have htrace : WordTrace (prefixWord ++ tailWord_223594) baseStart_223594 baseEnd_223594 := by
    simpa [prefixWord, tailWord_223594, baseEnd_223594] using wordTrace_append hprefix tailTrace_223594
  have hstable : (prefixWord ++ tailWord_223594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223594).length < 2 ^ (prefixWord ++ tailWord_223594).sum := by decide
  have hdescent : baseEnd_223594 < baseStart_223594 := by decide
  rcases family_descends (prefixWord ++ tailWord_223594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223642 : List Nat := [3, 1, 1, 4, 1, 2, 4, 2, 2]
def baseStart_223642 : Nat := 118140960795 + 223642 * 2 ^ 59
def prefixEnd_223642 : Nat := 4983230072969 + 3 ^ 40 * 223642 * 2
def baseEnd_223642 : Nat := 102076302695928207419107

theorem tailTrace_223642 : CollatzResearch.WordTrace tailWord_223642 prefixEnd_223642 102076302695928207419107 := by
  unfold tailWord_223642
  simp only [CollatzResearch.WordTrace]
  refine ⟨2039223463947675964462295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5437929237193802571899453 2039223463947675964462295)
  ·
    refine ⟨3058835195921513946693443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2039223463947675964462295 3058835195921513946693443)
    ·
      refine ⟨4588252793882270920040165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3058835195921513946693443 4588252793882270920040165)
      ·
        refine ⟨860297398852925797507531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4588252793882270920040165 860297398852925797507531)
        ·
          refine ⟨1290446098279388696261297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860297398852925797507531 1290446098279388696261297)
          ·
            refine ⟨967834573709541522195973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1290446098279388696261297 967834573709541522195973)
            ·
              refine ⟨181468982570539035411745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 967834573709541522195973 181468982570539035411745)
              ·
                refine ⟨136101736927904276558809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181468982570539035411745 136101736927904276558809)
                ·
                  refine ⟨102076302695928207419107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136101736927904276558809 102076302695928207419107)
                  ·
                    rfl

theorem cell20_223642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_223642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223642 prefixEnd_223642 := by exact prefixLift 223642
  have htrace : WordTrace (prefixWord ++ tailWord_223642) baseStart_223642 baseEnd_223642 := by
    simpa [prefixWord, tailWord_223642, baseEnd_223642] using wordTrace_append hprefix tailTrace_223642
  have hstable : (prefixWord ++ tailWord_223642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223642).length < 2 ^ (prefixWord ++ tailWord_223642).sum := by decide
  have hdescent : baseEnd_223642 < baseStart_223642 := by decide
  rcases family_descends (prefixWord ++ tailWord_223642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223649 : List Nat := [1, 2, 3, 5, 1, 2, 1, 5]
def baseStart_223649 : Nat := 118140960795 + 223649 * 2 ^ 59
def prefixEnd_223649 : Nat := 4983230072969 + 3 ^ 40 * 223649 * 2
def baseEnd_223649 : Nat := 34026499228889098061915

theorem tailTrace_223649 : CollatzResearch.WordTrace tailWord_223649 prefixEnd_223649 34026499228889098061915 := by
  unfold tailWord_223649
  simp only [CollatzResearch.WordTrace]
  refine ⟨8157149166765344053354001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5438099444510229368902667 8157149166765344053354001)
  ·
    refine ⟨6117861875074008040015501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8157149166765344053354001 6117861875074008040015501)
    ·
      refine ⟨2294198203152753015005813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6117861875074008040015501 2294198203152753015005813)
      ·
        refine ⟨215081081545570595156795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2294198203152753015005813 215081081545570595156795)
        ·
          refine ⟨322621622318355892735193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215081081545570595156795 322621622318355892735193)
          ·
            refine ⟨241966216738766919551395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322621622318355892735193 241966216738766919551395)
            ·
              refine ⟨362949325108150379327093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 241966216738766919551395 362949325108150379327093)
              ·
                refine ⟨34026499228889098061915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 362949325108150379327093 34026499228889098061915)
                ·
                  rfl

theorem cell20_223649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 5].length) (baseStart_223649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223649 prefixEnd_223649 := by exact prefixLift 223649
  have htrace : WordTrace (prefixWord ++ tailWord_223649) baseStart_223649 baseEnd_223649 := by
    simpa [prefixWord, tailWord_223649, baseEnd_223649] using wordTrace_append hprefix tailTrace_223649
  have hstable : (prefixWord ++ tailWord_223649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223649).length < 2 ^ (prefixWord ++ tailWord_223649).sum := by decide
  have hdescent : baseEnd_223649 < baseStart_223649 := by decide
  rcases family_descends (prefixWord ++ tailWord_223649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223656 : List Nat := [2, 1, 6, 1, 1, 1, 2, 3, 3]
def baseStart_223656 : Nat := 118140960795 + 223656 * 2 ^ 59
def prefixEnd_223656 : Nat := 4983230072969 + 3 ^ 40 * 223656 * 2
def baseEnd_223656 : Nat := 102082692677406380952383

theorem tailTrace_223656 : CollatzResearch.WordTrace tailWord_223656 prefixEnd_223656 102082692677406380952383 := by
  unfold tailWord_223656
  simp only [CollatzResearch.WordTrace]
  refine ⟨4078702238869992124429411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5438269651826656165905881 4078702238869992124429411)
  ·
    refine ⟨6118053358304988186644117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4078702238869992124429411 6118053358304988186644117)
    ·
      refine ⟨286783751170546321248943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6118053358304988186644117 286783751170546321248943)
      ·
        refine ⟨430175626755819481873415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 286783751170546321248943 430175626755819481873415)
        ·
          refine ⟨645263440133729222810123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430175626755819481873415 645263440133729222810123)
          ·
            refine ⟨967895160200593834215185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645263440133729222810123 967895160200593834215185)
            ·
              refine ⟨725921370150445375661389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 967895160200593834215185 725921370150445375661389)
              ·
                refine ⟨272220513806417015873021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 725921370150445375661389 272220513806417015873021)
                ·
                  refine ⟨102082692677406380952383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272220513806417015873021 102082692677406380952383)
                  ·
                    rfl

theorem cell20_223656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_223656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223656 prefixEnd_223656 := by exact prefixLift 223656
  have htrace : WordTrace (prefixWord ++ tailWord_223656) baseStart_223656 baseEnd_223656 := by
    simpa [prefixWord, tailWord_223656, baseEnd_223656] using wordTrace_append hprefix tailTrace_223656
  have hstable : (prefixWord ++ tailWord_223656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223656).length < 2 ^ (prefixWord ++ tailWord_223656).sum := by decide
  have hdescent : baseEnd_223656 < baseStart_223656 := by decide
  rcases family_descends (prefixWord ++ tailWord_223656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223674 : List Nat := [3, 1, 1, 1, 2, 1, 1, 10]
def baseStart_223674 : Nat := 118140960795 + 223674 * 2 ^ 59
def prefixEnd_223674 : Nat := 4983230072969 + 3 ^ 40 * 223674 * 2
def baseEnd_223674 : Nat := 34030302789292772784103

theorem tailTrace_223674 : CollatzResearch.WordTrace tailWord_223674 prefixEnd_223674 34030302789292772784103 := by
  unfold tailWord_223674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2039515247918693330753519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5438707327783182215342717 2039515247918693330753519)
  ·
    refine ⟨3059272871878039996130279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2039515247918693330753519 3059272871878039996130279)
    ·
      refine ⟨4588909307817059994195419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3059272871878039996130279 4588909307817059994195419)
      ·
        refine ⟨6883363961725589991293129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4588909307817059994195419 6883363961725589991293129)
        ·
          refine ⟨5162522971294192493469847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6883363961725589991293129 5162522971294192493469847)
          ·
            refine ⟨7743784456941288740204771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5162522971294192493469847 7743784456941288740204771)
            ·
              refine ⟨11615676685411933110307157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7743784456941288740204771 11615676685411933110307157)
              ·
                refine ⟨34030302789292772784103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11615676685411933110307157 34030302789292772784103)
                ·
                  rfl

theorem cell20_223674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_223674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223674 prefixEnd_223674 := by exact prefixLift 223674
  have htrace : WordTrace (prefixWord ++ tailWord_223674) baseStart_223674 baseEnd_223674 := by
    simpa [prefixWord, tailWord_223674, baseEnd_223674] using wordTrace_append hprefix tailTrace_223674
  have hstable : (prefixWord ++ tailWord_223674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223674).length < 2 ^ (prefixWord ++ tailWord_223674).sum := by decide
  have hdescent : baseEnd_223674 < baseStart_223674 := by decide
  rcases family_descends (prefixWord ++ tailWord_223674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223701 : List Nat := [1, 3, 2, 3, 1, 2, 2, 4, 2]
def baseStart_223701 : Nat := 118140960795 + 223701 * 2 ^ 59
def prefixEnd_223701 : Nat := 4983230072969 + 3 ^ 40 * 223701 * 2
def baseEnd_223701 : Nat := 102103231903586224452199

theorem tailTrace_223701 : CollatzResearch.WordTrace tailWord_223701 prefixEnd_223701 102103231903586224452199 := by
  unfold tailWord_223701
  simp only [CollatzResearch.WordTrace]
  refine ⟨8159045762576956934246957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5439363841717971289497971 8159045762576956934246957)
  ·
    refine ⟨3059642160966358850342609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8159045762576956934246957 3059642160966358850342609)
    ·
      refine ⟨2294731620724769137756957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3059642160966358850342609 2294731620724769137756957)
      ·
        refine ⟨860524357771788426658859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2294731620724769137756957 860524357771788426658859)
        ·
          refine ⟨1290786536657682639988289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 860524357771788426658859 1290786536657682639988289)
          ·
            refine ⟨968089902493261979991217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1290786536657682639988289 968089902493261979991217)
            ·
              refine ⟨726067426869946484993413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 968089902493261979991217 726067426869946484993413)
              ·
                refine ⟨136137642538114965936265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 726067426869946484993413 136137642538114965936265)
                ·
                  refine ⟨102103231903586224452199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136137642538114965936265 102103231903586224452199)
                  ·
                    rfl

theorem cell20_223701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_223701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223701 prefixEnd_223701 := by exact prefixLift 223701
  have htrace : WordTrace (prefixWord ++ tailWord_223701) baseStart_223701 baseEnd_223701 := by
    simpa [prefixWord, tailWord_223701, baseEnd_223701] using wordTrace_append hprefix tailTrace_223701
  have hstable : (prefixWord ++ tailWord_223701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223701).length < 2 ^ (prefixWord ++ tailWord_223701).sum := by decide
  have hdescent : baseEnd_223701 < baseStart_223701 := by decide
  rcases family_descends (prefixWord ++ tailWord_223701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223712 : List Nat := [2, 1, 1, 3, 1, 1, 4, 7]
def baseStart_223712 : Nat := 118140960795 + 223712 * 2 ^ 59
def prefixEnd_223712 : Nat := 4983230072969 + 3 ^ 40 * 223712 * 2
def baseEnd_223712 : Nat := 34036084201106358361829

theorem tailTrace_223712 : CollatzResearch.WordTrace tailWord_223712 prefixEnd_223712 34036084201106358361829 := by
  unfold tailWord_223712
  simp only [CollatzResearch.WordTrace]
  refine ⟨4079723482768552906448695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5439631310358070541931593 4079723482768552906448695)
  ·
    refine ⟨6119585224152829359673043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4079723482768552906448695 6119585224152829359673043)
    ·
      refine ⟨9179377836229244039509565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6119585224152829359673043 9179377836229244039509565)
      ·
        refine ⟨3442266688585966514816087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9179377836229244039509565 3442266688585966514816087)
        ·
          refine ⟨5163400032878949772224131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3442266688585966514816087 5163400032878949772224131)
          ·
            refine ⟨7745100049318424658336197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5163400032878949772224131 7745100049318424658336197)
            ·
              refine ⟨1452206259247204623438037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7745100049318424658336197 1452206259247204623438037)
              ·
                refine ⟨34036084201106358361829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1452206259247204623438037 34036084201106358361829)
                ·
                  rfl

theorem cell20_223712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_223712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223712 prefixEnd_223712 := by exact prefixLift 223712
  have htrace : WordTrace (prefixWord ++ tailWord_223712) baseStart_223712 baseEnd_223712 := by
    simpa [prefixWord, tailWord_223712, baseEnd_223712] using wordTrace_append hprefix tailTrace_223712
  have hstable : (prefixWord ++ tailWord_223712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223712).length < 2 ^ (prefixWord ++ tailWord_223712).sum := by decide
  have hdescent : baseEnd_223712 < baseStart_223712 := by decide
  rcases family_descends (prefixWord ++ tailWord_223712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223722 : List Nat := [3, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_223722 : Nat := 118140960795 + 223722 * 2 ^ 59
def prefixEnd_223722 : Nat := 4983230072969 + 3 ^ 40 * 223722 * 2
def baseEnd_223722 : Nat := 102112816875803484752113

theorem tailTrace_223722 : CollatzResearch.WordTrace tailWord_223722 prefixEnd_223722 102112816875803484752113 := by
  unfold tailWord_223722
  simp only [CollatzResearch.WordTrace]
  refine ⟨2039952923875219380190355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5439874463667251680507613 2039952923875219380190355)
  ·
    refine ⟨3059929385812829070285533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2039952923875219380190355 3059929385812829070285533)
    ·
      refine ⟨1147473519679810901357075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3059929385812829070285533 1147473519679810901357075)
      ·
        refine ⟨1721210279519716352035613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1147473519679810901357075 1721210279519716352035613)
        ·
          refine ⟨645453854819893632013355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1721210279519716352035613 645453854819893632013355)
          ·
            refine ⟨968180782229840448020033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645453854819893632013355 968180782229840448020033)
            ·
              refine ⟨726135586672380336015025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 968180782229840448020033 726135586672380336015025)
              ·
                refine ⟨544601690004285252011269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 726135586672380336015025 544601690004285252011269)
                ·
                  refine ⟨102112816875803484752113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 544601690004285252011269 102112816875803484752113)
                  ·
                    rfl

theorem cell20_223722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_223722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223722 prefixEnd_223722 := by exact prefixLift 223722
  have htrace : WordTrace (prefixWord ++ tailWord_223722) baseStart_223722 baseEnd_223722 := by
    simpa [prefixWord, tailWord_223722, baseEnd_223722] using wordTrace_append hprefix tailTrace_223722
  have hstable : (prefixWord ++ tailWord_223722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223722).length < 2 ^ (prefixWord ++ tailWord_223722).sum := by decide
  have hdescent : baseEnd_223722 < baseStart_223722 := by decide
  rcases family_descends (prefixWord ++ tailWord_223722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223725 : List Nat := [1, 5, 1, 3, 1, 3, 2, 4]
def baseStart_223725 : Nat := 118140960795 + 223725 * 2 ^ 59
def prefixEnd_223725 : Nat := 4983230072969 + 3 ^ 40 * 223725 * 2
def baseEnd_223725 : Nat := 34038062052516269217367

theorem tailTrace_223725 : CollatzResearch.WordTrace tailWord_223725 prefixEnd_223725 34038062052516269217367 := by
  unfold tailWord_223725
  simp only [CollatzResearch.WordTrace]
  refine ⟨8159921114490009033120629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5439947409660006022080419 8159921114490009033120629)
  ·
    refine ⟨764992604483438346855059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8159921114490009033120629 764992604483438346855059)
    ·
      refine ⟨1147488906725157520282589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 764992604483438346855059 1147488906725157520282589)
      ·
        refine ⟨430308340021934070105971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1147488906725157520282589 430308340021934070105971)
        ·
          refine ⟨645462510032901105158957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430308340021934070105971 645462510032901105158957)
          ·
            refine ⟨242048441262337914434609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 645462510032901105158957 242048441262337914434609)
            ·
              refine ⟨181536330946753435825957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242048441262337914434609 181536330946753435825957)
              ·
                refine ⟨34038062052516269217367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181536330946753435825957 34038062052516269217367)
                ·
                  rfl

theorem cell20_223725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 4].length) (baseStart_223725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223725 prefixEnd_223725 := by exact prefixLift 223725
  have htrace : WordTrace (prefixWord ++ tailWord_223725) baseStart_223725 baseEnd_223725 := by
    simpa [prefixWord, tailWord_223725, baseEnd_223725] using wordTrace_append hprefix tailTrace_223725
  have hstable : (prefixWord ++ tailWord_223725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223725).length < 2 ^ (prefixWord ++ tailWord_223725).sum := by decide
  have hdescent : baseEnd_223725 < baseStart_223725 := by decide
  rcases family_descends (prefixWord ++ tailWord_223725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223756 : List Nat := [2, 2, 1, 2, 4, 2, 3, 2, 2]
def baseStart_223756 : Nat := 118140960795 + 223756 * 2 ^ 59
def prefixEnd_223756 : Nat := 4983230072969 + 3 ^ 40 * 223756 * 2
def baseEnd_223756 : Nat := 102128335402250477618641

theorem tailTrace_223756 : CollatzResearch.WordTrace tailWord_223756 prefixEnd_223756 102128335402250477618641 := by
  unfold tailWord_223756
  simp only [CollatzResearch.WordTrace]
  refine ⟨4080525888688850663749561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5440701184918467551666081 4080525888688850663749561)
  ·
    refine ⟨3060394416516637997812171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4080525888688850663749561 3060394416516637997812171)
    ·
      refine ⟨4590591624774956996718257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3060394416516637997812171 4590591624774956996718257)
      ·
        refine ⟨3442943718581217747538693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4590591624774956996718257 3442943718581217747538693)
        ·
          refine ⟨645551947233978327663505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3442943718581217747538693 645551947233978327663505)
          ·
            refine ⟨484163960425483745747629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645551947233978327663505 484163960425483745747629)
            ·
              refine ⟨181561485159556404655361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 484163960425483745747629 181561485159556404655361)
              ·
                refine ⟨136171113869667303491521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 181561485159556404655361 136171113869667303491521)
                ·
                  refine ⟨102128335402250477618641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136171113869667303491521 102128335402250477618641)
                  ·
                    rfl

theorem cell20_223756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_223756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223756 prefixEnd_223756 := by exact prefixLift 223756
  have htrace : WordTrace (prefixWord ++ tailWord_223756) baseStart_223756 baseEnd_223756 := by
    simpa [prefixWord, tailWord_223756, baseEnd_223756] using wordTrace_append hprefix tailTrace_223756
  have hstable : (prefixWord ++ tailWord_223756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223756).length < 2 ^ (prefixWord ++ tailWord_223756).sum := by decide
  have hdescent : baseEnd_223756 < baseStart_223756 := by decide
  rcases family_descends (prefixWord ++ tailWord_223756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223781 : List Nat := [1, 3, 1, 2, 2, 1, 2, 4, 4]
def baseStart_223781 : Nat := 118140960795 + 223781 * 2 ^ 59
def prefixEnd_223781 : Nat := 4983230072969 + 3 ^ 40 * 223781 * 2
def baseEnd_223781 : Nat := 102139746083461501785205

theorem tailTrace_223781 : CollatzResearch.WordTrace tailWord_223781 prefixEnd_223781 102139746083461501785205 := by
  unfold tailWord_223781
  simp only [CollatzResearch.WordTrace]
  refine ⟨8161963602287130597159197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5441309068191420398106131 8161963602287130597159197)
  ·
    refine ⟨3060736350857673973934699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8161963602287130597159197 3060736350857673973934699)
    ·
      refine ⟨4591104526286510960902049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3060736350857673973934699 4591104526286510960902049)
      ·
        refine ⟨3443328394714883220676537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4591104526286510960902049 3443328394714883220676537)
        ·
          refine ⟨2582496296036162415507403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3443328394714883220676537 2582496296036162415507403)
          ·
            refine ⟨3873744444054243623261105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582496296036162415507403 3873744444054243623261105)
            ·
              refine ⟨2905308333040682717445829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3873744444054243623261105 2905308333040682717445829)
              ·
                refine ⟨544745312445128009521093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2905308333040682717445829 544745312445128009521093)
                ·
                  refine ⟨102139746083461501785205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 544745312445128009521093 102139746083461501785205)
                  ·
                    rfl

theorem cell20_223781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_223781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223781 prefixEnd_223781 := by exact prefixLift 223781
  have htrace : WordTrace (prefixWord ++ tailWord_223781) baseStart_223781 baseEnd_223781 := by
    simpa [prefixWord, tailWord_223781, baseEnd_223781] using wordTrace_append hprefix tailTrace_223781
  have hstable : (prefixWord ++ tailWord_223781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223781).length < 2 ^ (prefixWord ++ tailWord_223781).sum := by decide
  have hdescent : baseEnd_223781 < baseStart_223781 := by decide
  rcases family_descends (prefixWord ++ tailWord_223781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223815 : List Nat := [1, 1, 4, 1, 4, 2, 1, 4, 2]
def baseStart_223815 : Nat := 118140960795 + 223815 * 2 ^ 59
def prefixEnd_223815 : Nat := 4983230072969 + 3 ^ 40 * 223815 * 2
def baseEnd_223815 : Nat := 102155264609908494651733

theorem tailTrace_223815 : CollatzResearch.WordTrace tailWord_223815 prefixEnd_223815 102155264609908494651733 := by
  unfold tailWord_223815
  simp only [CollatzResearch.WordTrace]
  refine ⟨8163203684163954403896899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5442135789442636269264599 8163203684163954403896899)
  ·
    refine ⟨12244805526245931605845349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8163203684163954403896899 12244805526245931605845349)
    ·
      refine ⟨2295901036171112176096003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12244805526245931605845349 2295901036171112176096003)
      ·
        refine ⟨3443851554256668264144005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2295901036171112176096003 3443851554256668264144005)
        ·
          refine ⟨645722166423125299527001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3443851554256668264144005 645722166423125299527001)
          ·
            refine ⟨484291624817343974645251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 645722166423125299527001 484291624817343974645251)
            ·
              refine ⟨726437437226015961967877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484291624817343974645251 726437437226015961967877)
              ·
                refine ⟨136207019479877992868977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 726437437226015961967877 136207019479877992868977)
                ·
                  refine ⟨102155264609908494651733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136207019479877992868977 102155264609908494651733)
                  ·
                    rfl

theorem cell20_223815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4, 2].length) (baseStart_223815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223815 prefixEnd_223815 := by exact prefixLift 223815
  have htrace : WordTrace (prefixWord ++ tailWord_223815) baseStart_223815 baseEnd_223815 := by
    simpa [prefixWord, tailWord_223815, baseEnd_223815] using wordTrace_append hprefix tailTrace_223815
  have hstable : (prefixWord ++ tailWord_223815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223815).length < 2 ^ (prefixWord ++ tailWord_223815).sum := by decide
  have hdescent : baseEnd_223815 < baseStart_223815 := by decide
  rcases family_descends (prefixWord ++ tailWord_223815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223833 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 9]
def baseStart_223833 : Nat := 118140960795 + 223833 * 2 ^ 59
def prefixEnd_223833 : Nat := 4983230072969 + 3 ^ 40 * 223833 * 2
def baseEnd_223833 : Nat := 102163480300380432051659

theorem tailTrace_223833 : CollatzResearch.WordTrace tailWord_223833 prefixEnd_223833 102163480300380432051659 := by
  unfold tailWord_223833
  simp only [CollatzResearch.WordTrace]
  refine ⟨8163860198098743478052153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5442573465399162318701435 8163860198098743478052153)
  ·
    refine ⟨6122895148574057608539115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8163860198098743478052153 6122895148574057608539115)
    ·
      refine ⟨9184342722861086412808673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6122895148574057608539115 9184342722861086412808673)
      ·
        refine ⟨6888257042145814809606505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9184342722861086412808673 6888257042145814809606505)
        ·
          refine ⟨5166192781609361107204879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6888257042145814809606505 5166192781609361107204879)
          ·
            refine ⟨7749289172414041660807319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5166192781609361107204879 7749289172414041660807319)
            ·
              refine ⟨11623933758621062491210979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7749289172414041660807319 11623933758621062491210979)
              ·
                refine ⟨17435900637931593736816469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11623933758621062491210979 17435900637931593736816469)
                ·
                  refine ⟨102163480300380432051659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17435900637931593736816469 102163480300380432051659)
                  ·
                    rfl

theorem cell20_223833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_223833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223833 prefixEnd_223833 := by exact prefixLift 223833
  have htrace : WordTrace (prefixWord ++ tailWord_223833) baseStart_223833 baseEnd_223833 := by
    simpa [prefixWord, tailWord_223833, baseEnd_223833] using wordTrace_append hprefix tailTrace_223833
  have hstable : (prefixWord ++ tailWord_223833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223833).length < 2 ^ (prefixWord ++ tailWord_223833).sum := by decide
  have hdescent : baseEnd_223833 < baseStart_223833 := by decide
  rcases family_descends (prefixWord ++ tailWord_223833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223843 : List Nat := [1, 1, 1, 5, 1, 2, 5, 4]
def baseStart_223843 : Nat := 118140960795 + 223843 * 2 ^ 59
def prefixEnd_223843 : Nat := 4983230072969 + 3 ^ 40 * 223843 * 2
def baseEnd_223843 : Nat := 34056014857621613906095

theorem tailTrace_223843 : CollatzResearch.WordTrace tailWord_223843 prefixEnd_223843 34056014857621613906095 := by
  unfold tailWord_223843
  simp only [CollatzResearch.WordTrace]
  refine ⟨8164224928062515185916183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5442816618708343457277455 8164224928062515185916183)
  ·
    refine ⟨12246337392093772778874275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8164224928062515185916183 12246337392093772778874275)
    ·
      refine ⟨18369506088140659168311413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12246337392093772778874275 18369506088140659168311413)
      ·
        refine ⟨1722141195763186797029195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18369506088140659168311413 1722141195763186797029195)
        ·
          refine ⟨2583211793644780195543793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1722141195763186797029195 2583211793644780195543793)
          ·
            refine ⟨1937408845233585146657845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2583211793644780195543793 1937408845233585146657845)
            ·
              refine ⟨181632079240648607499173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1937408845233585146657845 181632079240648607499173)
              ·
                refine ⟨34056014857621613906095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181632079240648607499173 34056014857621613906095)
                ·
                  rfl

theorem cell20_223843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 4].length) (baseStart_223843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223843 prefixEnd_223843 := by exact prefixLift 223843
  have htrace : WordTrace (prefixWord ++ tailWord_223843) baseStart_223843 baseEnd_223843 := by
    simpa [prefixWord, tailWord_223843, baseEnd_223843] using wordTrace_append hprefix tailTrace_223843
  have hstable : (prefixWord ++ tailWord_223843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223843).length < 2 ^ (prefixWord ++ tailWord_223843).sum := by decide
  have hdescent : baseEnd_223843 < baseStart_223843 := by decide
  rcases family_descends (prefixWord ++ tailWord_223843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223850 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_223850 : Nat := 118140960795 + 223850 * 2 ^ 59
def prefixEnd_223850 : Nat := 4983230072969 + 3 ^ 40 * 223850 * 2
def baseEnd_223850 : Nat := 102171239563603928484923

theorem tailTrace_223850 : CollatzResearch.WordTrace tailWord_223850 prefixEnd_223850 102171239563603928484923 := by
  unfold tailWord_223850
  simp only [CollatzResearch.WordTrace]
  refine ⟨2041120059759288845355251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5442986826024770254280669 2041120059759288845355251)
  ·
    refine ⟨3061680089638933268032877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2041120059759288845355251 3061680089638933268032877)
    ·
      refine ⟨1148130033614599975512329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3061680089638933268032877 1148130033614599975512329)
      ·
        refine ⟨861097525210949981634247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1148130033614599975512329 861097525210949981634247)
        ·
          refine ⟨1291646287816424972451371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861097525210949981634247 1291646287816424972451371)
          ·
            refine ⟨1937469431724637458677057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291646287816424972451371 1937469431724637458677057)
            ·
              refine ⟨1453102073793478094007793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1937469431724637458677057 1453102073793478094007793)
              ·
                refine ⟨1089826555345108570505845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1453102073793478094007793 1089826555345108570505845)
                ·
                  refine ⟨102171239563603928484923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1089826555345108570505845 102171239563603928484923)
                  ·
                    rfl

theorem cell20_223850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_223850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223850 prefixEnd_223850 := by exact prefixLift 223850
  have htrace : WordTrace (prefixWord ++ tailWord_223850) baseStart_223850 baseEnd_223850 := by
    simpa [prefixWord, tailWord_223850, baseEnd_223850] using wordTrace_append hprefix tailTrace_223850
  have hstable : (prefixWord ++ tailWord_223850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223850).length < 2 ^ (prefixWord ++ tailWord_223850).sum := by decide
  have hdescent : baseEnd_223850 < baseStart_223850 := by decide
  rcases family_descends (prefixWord ++ tailWord_223850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223853 : List Nat := [1, 5, 1, 1, 3, 1, 1, 5, 2]
def baseStart_223853 : Nat := 118140960795 + 223853 * 2 ^ 59
def prefixEnd_223853 : Nat := 4983230072969 + 3 ^ 40 * 223853 * 2
def baseEnd_223853 : Nat := 102172608845349251384911

theorem tailTrace_223853 : CollatzResearch.WordTrace tailWord_223853 prefixEnd_223853 102172608845349251384911 := by
  unfold tailWord_223853
  simp only [CollatzResearch.WordTrace]
  refine ⟨8164589658026286893780213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5443059772017524595853475 8164589658026286893780213)
  ·
    refine ⟨765430280439964396291895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8164589658026286893780213 765430280439964396291895)
    ·
      refine ⟨1148145420659946594437843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 765430280439964396291895 1148145420659946594437843)
      ·
        refine ⟨1722218130989919891656765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1148145420659946594437843 1722218130989919891656765)
        ·
          refine ⟨645831799121219959371287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1722218130989919891656765 645831799121219959371287)
          ·
            refine ⟨968747698681829939056931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645831799121219959371287 968747698681829939056931)
            ·
              refine ⟨1453121548022744908585397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 968747698681829939056931 1453121548022744908585397)
              ·
                refine ⟨136230145127132335179881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1453121548022744908585397 136230145127132335179881)
                ·
                  refine ⟨102172608845349251384911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136230145127132335179881 102172608845349251384911)
                  ·
                    rfl

theorem cell20_223853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_223853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223853 prefixEnd_223853 := by exact prefixLift 223853
  have htrace : WordTrace (prefixWord ++ tailWord_223853) baseStart_223853 baseEnd_223853 := by
    simpa [prefixWord, tailWord_223853, baseEnd_223853] using wordTrace_append hprefix tailTrace_223853
  have hstable : (prefixWord ++ tailWord_223853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223853).length < 2 ^ (prefixWord ++ tailWord_223853).sum := by decide
  have hdescent : baseEnd_223853 < baseStart_223853 := by decide
  rcases family_descends (prefixWord ++ tailWord_223853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223895 : List Nat := [1, 1, 3, 3, 2, 1, 1, 4, 4]
def baseStart_223895 : Nat := 118140960795 + 223895 * 2 ^ 59
def prefixEnd_223895 : Nat := 4983230072969 + 3 ^ 40 * 223895 * 2
def baseEnd_223895 : Nat := 102191778789783771984739

theorem tailTrace_223895 : CollatzResearch.WordTrace tailWord_223895 prefixEnd_223895 102191778789783771984739 := by
  unfold tailWord_223895
  simp only [CollatzResearch.WordTrace]
  refine ⟨8166121523874128066809139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5444081015916085377872759 8166121523874128066809139)
  ·
    refine ⟨12249182285811192100213709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8166121523874128066809139 12249182285811192100213709)
    ·
      refine ⟨4593443357179197037580141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12249182285811192100213709 4593443357179197037580141)
      ·
        refine ⟨1722541258942198889092553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4593443357179197037580141 1722541258942198889092553)
        ·
          refine ⟨1291905944206649166819415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1722541258942198889092553 1291905944206649166819415)
          ·
            refine ⟨1937858916309973750229123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1291905944206649166819415 1937858916309973750229123)
            ·
              refine ⟨2906788374464960625343685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1937858916309973750229123 2906788374464960625343685)
              ·
                refine ⟨545022820212180117251941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2906788374464960625343685 545022820212180117251941)
                ·
                  refine ⟨102191778789783771984739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 545022820212180117251941 102191778789783771984739)
                  ·
                    rfl

theorem cell20_223895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 4].length) (baseStart_223895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223895 prefixEnd_223895 := by exact prefixLift 223895
  have htrace : WordTrace (prefixWord ++ tailWord_223895) baseStart_223895 baseEnd_223895 := by
    simpa [prefixWord, tailWord_223895, baseEnd_223895] using wordTrace_append hprefix tailTrace_223895
  have hstable : (prefixWord ++ tailWord_223895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223895).length < 2 ^ (prefixWord ++ tailWord_223895).sum := by decide
  have hdescent : baseEnd_223895 < baseStart_223895 := by decide
  rcases family_descends (prefixWord ++ tailWord_223895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223898 : List Nat := [3, 1, 1, 6, 1, 1, 1, 6]
def baseStart_223898 : Nat := 118140960795 + 223898 * 2 ^ 59
def prefixEnd_223898 : Nat := 4983230072969 + 3 ^ 40 * 223898 * 2
def baseEnd_223898 : Nat := 34064382690509698294909

theorem tailTrace_223898 : CollatzResearch.WordTrace tailWord_223898 prefixEnd_223898 34064382690509698294909 := by
  unfold tailWord_223898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2041557735715814894792087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5444153961908839719445565 2041557735715814894792087)
  ·
    refine ⟨3062336603573722342188131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2041557735715814894792087 3062336603573722342188131)
    ·
      refine ⟨4593504905360583513282197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3062336603573722342188131 4593504905360583513282197)
      ·
        refine ⟨215320542438777352185103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4593504905360583513282197 215320542438777352185103)
        ·
          refine ⟨322980813658166028277655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215320542438777352185103 322980813658166028277655)
          ·
            refine ⟨484471220487249042416483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 322980813658166028277655 484471220487249042416483)
            ·
              refine ⟨726706830730873563624725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 484471220487249042416483 726706830730873563624725)
              ·
                refine ⟨34064382690509698294909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 726706830730873563624725 34064382690509698294909)
                ·
                  rfl

theorem cell20_223898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_223898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223898 prefixEnd_223898 := by exact prefixLift 223898
  have htrace : WordTrace (prefixWord ++ tailWord_223898) baseStart_223898 baseEnd_223898 := by
    simpa [prefixWord, tailWord_223898, baseEnd_223898] using wordTrace_append hprefix tailTrace_223898
  have hstable : (prefixWord ++ tailWord_223898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223898).length < 2 ^ (prefixWord ++ tailWord_223898).sum := by decide
  have hdescent : baseEnd_223898 < baseStart_223898 := by decide
  rcases family_descends (prefixWord ++ tailWord_223898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_223981 : List Nat := [1, 5, 1, 2, 1, 1, 4, 2, 3]
def baseStart_223981 : Nat := 118140960795 + 223981 * 2 ^ 59
def prefixEnd_223981 : Nat := 4983230072969 + 3 ^ 40 * 223981 * 2
def baseEnd_223981 : Nat := 102231031533149695117721

theorem tailTrace_223981 : CollatzResearch.WordTrace tailWord_223981 prefixEnd_223981 102231031533149695117721 := by
  unfold tailWord_223981
  simp only [CollatzResearch.WordTrace]
  refine ⟨8169258201562564754439797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5446172134375043169626531 8169258201562564754439797)
  ·
    refine ⟨765867956396490445728731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8169258201562564754439797 765867956396490445728731)
    ·
      refine ⟨1148801934594735668593097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 765867956396490445728731 1148801934594735668593097)
      ·
        refine ⟨861601450946051751444823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1148801934594735668593097 861601450946051751444823)
        ·
          refine ⟨1292402176419077627167235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861601450946051751444823 1292402176419077627167235)
          ·
            refine ⟨1938603264628616440750853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1292402176419077627167235 1938603264628616440750853)
            ·
              refine ⟨363488112117865582640785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1938603264628616440750853 363488112117865582640785)
              ·
                refine ⟨272616084088399186980589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 363488112117865582640785 272616084088399186980589)
                ·
                  refine ⟨102231031533149695117721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272616084088399186980589 102231031533149695117721)
                  ·
                    rfl

theorem cell20_223981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_223981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_223981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_223981 prefixEnd_223981 := by exact prefixLift 223981
  have htrace : WordTrace (prefixWord ++ tailWord_223981) baseStart_223981 baseEnd_223981 := by
    simpa [prefixWord, tailWord_223981, baseEnd_223981] using wordTrace_append hprefix tailTrace_223981
  have hstable : (prefixWord ++ tailWord_223981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_223981).length < 2 ^ (prefixWord ++ tailWord_223981).sum := by decide
  have hdescent : baseEnd_223981 < baseStart_223981 := by decide
  rcases family_descends (prefixWord ++ tailWord_223981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224036 : List Nat := [2, 3, 1, 3, 3, 2, 1, 2, 3]
def baseStart_224036 : Nat := 118140960795 + 224036 * 2 ^ 59
def prefixEnd_224036 : Nat := 4983230072969 + 3 ^ 40 * 224036 * 2
def baseEnd_224036 : Nat := 102256135031813948284163

theorem tailTrace_224036 : CollatzResearch.WordTrace tailWord_224036 prefixEnd_224036 102256135031813948284163 := by
  unfold tailWord_224036
  simp only [CollatzResearch.WordTrace]
  refine ⟨4085632108181654573845981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5447509477575539431794641 4085632108181654573845981)
  ·
    refine ⟨1532112040568120465192243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4085632108181654573845981 1532112040568120465192243)
    ·
      refine ⟨2298168060852180697788365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1532112040568120465192243 2298168060852180697788365)
      ·
        refine ⟨861813022819567761670637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2298168060852180697788365 861813022819567761670637)
        ·
          refine ⟨323179883557337910626489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 861813022819567761670637 323179883557337910626489)
          ·
            refine ⟨242384912668003432969867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323179883557337910626489 242384912668003432969867)
            ·
              refine ⟨363577369002005149454801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242384912668003432969867 363577369002005149454801)
              ·
                refine ⟨272683026751503862091101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 363577369002005149454801 272683026751503862091101)
                ·
                  refine ⟨102256135031813948284163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272683026751503862091101 102256135031813948284163)
                  ·
                    rfl

theorem cell20_224036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_224036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224036 prefixEnd_224036 := by exact prefixLift 224036
  have htrace : WordTrace (prefixWord ++ tailWord_224036) baseStart_224036 baseEnd_224036 := by
    simpa [prefixWord, tailWord_224036, baseEnd_224036] using wordTrace_append hprefix tailTrace_224036
  have hstable : (prefixWord ++ tailWord_224036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224036).length < 2 ^ (prefixWord ++ tailWord_224036).sum := by decide
  have hdescent : baseEnd_224036 < baseStart_224036 := by decide
  rcases family_descends (prefixWord ++ tailWord_224036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224040 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 5]
def baseStart_224040 : Nat := 118140960795 + 224040 * 2 ^ 59
def prefixEnd_224040 : Nat := 4983230072969 + 3 ^ 40 * 224040 * 2
def baseEnd_224040 : Nat := 102257960740807712150813

theorem tailTrace_224040 : CollatzResearch.WordTrace tailWord_224040 prefixEnd_224040 102257960740807712150813 := by
  unfold tailWord_224040
  simp only [CollatzResearch.WordTrace]
  refine ⟨4085705054174408915418787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5447606738899211887225049 4085705054174408915418787)
  ·
    refine ⟨6128557581261613373128181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4085705054174408915418787 6128557581261613373128181)
    ·
      refine ⟨574552273243276253730767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6128557581261613373128181 574552273243276253730767)
      ·
        refine ⟨861828409864914380596151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574552273243276253730767 861828409864914380596151)
        ·
          refine ⟨1292742614797371570894227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 861828409864914380596151 1292742614797371570894227)
          ·
            refine ⟨1939113922196057356341341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1292742614797371570894227 1939113922196057356341341)
            ·
              refine ⟨727167720823521508628003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1939113922196057356341341 727167720823521508628003)
              ·
                refine ⟨1090751581235282262942005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727167720823521508628003 1090751581235282262942005)
                ·
                  refine ⟨102257960740807712150813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1090751581235282262942005 102257960740807712150813)
                  ·
                    rfl

theorem cell20_224040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_224040 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224040 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224040 prefixEnd_224040 := by exact prefixLift 224040
  have htrace : WordTrace (prefixWord ++ tailWord_224040) baseStart_224040 baseEnd_224040 := by
    simpa [prefixWord, tailWord_224040, baseEnd_224040] using wordTrace_append hprefix tailTrace_224040
  have hstable : (prefixWord ++ tailWord_224040).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224040).length < 2 ^ (prefixWord ++ tailWord_224040).sum := by decide
  have hdescent : baseEnd_224040 < baseStart_224040 := by decide
  rcases family_descends (prefixWord ++ tailWord_224040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224077 : List Nat := [1, 6, 1, 2, 2, 2, 1, 3, 2]
def baseStart_224077 : Nat := 118140960795 + 224077 * 2 ^ 59
def prefixEnd_224077 : Nat := 4983230072969 + 3 ^ 40 * 224077 * 2
def baseEnd_224077 : Nat := 102274848549000027917329

theorem tailTrace_224077 : CollatzResearch.WordTrace tailWord_224077 prefixEnd_224077 102274848549000027917329 := by
  unfold tailWord_224077
  simp only [CollatzResearch.WordTrace]
  refine ⟨8172759609214773149934485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5448506406143182099956323 8172759609214773149934485)
  ·
    refine ⟨383098106681942491403179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8172759609214773149934485 383098106681942491403179)
    ·
      refine ⟨574647160022913737104769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383098106681942491403179 574647160022913737104769)
      ·
        refine ⟨430985370017185302828577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 574647160022913737104769 430985370017185302828577)
        ·
          refine ⟨323239027512888977121433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 430985370017185302828577 323239027512888977121433)
          ·
            refine ⟨242429270634666732841075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323239027512888977121433 242429270634666732841075)
            ·
              refine ⟨363643905952000099261613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242429270634666732841075 363643905952000099261613)
              ·
                refine ⟨136366464732000037223105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 363643905952000099261613 136366464732000037223105)
                ·
                  refine ⟨102274848549000027917329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136366464732000037223105 102274848549000027917329)
                  ·
                    rfl

theorem cell20_224077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_224077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224077 prefixEnd_224077 := by exact prefixLift 224077
  have htrace : WordTrace (prefixWord ++ tailWord_224077) baseStart_224077 baseEnd_224077 := by
    simpa [prefixWord, tailWord_224077, baseEnd_224077] using wordTrace_append hprefix tailTrace_224077
  have hstable : (prefixWord ++ tailWord_224077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224077).length < 2 ^ (prefixWord ++ tailWord_224077).sum := by decide
  have hdescent : baseEnd_224077 < baseStart_224077 := by decide
  rcases family_descends (prefixWord ++ tailWord_224077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224098 : List Nat := [3, 3, 2, 1, 4, 1, 1, 1, 4]
def baseStart_224098 : Nat := 118140960795 + 224098 * 2 ^ 59
def prefixEnd_224098 : Nat := 4983230072969 + 3 ^ 40 * 224098 * 2
def baseEnd_224098 : Nat := 102284433521217288217243

theorem tailTrace_224098 : CollatzResearch.WordTrace tailWord_224098 prefixEnd_224098 102284433521217288217243 := by
  unfold tailWord_224098
  simp only [CollatzResearch.WordTrace]
  refine ⟨2043381385534673434112237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5449017028092462490965965 2043381385534673434112237)
  ·
    refine ⟨766268019575502537792089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2043381385534673434112237 766268019575502537792089)
    ·
      refine ⟨574701014681626903344067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 766268019575502537792089 574701014681626903344067)
      ·
        refine ⟨862051522022440355016101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 574701014681626903344067 862051522022440355016101)
        ·
          refine ⟨161634660379207566565519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 862051522022440355016101 161634660379207566565519)
          ·
            refine ⟨242451990568811349848279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161634660379207566565519 242451990568811349848279)
            ·
              refine ⟨363677985853217024772419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242451990568811349848279 363677985853217024772419)
              ·
                refine ⟨545516978779825537158629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 363677985853217024772419 545516978779825537158629)
                ·
                  refine ⟨102284433521217288217243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 545516978779825537158629 102284433521217288217243)
                  ·
                    rfl

theorem cell20_224098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_224098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224098 prefixEnd_224098 := by exact prefixLift 224098
  have htrace : WordTrace (prefixWord ++ tailWord_224098) baseStart_224098 baseEnd_224098 := by
    simpa [prefixWord, tailWord_224098, baseEnd_224098] using wordTrace_append hprefix tailTrace_224098
  have hstable : (prefixWord ++ tailWord_224098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224098).length < 2 ^ (prefixWord ++ tailWord_224098).sum := by decide
  have hdescent : baseEnd_224098 < baseStart_224098 := by decide
  rcases family_descends (prefixWord ++ tailWord_224098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224185 : List Nat := [1, 2, 1, 4, 2, 3, 3, 4]
def baseStart_224185 : Nat := 118140960795 + 224185 * 2 ^ 59
def prefixEnd_224185 : Nat := 4983230072969 + 3 ^ 40 * 224185 * 2
def baseEnd_224185 : Nat := 34108047563943884105629

theorem tailTrace_224185 : CollatzResearch.WordTrace tailWord_224185 prefixEnd_224185 34108047563943884105629 := by
  unfold tailWord_224185
  simp only [CollatzResearch.WordTrace]
  refine ⟨8176698692823507594866009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5451132461882338396577339 8176698692823507594866009)
  ·
    refine ⟨6132524019617630696149507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8176698692823507594866009 6132524019617630696149507)
    ·
      refine ⟨9198786029426446044224261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6132524019617630696149507 9198786029426446044224261)
      ·
        refine ⟨1724772380517458633292049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9198786029426446044224261 1724772380517458633292049)
        ·
          refine ⟨1293579285388093974969037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1724772380517458633292049 1293579285388093974969037)
          ·
            refine ⟨485092232020535240613389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1293579285388093974969037 485092232020535240613389)
            ·
              refine ⟨181909587007700715230021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 485092232020535240613389 181909587007700715230021)
              ·
                refine ⟨34108047563943884105629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181909587007700715230021 34108047563943884105629)
                ·
                  rfl

theorem cell20_224185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 4].length) (baseStart_224185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224185 prefixEnd_224185 := by exact prefixLift 224185
  have htrace : WordTrace (prefixWord ++ tailWord_224185) baseStart_224185 baseEnd_224185 := by
    simpa [prefixWord, tailWord_224185, baseEnd_224185] using wordTrace_append hprefix tailTrace_224185
  have hstable : (prefixWord ++ tailWord_224185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224185).length < 2 ^ (prefixWord ++ tailWord_224185).sum := by decide
  have hdescent : baseEnd_224185 < baseStart_224185 := by decide
  rcases family_descends (prefixWord ++ tailWord_224185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224198 : List Nat := [6, 1, 3, 1, 1, 1, 7]
def baseStart_224198 : Nat := 118140960795 + 224198 * 2 ^ 59
def prefixEnd_224198 : Nat := 4983230072969 + 3 ^ 40 * 224198 * 2
def baseEnd_224198 : Nat := 11370008471784598320389

theorem tailTrace_224198 : CollatzResearch.WordTrace tailWord_224198 prefixEnd_224198 11370008471784598320389 := by
  unfold tailWord_224198
  simp only [CollatzResearch.WordTrace]
  refine ⟨255536651305512837971539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5451448561184273876726165 255536651305512837971539)
  ·
    refine ⟨383304976958269256957309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255536651305512837971539 383304976958269256957309)
    ·
      refine ⟨143739366359350971358991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383304976958269256957309 143739366359350971358991)
      ·
        refine ⟨215609049539026457038487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143739366359350971358991 215609049539026457038487)
        ·
          refine ⟨323413574308539685557731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215609049539026457038487 323413574308539685557731)
          ·
            refine ⟨485120361462809528336597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323413574308539685557731 485120361462809528336597)
            ·
              refine ⟨11370008471784598320389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 485120361462809528336597 11370008471784598320389)
              ·
                rfl

theorem cell20_224198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 7].length) (baseStart_224198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224198 prefixEnd_224198 := by exact prefixLift 224198
  have htrace : WordTrace (prefixWord ++ tailWord_224198) baseStart_224198 baseEnd_224198 := by
    simpa [prefixWord, tailWord_224198, baseEnd_224198] using wordTrace_append hprefix tailTrace_224198
  have hstable : (prefixWord ++ tailWord_224198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224198).length < 2 ^ (prefixWord ++ tailWord_224198).sum := by decide
  have hdescent : baseEnd_224198 < baseStart_224198 := by decide
  rcases family_descends (prefixWord ++ tailWord_224198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224205 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 5]
def baseStart_224205 : Nat := 118140960795 + 224205 * 2 ^ 59
def prefixEnd_224205 : Nat := 4983230072969 + 3 ^ 40 * 224205 * 2
def baseEnd_224205 : Nat := 102333271236800471650139

theorem tailTrace_224205 : CollatzResearch.WordTrace tailWord_224205 prefixEnd_224205 102333271236800471650139 := by
  unfold tailWord_224205
  simp only [CollatzResearch.WordTrace]
  refine ⟨8177428152751051010594069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5451618768500700673729379 8177428152751051010594069)
  ·
    refine ⟨383316944660205516121597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 8177428152751051010594069 383316944660205516121597)
    ·
      refine ⟨143743854247577068545599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 383316944660205516121597 143743854247577068545599)
      ·
        refine ⟨215615781371365602818399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143743854247577068545599 215615781371365602818399)
        ·
          refine ⟨323423672057048404227599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215615781371365602818399 323423672057048404227599)
          ·
            refine ⟨485135508085572606341399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323423672057048404227599 485135508085572606341399)
            ·
              refine ⟨727703262128358909512099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485135508085572606341399 727703262128358909512099)
              ·
                refine ⟨1091554893192538364268149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 727703262128358909512099 1091554893192538364268149)
                ·
                  refine ⟨102333271236800471650139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1091554893192538364268149 102333271236800471650139)
                  ·
                    rfl

theorem cell20_224205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_224205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224205 prefixEnd_224205 := by exact prefixLift 224205
  have htrace : WordTrace (prefixWord ++ tailWord_224205) baseStart_224205 baseEnd_224205 := by
    simpa [prefixWord, tailWord_224205, baseEnd_224205] using wordTrace_append hprefix tailTrace_224205
  have hstable : (prefixWord ++ tailWord_224205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224205).length < 2 ^ (prefixWord ++ tailWord_224205).sum := by decide
  have hdescent : baseEnd_224205 < baseStart_224205 := by decide
  rcases family_descends (prefixWord ++ tailWord_224205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224206 : List Nat := [4, 1, 1, 1, 2, 4, 7]
def baseStart_224206 : Nat := 118140960795 + 224206 * 2 ^ 59
def prefixEnd_224206 : Nat := 4983230072969 + 3 ^ 40 * 224206 * 2
def baseEnd_224206 : Nat := 11370414184894323624089

theorem tailTrace_224206 : CollatzResearch.WordTrace tailWord_224206 prefixEnd_224206 11370414184894323624089 := by
  unfold tailWord_224206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1022183078218428522672559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5451643083831618787586981 1022183078218428522672559)
  ·
    refine ⟨1533274617327642784008839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1022183078218428522672559 1533274617327642784008839)
    ·
      refine ⟨2299911925991464176013259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1533274617327642784008839 2299911925991464176013259)
      ·
        refine ⟨3449867888987196264019889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2299911925991464176013259 3449867888987196264019889)
        ·
          refine ⟨2587400916740397198014917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3449867888987196264019889 2587400916740397198014917)
          ·
            refine ⟨485137671888824474627797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2587400916740397198014917 485137671888824474627797)
            ·
              refine ⟨11370414184894323624089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 485137671888824474627797 11370414184894323624089)
              ·
                rfl

theorem cell20_224206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 7].length) (baseStart_224206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224206 prefixEnd_224206 := by exact prefixLift 224206
  have htrace : WordTrace (prefixWord ++ tailWord_224206) baseStart_224206 baseEnd_224206 := by
    simpa [prefixWord, tailWord_224206, baseEnd_224206] using wordTrace_append hprefix tailTrace_224206
  have hstable : (prefixWord ++ tailWord_224206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224206).length < 2 ^ (prefixWord ++ tailWord_224206).sum := by decide
  have hdescent : baseEnd_224206 < baseStart_224206 := by decide
  rcases family_descends (prefixWord ++ tailWord_224206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224216 : List Nat := [2, 1, 2, 2, 2, 3, 2, 4, 2]
def baseStart_224216 : Nat := 118140960795 + 224216 * 2 ^ 59
def prefixEnd_224216 : Nat := 4983230072969 + 3 ^ 40 * 224216 * 2
def baseEnd_224216 : Nat := 102338291936533322283427

theorem tailTrace_224216 : CollatzResearch.WordTrace tailWord_224216 prefixEnd_224216 102338291936533322283427 := by
  unfold tailWord_224216
  simp only [CollatzResearch.WordTrace]
  refine ⟨4088914677855599944622251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5451886237140799926163001 4088914677855599944622251)
  ·
    refine ⟨6133372016783399916933377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4088914677855599944622251 6133372016783399916933377)
    ·
      refine ⟨4600029012587549937700033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6133372016783399916933377 4600029012587549937700033)
      ·
        refine ⟨3450021759440662453275025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4600029012587549937700033 3450021759440662453275025)
        ·
          refine ⟨2587516319580496839956269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3450021759440662453275025 2587516319580496839956269)
          ·
            refine ⟨970318619842686314983601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2587516319580496839956269 970318619842686314983601)
            ·
              refine ⟨727738964882014736237701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 970318619842686314983601 727738964882014736237701)
              ·
                refine ⟨136451055915377763044569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 727738964882014736237701 136451055915377763044569)
                ·
                  refine ⟨102338291936533322283427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136451055915377763044569 102338291936533322283427)
                  ·
                    rfl

theorem cell20_224216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 2].length) (baseStart_224216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224216 prefixEnd_224216 := by exact prefixLift 224216
  have htrace : WordTrace (prefixWord ++ tailWord_224216) baseStart_224216 baseEnd_224216 := by
    simpa [prefixWord, tailWord_224216, baseEnd_224216] using wordTrace_append hprefix tailTrace_224216
  have hstable : (prefixWord ++ tailWord_224216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224216).length < 2 ^ (prefixWord ++ tailWord_224216).sum := by decide
  have hdescent : baseEnd_224216 < baseStart_224216 := by decide
  rcases family_descends (prefixWord ++ tailWord_224216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224282 : List Nat := [3, 1, 1, 3, 1, 2, 4, 5]
def baseStart_224282 : Nat := 118140960795 + 224282 * 2 ^ 59
def prefixEnd_224282 : Nat := 4983230072969 + 3 ^ 40 * 224282 * 2
def baseEnd_224282 : Nat := 34122805378310142027719

theorem tailTrace_224282 : CollatzResearch.WordTrace tailWord_224282 prefixEnd_224282 34122805378310142027719 := by
  unfold tailWord_224282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2045059143368023290286775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5453491048981395440764733 2045059143368023290286775)
  ·
    refine ⟨3067588715052034935430163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2045059143368023290286775 3067588715052034935430163)
    ·
      refine ⟨4601383072578052403145245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3067588715052034935430163 4601383072578052403145245)
      ·
        refine ⟨1725518652216769651179467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4601383072578052403145245 1725518652216769651179467)
        ·
          refine ⟨2588277978325154476769201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1725518652216769651179467 2588277978325154476769201)
          ·
            refine ⟨1941208483743865857576901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2588277978325154476769201 1941208483743865857576901)
            ·
              refine ⟨363976590701974848295669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1941208483743865857576901 363976590701974848295669)
              ·
                refine ⟨34122805378310142027719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 363976590701974848295669 34122805378310142027719)
                ·
                  rfl

theorem cell20_224282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_224282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224282 prefixEnd_224282 := by exact prefixLift 224282
  have htrace : WordTrace (prefixWord ++ tailWord_224282) baseStart_224282 baseEnd_224282 := by
    simpa [prefixWord, tailWord_224282, baseEnd_224282] using wordTrace_append hprefix tailTrace_224282
  have hstable : (prefixWord ++ tailWord_224282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224282).length < 2 ^ (prefixWord ++ tailWord_224282).sum := by decide
  have hdescent : baseEnd_224282 < baseStart_224282 := by decide
  rcases family_descends (prefixWord ++ tailWord_224282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224285 : List Nat := [1, 4, 2, 2, 3, 1, 1, 3, 3]
def baseStart_224285 : Nat := 118140960795 + 224285 * 2 ^ 59
def prefixEnd_224285 : Nat := 4983230072969 + 3 ^ 40 * 224285 * 2
def baseEnd_224285 : Nat := 102369785416675748983145

theorem tailTrace_224285 : CollatzResearch.WordTrace tailWord_224285 prefixEnd_224285 102369785416675748983145 := by
  unfold tailWord_224285
  simp only [CollatzResearch.WordTrace]
  refine ⟨8180345992461224673506309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5453563994974149782337539 8180345992461224673506309)
  ·
    refine ⟨1533814873586479626282433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8180345992461224673506309 1533814873586479626282433)
    ·
      refine ⟨1150361155189859719711825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1533814873586479626282433 1150361155189859719711825)
      ·
        refine ⟨862770866392394789783869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1150361155189859719711825 862770866392394789783869)
        ·
          refine ⟨323539074897148046168951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 862770866392394789783869 323539074897148046168951)
          ·
            refine ⟨485308612345722069253427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323539074897148046168951 485308612345722069253427)
            ·
              refine ⟨727962918518583103880141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485308612345722069253427 727962918518583103880141)
              ·
                refine ⟨272986094444468663955053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 727962918518583103880141 272986094444468663955053)
                ·
                  refine ⟨102369785416675748983145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 272986094444468663955053 102369785416675748983145)
                  ·
                    rfl

theorem cell20_224285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_224285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224285 prefixEnd_224285 := by exact prefixLift 224285
  have htrace : WordTrace (prefixWord ++ tailWord_224285) baseStart_224285 baseEnd_224285 := by
    simpa [prefixWord, tailWord_224285, baseEnd_224285] using wordTrace_append hprefix tailTrace_224285
  have hstable : (prefixWord ++ tailWord_224285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224285).length < 2 ^ (prefixWord ++ tailWord_224285).sum := by decide
  have hdescent : baseEnd_224285 < baseStart_224285 := by decide
  rcases family_descends (prefixWord ++ tailWord_224285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224326 : List Nat := [6, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_224326 : Nat := 118140960795 + 224326 * 2 ^ 59
def prefixEnd_224326 : Nat := 4983230072969 + 3 ^ 40 * 224326 * 2
def baseEnd_224326 : Nat := 102388498933861828616311

theorem tailTrace_224326 : CollatzResearch.WordTrace tailWord_224326 prefixEnd_224326 102388498933861828616311 := by
  unfold tailWord_224326
  simp only [CollatzResearch.WordTrace]
  refine ⟨255682543291021521117151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5454560923541792450499221 255682543291021521117151)
  ·
    refine ⟨383523814936532281675727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 255682543291021521117151 383523814936532281675727)
    ·
      refine ⟨575285722404798422513591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 383523814936532281675727 575285722404798422513591)
      ·
        refine ⟨862928583607197633770387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575285722404798422513591 862928583607197633770387)
        ·
          refine ⟨1294392875410796450655581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 862928583607197633770387 1294392875410796450655581)
          ·
            refine ⟨485397328279048668995843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1294392875410796450655581 485397328279048668995843)
            ·
              refine ⟨728095992418573003493765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485397328279048668995843 728095992418573003493765)
              ·
                refine ⟨136517998578482438155081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 728095992418573003493765 136517998578482438155081)
                ·
                  refine ⟨102388498933861828616311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136517998578482438155081 102388498933861828616311)
                  ·
                    rfl

theorem cell20_224326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_224326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224326 prefixEnd_224326 := by exact prefixLift 224326
  have htrace : WordTrace (prefixWord ++ tailWord_224326) baseStart_224326 baseEnd_224326 := by
    simpa [prefixWord, tailWord_224326, baseEnd_224326] using wordTrace_append hprefix tailTrace_224326
  have hstable : (prefixWord ++ tailWord_224326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224326).length < 2 ^ (prefixWord ++ tailWord_224326).sum := by decide
  have hdescent : baseEnd_224326 < baseStart_224326 := by decide
  rcases family_descends (prefixWord ++ tailWord_224326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224354 : List Nat := [3, 3, 2, 2, 1, 2, 3, 4]
def baseStart_224354 : Nat := 118140960795 + 224354 * 2 ^ 59
def prefixEnd_224354 : Nat := 4983230072969 + 3 ^ 40 * 224354 * 2
def baseEnd_224354 : Nat := 34133759632272725227621

theorem tailTrace_224354 : CollatzResearch.WordTrace tailWord_224354 prefixEnd_224354 34133759632272725227621 := by
  unfold tailWord_224354
  simp only [CollatzResearch.WordTrace]
  refine ⟨2045715657302812364442029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5455241752807499638512077 2045715657302812364442029)
  ·
    refine ⟨767143371488554636665761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2045715657302812364442029 767143371488554636665761)
    ·
      refine ⟨575357528616415977499321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 767143371488554636665761 575357528616415977499321)
      ·
        refine ⟨431518146462311983124491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575357528616415977499321 431518146462311983124491)
        ·
          refine ⟨647277219693467974686737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431518146462311983124491 647277219693467974686737)
          ·
            refine ⟨485457914770100981015053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 647277219693467974686737 485457914770100981015053)
            ·
              refine ⟨182046718038787867880645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 485457914770100981015053 182046718038787867880645)
              ·
                refine ⟨34133759632272725227621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182046718038787867880645 34133759632272725227621)
                ·
                  rfl

theorem cell20_224354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_224354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224354 prefixEnd_224354 := by exact prefixLift 224354
  have htrace : WordTrace (prefixWord ++ tailWord_224354) baseStart_224354 baseEnd_224354 := by
    simpa [prefixWord, tailWord_224354, baseEnd_224354] using wordTrace_append hprefix tailTrace_224354
  have hstable : (prefixWord ++ tailWord_224354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224354).length < 2 ^ (prefixWord ++ tailWord_224354).sum := by decide
  have hdescent : baseEnd_224354 < baseStart_224354 := by decide
  rcases family_descends (prefixWord ++ tailWord_224354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224368 : List Nat := [2, 1, 1, 1, 5, 1, 4, 3, 2]
def baseStart_224368 : Nat := 118140960795 + 224368 * 2 ^ 59
def prefixEnd_224368 : Nat := 4983230072969 + 3 ^ 40 * 224368 * 2
def baseEnd_224368 : Nat := 102407668878296349216139

theorem tailTrace_224368 : CollatzResearch.WordTrace tailWord_224368 prefixEnd_224368 102407668878296349216139 := by
  unfold tailWord_224368
  simp only [CollatzResearch.WordTrace]
  refine ⟨4091686625580264924388879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5455582167440353232518505 4091686625580264924388879)
  ·
    refine ⟨6137529938370397386583319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4091686625580264924388879 6137529938370397386583319)
    ·
      refine ⟨9206294907555596079874979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6137529938370397386583319 9206294907555596079874979)
      ·
        refine ⟨13809442361333394119812469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9206294907555596079874979 13809442361333394119812469)
        ·
          refine ⟨1294635221375005698732419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13809442361333394119812469 1294635221375005698732419)
          ·
            refine ⟨1941952832062508548098629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1294635221375005698732419 1941952832062508548098629)
            ·
              refine ⟨364116156011720352768493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1941952832062508548098629 364116156011720352768493)
              ·
                refine ⟨136543558504395132288185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364116156011720352768493 136543558504395132288185)
                ·
                  refine ⟨102407668878296349216139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136543558504395132288185 102407668878296349216139)
                  ·
                    rfl

theorem cell20_224368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 3, 2].length) (baseStart_224368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224368 prefixEnd_224368 := by exact prefixLift 224368
  have htrace : WordTrace (prefixWord ++ tailWord_224368) baseStart_224368 baseEnd_224368 := by
    simpa [prefixWord, tailWord_224368, baseEnd_224368] using wordTrace_append hprefix tailTrace_224368
  have hstable : (prefixWord ++ tailWord_224368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224368).length < 2 ^ (prefixWord ++ tailWord_224368).sum := by decide
  have hdescent : baseEnd_224368 < baseStart_224368 := by decide
  rcases family_descends (prefixWord ++ tailWord_224368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224403 : List Nat := [1, 1, 1, 2, 1, 2, 4, 5, 3]
def baseStart_224403 : Nat := 118140960795 + 224403 * 2 ^ 59
def prefixEnd_224403 : Nat := 4983230072969 + 3 ^ 40 * 224403 * 2
def baseEnd_224403 : Nat := 102423643831991783049329

theorem tailTrace_224403 : CollatzResearch.WordTrace tailWord_224403 prefixEnd_224403 102423643831991783049329 := by
  unfold tailWord_224403
  simp only [CollatzResearch.WordTrace]
  refine ⟨8184649806033730826301863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5456433204022487217534575 8184649806033730826301863)
  ·
    refine ⟨12276974709050596239452795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8184649806033730826301863 12276974709050596239452795)
    ·
      refine ⟨18415462063575894359179193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12276974709050596239452795 18415462063575894359179193)
      ·
        refine ⟨13811596547681920769384395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18415462063575894359179193 13811596547681920769384395)
        ·
          refine ⟨20717394821522881154076593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13811596547681920769384395 20717394821522881154076593)
          ·
            refine ⟨15538046116142160865557445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20717394821522881154076593 15538046116142160865557445)
            ·
              refine ⟨2913383646776655162292021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15538046116142160865557445 2913383646776655162292021)
              ·
                refine ⟨273129716885311421464877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2913383646776655162292021 273129716885311421464877)
                ·
                  refine ⟨102423643831991783049329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273129716885311421464877 102423643831991783049329)
                  ·
                    rfl

theorem cell20_224403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 5, 3].length) (baseStart_224403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224403 prefixEnd_224403 := by exact prefixLift 224403
  have htrace : WordTrace (prefixWord ++ tailWord_224403) baseStart_224403 baseEnd_224403 := by
    simpa [prefixWord, tailWord_224403, baseEnd_224403] using wordTrace_append hprefix tailTrace_224403
  have hstable : (prefixWord ++ tailWord_224403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224403).length < 2 ^ (prefixWord ++ tailWord_224403).sum := by decide
  have hdescent : baseEnd_224403 < baseStart_224403 := by decide
  rcases family_descends (prefixWord ++ tailWord_224403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224423 : List Nat := [1, 1, 6, 2, 1, 1, 3, 3, 2]
def baseStart_224423 : Nat := 118140960795 + 224423 * 2 ^ 59
def prefixEnd_224423 : Nat := 4983230072969 + 3 ^ 40 * 224423 * 2
def baseEnd_224423 : Nat := 102432772376960602382581

theorem tailTrace_224423 : CollatzResearch.WordTrace tailWord_224423 prefixEnd_224423 102432772376960602382581 := by
  unfold tailWord_224423
  simp only [CollatzResearch.WordTrace]
  refine ⟨8185379265961274242029923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5456919510640849494686615 8185379265961274242029923)
  ·
    refine ⟨12278068898941911363044885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8185379265961274242029923 12278068898941911363044885)
    ·
      refine ⟨575534479637902095142729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12278068898941911363044885 575534479637902095142729)
      ·
        refine ⟨431650859728426571357047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575534479637902095142729 431650859728426571357047)
        ·
          refine ⟨647476289592639857035571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431650859728426571357047 647476289592639857035571)
          ·
            refine ⟨971214434388959785553357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 647476289592639857035571 971214434388959785553357)
            ·
              refine ⟨364205412895859919582509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 971214434388959785553357 364205412895859919582509)
              ·
                refine ⟨136577029835947469843441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 364205412895859919582509 136577029835947469843441)
                ·
                  refine ⟨102432772376960602382581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136577029835947469843441 102432772376960602382581)
                  ·
                    rfl

theorem cell20_224423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 3, 2].length) (baseStart_224423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224423 prefixEnd_224423 := by exact prefixLift 224423
  have htrace : WordTrace (prefixWord ++ tailWord_224423) baseStart_224423 baseEnd_224423 := by
    simpa [prefixWord, tailWord_224423, baseEnd_224423] using wordTrace_append hprefix tailTrace_224423
  have hstable : (prefixWord ++ tailWord_224423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224423).length < 2 ^ (prefixWord ++ tailWord_224423).sum := by decide
  have hdescent : baseEnd_224423 < baseStart_224423 := by decide
  rcases family_descends (prefixWord ++ tailWord_224423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224434 : List Nat := [3, 2, 1, 1, 1, 6, 6]
def baseStart_224434 : Nat := 118140960795 + 224434 * 2 ^ 59
def prefixEnd_224434 : Nat := 4983230072969 + 3 ^ 40 * 224434 * 2
def baseEnd_224434 : Nat := 11381977008521494779541

theorem tailTrace_224434 : CollatzResearch.WordTrace tailWord_224434 prefixEnd_224434 11381977008521494779541 := by
  unfold tailWord_224434
  simp only [CollatzResearch.WordTrace]
  refine ⟨2046445117230355780170089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5457186979280948747120237 2046445117230355780170089)
  ·
    refine ⟨1534833837922766835127567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2046445117230355780170089 1534833837922766835127567)
    ·
      refine ⟨2302250756884150252691351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1534833837922766835127567 2302250756884150252691351)
      ·
        refine ⟨3453376135326225379037027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2302250756884150252691351 3453376135326225379037027)
        ·
          refine ⟨5180064202989338068555541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3453376135326225379037027 5180064202989338068555541)
          ·
            refine ⟨242815509515125221963541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5180064202989338068555541 242815509515125221963541)
            ·
              refine ⟨11381977008521494779541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 242815509515125221963541 11381977008521494779541)
              ·
                rfl

theorem cell20_224434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 6].length) (baseStart_224434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224434 prefixEnd_224434 := by exact prefixLift 224434
  have htrace : WordTrace (prefixWord ++ tailWord_224434) baseStart_224434 baseEnd_224434 := by
    simpa [prefixWord, tailWord_224434, baseEnd_224434] using wordTrace_append hprefix tailTrace_224434
  have hstable : (prefixWord ++ tailWord_224434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224434).length < 2 ^ (prefixWord ++ tailWord_224434).sum := by decide
  have hdescent : baseEnd_224434 < baseStart_224434 := by decide
  rcases family_descends (prefixWord ++ tailWord_224434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224441 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 5]
def baseStart_224441 : Nat := 118140960795 + 224441 * 2 ^ 59
def prefixEnd_224441 : Nat := 4983230072969 + 3 ^ 40 * 224441 * 2
def baseEnd_224441 : Nat := 102440988067432539782507

theorem tailTrace_224441 : CollatzResearch.WordTrace tailWord_224441 prefixEnd_224441 102440988067432539782507 := by
  unfold tailWord_224441
  simp only [CollatzResearch.WordTrace]
  refine ⟨8186035779896063316185177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5457357186597375544123451 8186035779896063316185177)
  ·
    refine ⟨6139526834922047487138883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8186035779896063316185177 6139526834922047487138883)
    ·
      refine ⟨9209290252383071230708325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6139526834922047487138883 9209290252383071230708325)
      ·
        refine ⟨1726741922321825855757811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9209290252383071230708325 1726741922321825855757811)
        ·
          refine ⟨2590112883482738783636717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1726741922321825855757811 2590112883482738783636717)
          ·
            refine ⟨971292331306027043863769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2590112883482738783636717 971292331306027043863769)
            ·
              refine ⟨728469248479520282897827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 971292331306027043863769 728469248479520282897827)
              ·
                refine ⟨1092703872719280424346741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 728469248479520282897827 1092703872719280424346741)
                ·
                  refine ⟨102440988067432539782507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1092703872719280424346741 102440988067432539782507)
                  ·
                    rfl

theorem cell20_224441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_224441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224441 prefixEnd_224441 := by exact prefixLift 224441
  have htrace : WordTrace (prefixWord ++ tailWord_224441) baseStart_224441 baseEnd_224441 := by
    simpa [prefixWord, tailWord_224441, baseEnd_224441] using wordTrace_append hprefix tailTrace_224441
  have hstable : (prefixWord ++ tailWord_224441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224441).length < 2 ^ (prefixWord ++ tailWord_224441).sum := by decide
  have hdescent : baseEnd_224441 < baseStart_224441 := by decide
  rcases family_descends (prefixWord ++ tailWord_224441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224444 : List Nat := [2, 2, 2, 3, 2, 3, 1, 1, 4]
def baseStart_224444 : Nat := 118140960795 + 224444 * 2 ^ 59
def prefixEnd_224444 : Nat := 4983230072969 + 3 ^ 40 * 224444 * 2
def baseEnd_224444 : Nat := 102442357349177862682495

theorem tailTrace_224444 : CollatzResearch.WordTrace tailWord_224444 prefixEnd_224444 102442357349177862682495 := by
  unfold tailWord_224444
  simp only [CollatzResearch.WordTrace]
  refine ⟨4093072599442597414272193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5457430132590129885696257 4093072599442597414272193)
  ·
    refine ⟨3069804449581948060704145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4093072599442597414272193 3069804449581948060704145)
    ·
      refine ⟨2302353337186461045528109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3069804449581948060704145 2302353337186461045528109)
      ·
        refine ⟨863382501444922892073041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2302353337186461045528109 863382501444922892073041)
        ·
          refine ⟨647536876083692169054781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 863382501444922892073041 647536876083692169054781)
          ·
            refine ⟨242826328531384563395543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 647536876083692169054781 242826328531384563395543)
            ·
              refine ⟨364239492797076845093315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242826328531384563395543 364239492797076845093315)
              ·
                refine ⟨546359239195615267639973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 364239492797076845093315 546359239195615267639973)
                ·
                  refine ⟨102442357349177862682495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 546359239195615267639973 102442357349177862682495)
                  ·
                    rfl

theorem cell20_224444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_224444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224444 prefixEnd_224444 := by exact prefixLift 224444
  have htrace : WordTrace (prefixWord ++ tailWord_224444) baseStart_224444 baseEnd_224444 := by
    simpa [prefixWord, tailWord_224444, baseEnd_224444] using wordTrace_append hprefix tailTrace_224444
  have hstable : (prefixWord ++ tailWord_224444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224444).length < 2 ^ (prefixWord ++ tailWord_224444).sum := by decide
  have hdescent : baseEnd_224444 < baseStart_224444 := by decide
  rcases family_descends (prefixWord ++ tailWord_224444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224450 : List Nat := [3, 5, 1, 1, 2, 2, 2, 1, 3]
def baseStart_224450 : Nat := 118140960795 + 224450 * 2 ^ 59
def prefixEnd_224450 : Nat := 4983230072969 + 3 ^ 40 * 224450 * 2
def baseEnd_224450 : Nat := 102445095912668508482471

theorem tailTrace_224450 : CollatzResearch.WordTrace tailWord_224450 prefixEnd_224450 102445095912668508482471 := by
  unfold tailWord_224450
  simp only [CollatzResearch.WordTrace]
  refine ⟨2046591009215864463315701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5457576024575638568841869 2046591009215864463315701)
  ·
    refine ⟨191867907113987293435847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2046591009215864463315701 191867907113987293435847)
    ·
      refine ⟨287801860670980940153771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191867907113987293435847 287801860670980940153771)
      ·
        refine ⟨431702791006471410230657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287801860670980940153771 431702791006471410230657)
        ·
          refine ⟨323777093254853557672993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 431702791006471410230657 323777093254853557672993)
          ·
            refine ⟨242832819941140168254745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323777093254853557672993 242832819941140168254745)
            ·
              refine ⟨182124614955855126191059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242832819941140168254745 182124614955855126191059)
              ·
                refine ⟨273186922433782689286589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182124614955855126191059 273186922433782689286589)
                ·
                  refine ⟨102445095912668508482471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273186922433782689286589 102445095912668508482471)
                  ·
                    rfl

theorem cell20_224450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_224450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224450 prefixEnd_224450 := by exact prefixLift 224450
  have htrace : WordTrace (prefixWord ++ tailWord_224450) baseStart_224450 baseEnd_224450 := by
    simpa [prefixWord, tailWord_224450, baseEnd_224450] using wordTrace_append hprefix tailTrace_224450
  have hstable : (prefixWord ++ tailWord_224450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224450).length < 2 ^ (prefixWord ++ tailWord_224450).sum := by decide
  have hdescent : baseEnd_224450 < baseStart_224450 := by decide
  rcases family_descends (prefixWord ++ tailWord_224450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224458 : List Nat := [3, 1, 2, 1, 3, 3, 1, 3, 3]
def baseStart_224458 : Nat := 118140960795 + 224458 * 2 ^ 59
def prefixEnd_224458 : Nat := 4983230072969 + 3 ^ 40 * 224458 * 2
def baseEnd_224458 : Nat := 102448747330656036215771

theorem tailTrace_224458 : CollatzResearch.WordTrace tailWord_224458 prefixEnd_224458 102448747330656036215771 := by
  unfold tailWord_224458
  simp only [CollatzResearch.WordTrace]
  refine ⟨2046663955208618804888507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5457770547222983479702685 2046663955208618804888507)
  ·
    refine ⟨3069995932812928207332761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2046663955208618804888507 3069995932812928207332761)
    ·
      refine ⟨2302496949609696155499571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3069995932812928207332761 2302496949609696155499571)
      ·
        refine ⟨3453745424414544233249357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2302496949609696155499571 3453745424414544233249357)
        ·
          refine ⟨1295154534155454087468509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3453745424414544233249357 1295154534155454087468509)
          ·
            refine ⟨485682950308295282800691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1295154534155454087468509 485682950308295282800691)
            ·
              refine ⟨728524425462442924201037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 485682950308295282800691 728524425462442924201037)
              ·
                refine ⟨273196659548416096575389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 728524425462442924201037 273196659548416096575389)
                ·
                  refine ⟨102448747330656036215771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273196659548416096575389 102448747330656036215771)
                  ·
                    rfl

theorem cell20_224458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_224458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224458 prefixEnd_224458 := by exact prefixLift 224458
  have htrace : WordTrace (prefixWord ++ tailWord_224458) baseStart_224458 baseEnd_224458 := by
    simpa [prefixWord, tailWord_224458, baseEnd_224458] using wordTrace_append hprefix tailTrace_224458
  have hstable : (prefixWord ++ tailWord_224458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224458).length < 2 ^ (prefixWord ++ tailWord_224458).sum := by decide
  have hdescent : baseEnd_224458 < baseStart_224458 := by decide
  rcases family_descends (prefixWord ++ tailWord_224458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224499 : List Nat := [1, 1, 1, 2, 2, 7, 2, 2, 2]
def baseStart_224499 : Nat := 118140960795 + 224499 * 2 ^ 59
def prefixEnd_224499 : Nat := 4983230072969 + 3 ^ 40 * 224499 * 2
def baseEnd_224499 : Nat := 102467460847842115848937

theorem tailTrace_224499 : CollatzResearch.WordTrace tailWord_224499 prefixEnd_224499 102467460847842115848937 := by
  unfold tailWord_224499
  simp only [CollatzResearch.WordTrace]
  refine ⟨8188151213685939221796551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5458767475790626147864367 8188151213685939221796551)
  ·
    refine ⟨12282226820528908832694827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8188151213685939221796551 12282226820528908832694827)
    ·
      refine ⟨18423340230793363249042241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12282226820528908832694827 18423340230793363249042241)
      ·
        refine ⟨13817505173095022436781681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18423340230793363249042241 13817505173095022436781681)
        ·
          refine ⟨10363128879821266827586261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13817505173095022436781681 10363128879821266827586261)
          ·
            refine ⟨242885833120810941271553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 10363128879821266827586261 242885833120810941271553)
            ·
              refine ⟨182164374840608205953665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 242885833120810941271553 182164374840608205953665)
              ·
                refine ⟨136623281130456154465249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182164374840608205953665 136623281130456154465249)
                ·
                  refine ⟨102467460847842115848937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136623281130456154465249 102467460847842115848937)
                  ·
                    rfl

theorem cell20_224499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 2, 2].length) (baseStart_224499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224499 prefixEnd_224499 := by exact prefixLift 224499
  have htrace : WordTrace (prefixWord ++ tailWord_224499) baseStart_224499 baseEnd_224499 := by
    simpa [prefixWord, tailWord_224499, baseEnd_224499] using wordTrace_append hprefix tailTrace_224499
  have hstable : (prefixWord ++ tailWord_224499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224499).length < 2 ^ (prefixWord ++ tailWord_224499).sum := by decide
  have hdescent : baseEnd_224499 < baseStart_224499 := by decide
  rcases family_descends (prefixWord ++ tailWord_224499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224503 : List Nat := [1, 1, 3, 1, 1, 1, 2, 8, 2]
def baseStart_224503 : Nat := 118140960795 + 224503 * 2 ^ 59
def prefixEnd_224503 : Nat := 4983230072969 + 3 ^ 40 * 224503 * 2
def baseEnd_224503 : Nat := 102469286556835879715587

theorem tailTrace_224503 : CollatzResearch.WordTrace tailWord_224503 prefixEnd_224503 102469286556835879715587 := by
  unfold tailWord_224503
  simp only [CollatzResearch.WordTrace]
  refine ⟨8188297105671447904942163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5458864737114298603294775 8188297105671447904942163)
  ·
    refine ⟨12282445658507171857413245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8188297105671447904942163 12282445658507171857413245)
    ·
      refine ⟨4605917121940189446529967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12282445658507171857413245 4605917121940189446529967)
      ·
        refine ⟨6908875682910284169794951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4605917121940189446529967 6908875682910284169794951)
        ·
          refine ⟨10363313524365426254692427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6908875682910284169794951 10363313524365426254692427)
          ·
            refine ⟨15544970286548139382038641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10363313524365426254692427 15544970286548139382038641)
            ·
              refine ⟨11658727714911104536528981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15544970286548139382038641 11658727714911104536528981)
              ·
                refine ⟨136625715409114506287449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11658727714911104536528981 136625715409114506287449)
                ·
                  refine ⟨102469286556835879715587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136625715409114506287449 102469286556835879715587)
                  ·
                    rfl

theorem cell20_224503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 8, 2].length) (baseStart_224503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224503 prefixEnd_224503 := by exact prefixLift 224503
  have htrace : WordTrace (prefixWord ++ tailWord_224503) baseStart_224503 baseEnd_224503 := by
    simpa [prefixWord, tailWord_224503, baseEnd_224503] using wordTrace_append hprefix tailTrace_224503
  have hstable : (prefixWord ++ tailWord_224503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224503).length < 2 ^ (prefixWord ++ tailWord_224503).sum := by decide
  have hdescent : baseEnd_224503 < baseStart_224503 := by decide
  rcases family_descends (prefixWord ++ tailWord_224503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224517 : List Nat := [1, 3, 1, 1, 2, 1, 3, 5, 3]
def baseStart_224517 : Nat := 118140960795 + 224517 * 2 ^ 59
def prefixEnd_224517 : Nat := 4983230072969 + 3 ^ 40 * 224517 * 2
def baseEnd_224517 : Nat := 102475676538314053248863

theorem tailTrace_224517 : CollatzResearch.WordTrace tailWord_224517 prefixEnd_224517 102475676538314053248863 := by
  unfold tailWord_224517
  simp only [CollatzResearch.WordTrace]
  refine ⟨8188807727620728295951805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5459205151747152197301203 8188807727620728295951805)
  ·
    refine ⟨3070802897857773110981927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8188807727620728295951805 3070802897857773110981927)
    ·
      refine ⟨4606204346786659666472891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3070802897857773110981927 4606204346786659666472891)
      ·
        refine ⟨6909306520179989499709337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4606204346786659666472891 6909306520179989499709337)
        ·
          refine ⟨5181979890134992124782003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6909306520179989499709337 5181979890134992124782003)
          ·
            refine ⟨7772969835202488187173005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5181979890134992124782003 7772969835202488187173005)
            ·
              refine ⟨2914863688200933070189877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7772969835202488187173005 2914863688200933070189877)
              ·
                refine ⟨273268470768837475330301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2914863688200933070189877 273268470768837475330301)
                ·
                  refine ⟨102475676538314053248863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273268470768837475330301 102475676538314053248863)
                  ·
                    rfl

theorem cell20_224517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_224517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224517 prefixEnd_224517 := by exact prefixLift 224517
  have htrace : WordTrace (prefixWord ++ tailWord_224517) baseStart_224517 baseEnd_224517 := by
    simpa [prefixWord, tailWord_224517, baseEnd_224517] using wordTrace_append hprefix tailTrace_224517
  have hstable : (prefixWord ++ tailWord_224517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224517).length < 2 ^ (prefixWord ++ tailWord_224517).sum := by decide
  have hdescent : baseEnd_224517 < baseStart_224517 := by decide
  rcases family_descends (prefixWord ++ tailWord_224517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224524 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 6]
def baseStart_224524 : Nat := 118140960795 + 224524 * 2 ^ 59
def prefixEnd_224524 : Nat := 4983230072969 + 3 ^ 40 * 224524 * 2
def baseEnd_224524 : Nat := 102478871529053140015501

theorem tailTrace_224524 : CollatzResearch.WordTrace tailWord_224524 prefixEnd_224524 102478871529053140015501 := by
  unfold tailWord_224524
  simp only [CollatzResearch.WordTrace]
  refine ⟨4094531519297684245728313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5459375359063578994304417 4094531519297684245728313)
  ·
    refine ⟨3070898639473263184296235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4094531519297684245728313 3070898639473263184296235)
    ·
      refine ⟨4606347959209894776444353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3070898639473263184296235 4606347959209894776444353)
      ·
        refine ⟨3454760969407421082333265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4606347959209894776444353 3454760969407421082333265)
        ·
          refine ⟨2591070727055565811749949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3454760969407421082333265 2591070727055565811749949)
          ·
            refine ⟨971651522645837179406231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2591070727055565811749949 971651522645837179406231)
            ·
              refine ⟨1457477283968755769109347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 971651522645837179406231 1457477283968755769109347)
              ·
                refine ⟨2186215925953133653664021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1457477283968755769109347 2186215925953133653664021)
                ·
                  refine ⟨102478871529053140015501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2186215925953133653664021 102478871529053140015501)
                  ·
                    rfl

theorem cell20_224524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_224524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224524 prefixEnd_224524 := by exact prefixLift 224524
  have htrace : WordTrace (prefixWord ++ tailWord_224524) baseStart_224524 baseEnd_224524 := by
    simpa [prefixWord, tailWord_224524, baseEnd_224524] using wordTrace_append hprefix tailTrace_224524
  have hstable : (prefixWord ++ tailWord_224524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224524).length < 2 ^ (prefixWord ++ tailWord_224524).sum := by decide
  have hdescent : baseEnd_224524 < baseStart_224524 := by decide
  rcases family_descends (prefixWord ++ tailWord_224524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224610 : List Nat := [3, 3, 2, 1, 1, 1, 2, 4, 3]
def baseStart_224610 : Nat := 118140960795 + 224610 * 2 ^ 59
def prefixEnd_224610 : Nat := 4983230072969 + 3 ^ 40 * 224610 * 2
def baseEnd_224610 : Nat := 102518124272419063148483

theorem tailTrace_224610 : CollatzResearch.WordTrace tailWord_224610 prefixEnd_224610 102518124272419063148483 := by
  unfold tailWord_224610
  simp only [CollatzResearch.WordTrace]
  refine ⟨2048049929070951294771821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5461466477522536786058189 2048049929070951294771821)
  ·
    refine ⟨768018723401606735539433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2048049929070951294771821 768018723401606735539433)
    ·
      refine ⟨576014042551205051654575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 768018723401606735539433 576014042551205051654575)
      ·
        refine ⟨864021063826807577481863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576014042551205051654575 864021063826807577481863)
        ·
          refine ⟨1296031595740211366222795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 864021063826807577481863 1296031595740211366222795)
          ·
            refine ⟨1944047393610317049334193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1296031595740211366222795 1944047393610317049334193)
            ·
              refine ⟨1458035545207737787000645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1944047393610317049334193 1458035545207737787000645)
              ·
                refine ⟨273381664726450835062621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1458035545207737787000645 273381664726450835062621)
                ·
                  refine ⟨102518124272419063148483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273381664726450835062621 102518124272419063148483)
                  ·
                    rfl

theorem cell20_224610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_224610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224610 prefixEnd_224610 := by exact prefixLift 224610
  have htrace : WordTrace (prefixWord ++ tailWord_224610) baseStart_224610 baseEnd_224610 := by
    simpa [prefixWord, tailWord_224610, baseEnd_224610] using wordTrace_append hprefix tailTrace_224610
  have hstable : (prefixWord ++ tailWord_224610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224610).length < 2 ^ (prefixWord ++ tailWord_224610).sum := by decide
  have hdescent : baseEnd_224610 < baseStart_224610 := by decide
  rcases family_descends (prefixWord ++ tailWord_224610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224631 : List Nat := [1, 1, 3, 1, 1, 2, 5, 3, 3]
def baseStart_224631 : Nat := 118140960795 + 224631 * 2 ^ 59
def prefixEnd_224631 : Nat := 4983230072969 + 3 ^ 40 * 224631 * 2
def baseEnd_224631 : Nat := 102527709244636323448397

theorem tailTrace_224631 : CollatzResearch.WordTrace tailWord_224631 prefixEnd_224631 102527709244636323448397 := by
  unfold tailWord_224631
  simp only [CollatzResearch.WordTrace]
  refine ⟨8192965649207725765601747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5461977099471817177067831 8192965649207725765601747)
  ·
    refine ⟨12289448473811588648402621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8192965649207725765601747 12289448473811588648402621)
    ·
      refine ⟨4608543177679345743150983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12289448473811588648402621 4608543177679345743150983)
      ·
        refine ⟨6912814766519018614726475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4608543177679345743150983 6912814766519018614726475)
        ·
          refine ⟨10369222149778527922089713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6912814766519018614726475 10369222149778527922089713)
          ·
            refine ⟨7776916612333895941567285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10369222149778527922089713 7776916612333895941567285)
            ·
              refine ⟨729085932406302744521933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7776916612333895941567285 729085932406302744521933)
              ·
                refine ⟨273407224652363529195725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 729085932406302744521933 273407224652363529195725)
                ·
                  refine ⟨102527709244636323448397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273407224652363529195725 102527709244636323448397)
                  ·
                    rfl

theorem cell20_224631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 3].length) (baseStart_224631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224631 prefixEnd_224631 := by exact prefixLift 224631
  have htrace : WordTrace (prefixWord ++ tailWord_224631) baseStart_224631 baseEnd_224631 := by
    simpa [prefixWord, tailWord_224631, baseEnd_224631] using wordTrace_append hprefix tailTrace_224631
  have hstable : (prefixWord ++ tailWord_224631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224631).length < 2 ^ (prefixWord ++ tailWord_224631).sum := by decide
  have hdescent : baseEnd_224631 < baseStart_224631 := by decide
  rcases family_descends (prefixWord ++ tailWord_224631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224645 : List Nat := [1, 3, 1, 1, 3, 1, 4, 6]
def baseStart_224645 : Nat := 118140960795 + 224645 * 2 ^ 59
def prefixEnd_224645 : Nat := 4983230072969 + 3 ^ 40 * 224645 * 2
def baseEnd_224645 : Nat := 34178033075371498993891

theorem tailTrace_224645 : CollatzResearch.WordTrace tailWord_224645 prefixEnd_224645 34178033075371498993891 := by
  unfold tailWord_224645
  simp only [CollatzResearch.WordTrace]
  refine ⟨8193476271157006156611389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5462317514104670771074259 8193476271157006156611389)
  ·
    refine ⟨3072553601683877308729271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8193476271157006156611389 3072553601683877308729271)
    ·
      refine ⟨4608830402525815963093907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3072553601683877308729271 4608830402525815963093907)
      ·
        refine ⟨6913245603788723944640861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4608830402525815963093907 6913245603788723944640861)
        ·
          refine ⟨2592467101420771479240323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6913245603788723944640861 2592467101420771479240323)
          ·
            refine ⟨3888700652131157218860485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592467101420771479240323 3888700652131157218860485)
            ·
              refine ⟨729131372274591978536341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3888700652131157218860485 729131372274591978536341)
              ·
                refine ⟨34178033075371498993891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 729131372274591978536341 34178033075371498993891)
                ·
                  rfl

theorem cell20_224645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 6].length) (baseStart_224645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224645 prefixEnd_224645 := by exact prefixLift 224645
  have htrace : WordTrace (prefixWord ++ tailWord_224645) baseStart_224645 baseEnd_224645 := by
    simpa [prefixWord, tailWord_224645, baseEnd_224645] using wordTrace_append hprefix tailTrace_224645
  have hstable : (prefixWord ++ tailWord_224645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224645).length < 2 ^ (prefixWord ++ tailWord_224645).sum := by decide
  have hdescent : baseEnd_224645 < baseStart_224645 := by decide
  rcases family_descends (prefixWord ++ tailWord_224645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224676 : List Nat := [2, 3, 1, 2, 1, 1, 1, 5, 4]
def baseStart_224676 : Nat := 118140960795 + 224676 * 2 ^ 59
def prefixEnd_224676 : Nat := 4983230072969 + 3 ^ 40 * 224676 * 2
def baseEnd_224676 : Nat := 102548248470816166948213

theorem tailTrace_224676 : CollatzResearch.WordTrace tailWord_224676 prefixEnd_224676 102548248470816166948213 := by
  unfold tailWord_224676
  simp only [CollatzResearch.WordTrace]
  refine ⟨4097303467022349225494941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5463071289363132300659921 4097303467022349225494941)
  ·
    refine ⟨1536488800133380959560603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4097303467022349225494941 1536488800133380959560603)
    ·
      refine ⟨2304733200200071439340905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1536488800133380959560603 2304733200200071439340905)
      ·
        refine ⟨1728549900150053579505679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2304733200200071439340905 1728549900150053579505679)
        ·
          refine ⟨2592824850225080369258519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1728549900150053579505679 2592824850225080369258519)
          ·
            refine ⟨3889237275337620553887779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2592824850225080369258519 3889237275337620553887779)
            ·
              refine ⟨5833855913006430830831669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3889237275337620553887779 5833855913006430830831669)
              ·
                refine ⟨546923991844352890390469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5833855913006430830831669 546923991844352890390469)
                ·
                  refine ⟨102548248470816166948213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 546923991844352890390469 102548248470816166948213)
                  ·
                    rfl

theorem cell20_224676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_224676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224676 prefixEnd_224676 := by exact prefixLift 224676
  have htrace : WordTrace (prefixWord ++ tailWord_224676) baseStart_224676 baseEnd_224676 := by
    simpa [prefixWord, tailWord_224676, baseEnd_224676] using wordTrace_append hprefix tailTrace_224676
  have hstable : (prefixWord ++ tailWord_224676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224676).length < 2 ^ (prefixWord ++ tailWord_224676).sum := by decide
  have hdescent : baseEnd_224676 < baseStart_224676 := by decide
  rcases family_descends (prefixWord ++ tailWord_224676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224693 : List Nat := [1, 3, 3, 2, 2, 2, 1, 2, 4]
def baseStart_224693 : Nat := 118140960795 + 224693 * 2 ^ 59
def prefixEnd_224693 : Nat := 4983230072969 + 3 ^ 40 * 224693 * 2
def baseEnd_224693 : Nat := 102556007734039663381477

theorem tailTrace_224693 : CollatzResearch.WordTrace tailWord_224693 prefixEnd_224693 102556007734039663381477 := by
  unfold tailWord_224693
  simp only [CollatzResearch.WordTrace]
  refine ⟨8195226974983110354358733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5463484649988740236239155 8195226974983110354358733)
  ·
    refine ⟨3073210115618666382884525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8195226974983110354358733 3073210115618666382884525)
    ·
      refine ⟨1152453793356999893581697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3073210115618666382884525 1152453793356999893581697)
      ·
        refine ⟨864340345017749920186273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1152453793356999893581697 864340345017749920186273)
        ·
          refine ⟨648255258763312440139705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 864340345017749920186273 648255258763312440139705)
          ·
            refine ⟨486191444072484330104779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 648255258763312440139705 486191444072484330104779)
            ·
              refine ⟨729287166108726495157169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486191444072484330104779 729287166108726495157169)
              ·
                refine ⟨546965374581544871367877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 729287166108726495157169 546965374581544871367877)
                ·
                  refine ⟨102556007734039663381477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 546965374581544871367877 102556007734039663381477)
                  ·
                    rfl

theorem cell20_224693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_224693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224693 prefixEnd_224693 := by exact prefixLift 224693
  have htrace : WordTrace (prefixWord ++ tailWord_224693) baseStart_224693 baseEnd_224693 := by
    simpa [prefixWord, tailWord_224693, baseEnd_224693] using wordTrace_append hprefix tailTrace_224693
  have hstable : (prefixWord ++ tailWord_224693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224693).length < 2 ^ (prefixWord ++ tailWord_224693).sum := by decide
  have hdescent : baseEnd_224693 < baseStart_224693 := by decide
  rcases family_descends (prefixWord ++ tailWord_224693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224724 : List Nat := [2, 4, 1, 2, 3, 1, 1, 1, 5]
def baseStart_224724 : Nat := 118140960795 + 224724 * 2 ^ 59
def prefixEnd_224724 : Nat := 4983230072969 + 3 ^ 40 * 224724 * 2
def baseEnd_224724 : Nat := 102570156978741333348017

theorem tailTrace_224724 : CollatzResearch.WordTrace tailWord_224724 prefixEnd_224724 102570156978741333348017 := by
  unfold tailWord_224724
  simp only [CollatzResearch.WordTrace]
  refine ⟨4098178818935401324368613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5464238425247201765824817 4098178818935401324368613)
  ·
    refine ⟨768408528550387748319115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4098178818935401324368613 768408528550387748319115)
    ·
      refine ⟨1152612792825581622478673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 768408528550387748319115 1152612792825581622478673)
      ·
        refine ⟨864459594619186216859005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1152612792825581622478673 864459594619186216859005)
        ·
          refine ⟨324172347982194831322127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 864459594619186216859005 324172347982194831322127)
          ·
            refine ⟨486258521973292246983191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324172347982194831322127 486258521973292246983191)
            ·
              refine ⟨729387782959938370474787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486258521973292246983191 729387782959938370474787)
              ·
                refine ⟨1094081674439907555712181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 729387782959938370474787 1094081674439907555712181)
                ·
                  refine ⟨102570156978741333348017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1094081674439907555712181 102570156978741333348017)
                  ·
                    rfl

theorem cell20_224724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_224724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224724 prefixEnd_224724 := by exact prefixLift 224724
  have htrace : WordTrace (prefixWord ++ tailWord_224724) baseStart_224724 baseEnd_224724 := by
    simpa [prefixWord, tailWord_224724, baseEnd_224724] using wordTrace_append hprefix tailTrace_224724
  have hstable : (prefixWord ++ tailWord_224724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224724).length < 2 ^ (prefixWord ++ tailWord_224724).sum := by decide
  have hdescent : baseEnd_224724 < baseStart_224724 := by decide
  rcases family_descends (prefixWord ++ tailWord_224724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224741 : List Nat := [1, 3, 1, 5, 1, 2, 3, 1, 3]
def baseStart_224741 : Nat := 118140960795 + 224741 * 2 ^ 59
def prefixEnd_224741 : Nat := 4983230072969 + 3 ^ 40 * 224741 * 2
def baseEnd_224741 : Nat := 102577916241964829781281

theorem tailTrace_224741 : CollatzResearch.WordTrace tailWord_224741 prefixEnd_224741 102577916241964829781281 := by
  unfold tailWord_224741
  simp only [CollatzResearch.WordTrace]
  refine ⟨8196977678809214552106077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5464651785872809701404051 8196977678809214552106077)
  ·
    refine ⟨3073866629553455457039779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8196977678809214552106077 3073866629553455457039779)
    ·
      refine ⟨4610799944330183185559669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3073866629553455457039779 4610799944330183185559669)
      ·
        refine ⟨432262494780954673646219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4610799944330183185559669 432262494780954673646219)
        ·
          refine ⟨648393742171432010469329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432262494780954673646219 648393742171432010469329)
          ·
            refine ⟨486295306628574007851997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 648393742171432010469329 486295306628574007851997)
            ·
              refine ⟨182360739985715252944499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 486295306628574007851997 182360739985715252944499)
              ·
                refine ⟨273541109978572879416749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182360739985715252944499 273541109978572879416749)
                ·
                  refine ⟨102577916241964829781281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273541109978572879416749 102577916241964829781281)
                  ·
                    rfl

theorem cell20_224741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_224741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224741 prefixEnd_224741 := by exact prefixLift 224741
  have htrace : WordTrace (prefixWord ++ tailWord_224741) baseStart_224741 baseEnd_224741 := by
    simpa [prefixWord, tailWord_224741, baseEnd_224741] using wordTrace_append hprefix tailTrace_224741
  have hstable : (prefixWord ++ tailWord_224741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224741).length < 2 ^ (prefixWord ++ tailWord_224741).sum := by decide
  have hdescent : baseEnd_224741 < baseStart_224741 := by decide
  rcases family_descends (prefixWord ++ tailWord_224741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224752 : List Nat := [2, 1, 1, 1, 3, 4, 2, 2, 4]
def baseStart_224752 : Nat := 118140960795 + 224752 * 2 ^ 59
def prefixEnd_224752 : Nat := 4983230072969 + 3 ^ 40 * 224752 * 2
def baseEnd_224752 : Nat := 102582936941697680414569

theorem tailTrace_224752 : CollatzResearch.WordTrace tailWord_224752 prefixEnd_224752 102582936941697680414569 := by
  unfold tailWord_224752
  simp only [CollatzResearch.WordTrace]
  refine ⟨4098689440884681715378255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5464919254512908953837673 4098689440884681715378255)
  ·
    refine ⟨6148034161327022573067383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4098689440884681715378255 6148034161327022573067383)
    ·
      refine ⟨9222051241990533859601075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6148034161327022573067383 9222051241990533859601075)
      ·
        refine ⟨13833076862985800789401613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9222051241990533859601075 13833076862985800789401613)
        ·
          refine ⟨5187403823619675296025605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13833076862985800789401613 5187403823619675296025605)
          ·
            refine ⟨972638216928689118004801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5187403823619675296025605 972638216928689118004801)
            ·
              refine ⟨729478662696516838503601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 972638216928689118004801 729478662696516838503601)
              ·
                refine ⟨547108997022387628877701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 729478662696516838503601 547108997022387628877701)
                ·
                  refine ⟨102582936941697680414569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 547108997022387628877701 102582936941697680414569)
                  ·
                    rfl

theorem cell20_224752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_224752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224752 prefixEnd_224752 := by exact prefixLift 224752
  have htrace : WordTrace (prefixWord ++ tailWord_224752) baseStart_224752 baseEnd_224752 := by
    simpa [prefixWord, tailWord_224752, baseEnd_224752] using wordTrace_append hprefix tailTrace_224752
  have hstable : (prefixWord ++ tailWord_224752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224752).length < 2 ^ (prefixWord ++ tailWord_224752).sum := by decide
  have hdescent : baseEnd_224752 < baseStart_224752 := by decide
  rcases family_descends (prefixWord ++ tailWord_224752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224800 : List Nat := [2, 1, 1, 6, 1, 2, 1, 3, 3]
def baseStart_224800 : Nat := 118140960795 + 224800 * 2 ^ 59
def prefixEnd_224800 : Nat := 4983230072969 + 3 ^ 40 * 224800 * 2
def baseEnd_224800 : Nat := 102604845449622846814373

theorem tailTrace_224800 : CollatzResearch.WordTrace tailWord_224800 prefixEnd_224800 102604845449622846814373 := by
  unfold tailWord_224800
  simp only [CollatzResearch.WordTrace]
  refine ⟨4099564792797733814251927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5466086390396978419002569 4099564792797733814251927)
  ·
    refine ⟨6149347189196600721377891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4099564792797733814251927 6149347189196600721377891)
    ·
      refine ⟨9224020783794901082066837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6149347189196600721377891 9224020783794901082066837)
      ·
        refine ⟨432375974240385988221883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 9224020783794901082066837 432375974240385988221883)
        ·
          refine ⟨648563961360578982332825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 432375974240385988221883 648563961360578982332825)
          ·
            refine ⟨486422971020434236749619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 648563961360578982332825 486422971020434236749619)
            ·
              refine ⟨729634456530651355124429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486422971020434236749619 729634456530651355124429)
              ·
                refine ⟨273612921198994258171661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 729634456530651355124429 273612921198994258171661)
                ·
                  refine ⟨102604845449622846814373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 273612921198994258171661 102604845449622846814373)
                  ·
                    rfl

theorem cell20_224800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_224800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224800 prefixEnd_224800 := by exact prefixLift 224800
  have htrace : WordTrace (prefixWord ++ tailWord_224800) baseStart_224800 baseEnd_224800 := by
    simpa [prefixWord, tailWord_224800, baseEnd_224800] using wordTrace_append hprefix tailTrace_224800
  have hstable : (prefixWord ++ tailWord_224800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224800).length < 2 ^ (prefixWord ++ tailWord_224800).sum := by decide
  have hdescent : baseEnd_224800 < baseStart_224800 := by decide
  rcases family_descends (prefixWord ++ tailWord_224800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224814 : List Nat := [4, 1, 3, 1, 2, 1, 2, 6]
def baseStart_224814 : Nat := 118140960795 + 224814 * 2 ^ 59
def prefixEnd_224814 : Nat := 4983230072969 + 3 ^ 40 * 224814 * 2
def baseEnd_224814 : Nat := 34203745143700340115883

theorem tailTrace_224814 : CollatzResearch.WordTrace tailWord_224814 prefixEnd_224814 34203745143700340115883 := by
  unfold tailWord_224814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1024955025943093502439187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5466426805029832013008997 1024955025943093502439187)
  ·
    refine ⟨1537432538914640253658781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1024955025943093502439187 1537432538914640253658781)
    ·
      refine ⟨576537202092990095122043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1537432538914640253658781 576537202092990095122043)
      ·
        refine ⟨864805803139485142683065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 576537202092990095122043 864805803139485142683065)
        ·
          refine ⟨648604352354613857012299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 864805803139485142683065 648604352354613857012299)
          ·
            refine ⟨972906528531920785518449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648604352354613857012299 972906528531920785518449)
            ·
              refine ⟨729679896398940589138837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 972906528531920785518449 729679896398940589138837)
              ·
                refine ⟨34203745143700340115883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 729679896398940589138837 34203745143700340115883)
                ·
                  rfl

theorem cell20_224814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_224814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224814 prefixEnd_224814 := by exact prefixLift 224814
  have htrace : WordTrace (prefixWord ++ tailWord_224814) baseStart_224814 baseEnd_224814 := by
    simpa [prefixWord, tailWord_224814, baseEnd_224814] using wordTrace_append hprefix tailTrace_224814
  have hstable : (prefixWord ++ tailWord_224814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224814).length < 2 ^ (prefixWord ++ tailWord_224814).sum := by decide
  have hdescent : baseEnd_224814 < baseStart_224814 := by decide
  rcases family_descends (prefixWord ++ tailWord_224814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224887 : List Nat := [1, 1, 3, 1, 1, 3, 1, 1, 8]
def baseStart_224887 : Nat := 118140960795 + 224887 * 2 ^ 59
def prefixEnd_224887 : Nat := 4983230072969 + 3 ^ 40 * 224887 * 2
def baseEnd_224887 : Nat := 102644554620237210914017

theorem tailTrace_224887 : CollatzResearch.WordTrace tailWord_224887 prefixEnd_224887 102644554620237210914017 := by
  unfold tailWord_224887
  simp only [CollatzResearch.WordTrace]
  refine ⟨8202302736280281486920915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5468201824186854324613943 8202302736280281486920915)
  ·
    refine ⟨12303454104420422230381373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8202302736280281486920915 12303454104420422230381373)
    ·
      refine ⟨4613795289157658336393015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12303454104420422230381373 4613795289157658336393015)
      ·
        refine ⟨6920692933736487504589523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4613795289157658336393015 6920692933736487504589523)
        ·
          refine ⟨10381039400604731256884285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6920692933736487504589523 10381039400604731256884285)
          ·
            refine ⟨3892889775226774221331607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10381039400604731256884285 3892889775226774221331607)
            ·
              refine ⟨5839334662840161331997411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3892889775226774221331607 5839334662840161331997411)
              ·
                refine ⟨8759001994260241997996117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5839334662840161331997411 8759001994260241997996117)
                ·
                  refine ⟨102644554620237210914017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8759001994260241997996117 102644554620237210914017)
                  ·
                    rfl

theorem cell20_224887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_224887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224887 prefixEnd_224887 := by exact prefixLift 224887
  have htrace : WordTrace (prefixWord ++ tailWord_224887) baseStart_224887 baseEnd_224887 := by
    simpa [prefixWord, tailWord_224887, baseEnd_224887] using wordTrace_append hprefix tailTrace_224887
  have hstable : (prefixWord ++ tailWord_224887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224887).length < 2 ^ (prefixWord ++ tailWord_224887).sum := by decide
  have hdescent : baseEnd_224887 < baseStart_224887 := by decide
  rcases family_descends (prefixWord ++ tailWord_224887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224897 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 5]
def baseStart_224897 : Nat := 118140960795 + 224897 * 2 ^ 59
def prefixEnd_224897 : Nat := 4983230072969 + 3 ^ 40 * 224897 * 2
def baseEnd_224897 : Nat := 102649118892721620580643

theorem tailTrace_224897 : CollatzResearch.WordTrace tailWord_224897 prefixEnd_224897 102649118892721620580643 := by
  unfold tailWord_224897
  simp only [CollatzResearch.WordTrace]
  refine ⟨8202667466244053194784945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5468444977496035463189963 8202667466244053194784945)
  ·
    refine ⟨6152000599683039896088709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8202667466244053194784945 6152000599683039896088709)
    ·
      refine ⟨1153500112440569980516633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6152000599683039896088709 1153500112440569980516633)
      ·
        refine ⟨865125084330427485387475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1153500112440569980516633 865125084330427485387475)
        ·
          refine ⟨1297687626495641228081213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865125084330427485387475 1297687626495641228081213)
          ·
            refine ⟨486632859935865460530455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1297687626495641228081213 486632859935865460530455)
            ·
              refine ⟨729949289903798190795683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486632859935865460530455 729949289903798190795683)
              ·
                refine ⟨1094923934855697286193525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 729949289903798190795683 1094923934855697286193525)
                ·
                  refine ⟨102649118892721620580643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1094923934855697286193525 102649118892721620580643)
                  ·
                    rfl

theorem cell20_224897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_224897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224897 prefixEnd_224897 := by exact prefixLift 224897
  have htrace : WordTrace (prefixWord ++ tailWord_224897) baseStart_224897 baseEnd_224897 := by
    simpa [prefixWord, tailWord_224897, baseEnd_224897] using wordTrace_append hprefix tailTrace_224897
  have hstable : (prefixWord ++ tailWord_224897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224897).length < 2 ^ (prefixWord ++ tailWord_224897).sum := by decide
  have hdescent : baseEnd_224897 < baseStart_224897 := by decide
  rcases family_descends (prefixWord ++ tailWord_224897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224924 : List Nat := [2, 2, 3, 2, 4, 1, 2, 4]
def baseStart_224924 : Nat := 118140960795 + 224924 * 2 ^ 59
def prefixEnd_224924 : Nat := 4983230072969 + 3 ^ 40 * 224924 * 2
def baseEnd_224924 : Nat := 34220480809476508893511

theorem tailTrace_224924 : CollatzResearch.WordTrace tailWord_224924 prefixEnd_224924 34220480809476508893511 := by
  unfold tailWord_224924
  simp only [CollatzResearch.WordTrace]
  refine ⟨4101826118573118403008913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5469101491430824537345217 4101826118573118403008913)
  ·
    refine ⟨3076369588929838802256685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4101826118573118403008913 3076369588929838802256685)
    ·
      refine ⟨1153638595848689550846257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3076369588929838802256685 1153638595848689550846257)
      ·
        refine ⟨865228946886517163134693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1153638595848689550846257 865228946886517163134693)
        ·
          refine ⟨162230427541221968087755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 865228946886517163134693 162230427541221968087755)
          ·
            refine ⟨243345641311832952131633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162230427541221968087755 243345641311832952131633)
            ·
              refine ⟨182509230983874714098725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243345641311832952131633 182509230983874714098725)
              ·
                refine ⟨34220480809476508893511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182509230983874714098725 34220480809476508893511)
                ·
                  rfl

theorem cell20_224924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 4].length) (baseStart_224924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224924 prefixEnd_224924 := by exact prefixLift 224924
  have htrace : WordTrace (prefixWord ++ tailWord_224924) baseStart_224924 baseEnd_224924 := by
    simpa [prefixWord, tailWord_224924, baseEnd_224924] using wordTrace_append hprefix tailTrace_224924
  have hstable : (prefixWord ++ tailWord_224924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224924).length < 2 ^ (prefixWord ++ tailWord_224924).sum := by decide
  have hdescent : baseEnd_224924 < baseStart_224924 := by decide
  rcases family_descends (prefixWord ++ tailWord_224924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224928 : List Nat := [2, 1, 1, 4, 3, 1, 4, 4]
def baseStart_224928 : Nat := 118140960795 + 224928 * 2 ^ 59
def prefixEnd_224928 : Nat := 4983230072969 + 3 ^ 40 * 224928 * 2
def baseEnd_224928 : Nat := 34221089379141096849061

theorem tailTrace_224928 : CollatzResearch.WordTrace tailWord_224928 prefixEnd_224928 34221089379141096849061 := by
  unfold tailWord_224928
  simp only [CollatzResearch.WordTrace]
  refine ⟨4101899064565872744581719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5469198752754496992775625 4101899064565872744581719)
  ·
    refine ⟨6152848596848809116872579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4101899064565872744581719 6152848596848809116872579)
    ·
      refine ⟨9229272895273213675308869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6152848596848809116872579 9229272895273213675308869)
      ·
        refine ⟨1730488667863727564120413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9229272895273213675308869 1730488667863727564120413)
        ·
          refine ⟨648933250448897836545155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1730488667863727564120413 648933250448897836545155)
          ·
            refine ⟨973399875673346754817733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 648933250448897836545155 973399875673346754817733)
            ·
              refine ⟨182512476688752516528325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 973399875673346754817733 182512476688752516528325)
              ·
                refine ⟨34221089379141096849061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182512476688752516528325 34221089379141096849061)
                ·
                  rfl

theorem cell20_224928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_224928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224928 prefixEnd_224928 := by exact prefixLift 224928
  have htrace : WordTrace (prefixWord ++ tailWord_224928) baseStart_224928 baseEnd_224928 := by
    simpa [prefixWord, tailWord_224928, baseEnd_224928] using wordTrace_append hprefix tailTrace_224928
  have hstable : (prefixWord ++ tailWord_224928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224928).length < 2 ^ (prefixWord ++ tailWord_224928).sum := by decide
  have hdescent : baseEnd_224928 < baseStart_224928 := by decide
  rcases family_descends (prefixWord ++ tailWord_224928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_224997 : List Nat := [1, 3, 1, 4, 1, 1, 2, 5, 2]
def baseStart_224997 : Nat := 118140960795 + 224997 * 2 ^ 59
def prefixEnd_224997 : Nat := 4983230072969 + 3 ^ 40 * 224997 * 2
def baseEnd_224997 : Nat := 102694761617565717246901

theorem tailTrace_224997 : CollatzResearch.WordTrace tailWord_224997 prefixEnd_224997 102694761617565717246901 := by
  unfold tailWord_224997
  simp only [CollatzResearch.WordTrace]
  refine ⟨8206314765881770273425245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5470876510587846848950163 8206314765881770273425245)
  ·
    refine ⟨3077368037205663852534467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8206314765881770273425245 3077368037205663852534467)
    ·
      refine ⟨4616052055808495778801701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3077368037205663852534467 4616052055808495778801701)
      ·
        refine ⟨865509760464092958525319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4616052055808495778801701 865509760464092958525319)
        ·
          refine ⟨1298264640696139437787979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 865509760464092958525319 1298264640696139437787979)
          ·
            refine ⟨1947396961044209156681969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1298264640696139437787979 1947396961044209156681969)
            ·
              refine ⟨1460547720783156867511477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1947396961044209156681969 1460547720783156867511477)
              ·
                refine ⟨136926348823420956329201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1460547720783156867511477 136926348823420956329201)
                ·
                  refine ⟨102694761617565717246901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136926348823420956329201 102694761617565717246901)
                  ·
                    rfl

theorem cell20_224997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_224997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_224997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_224997 prefixEnd_224997 := by exact prefixLift 224997
  have htrace : WordTrace (prefixWord ++ tailWord_224997) baseStart_224997 baseEnd_224997 := by
    simpa [prefixWord, tailWord_224997, baseEnd_224997] using wordTrace_append hprefix tailTrace_224997
  have hstable : (prefixWord ++ tailWord_224997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_224997).length < 2 ^ (prefixWord ++ tailWord_224997).sum := by decide
  have hdescent : baseEnd_224997 < baseStart_224997 := by decide
  rcases family_descends (prefixWord ++ tailWord_224997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225014 : List Nat := [5, 1, 1, 1, 1, 4, 1, 4, 2]
def baseStart_225014 : Nat := 118140960795 + 225014 * 2 ^ 59
def prefixEnd_225014 : Nat := 4983230072969 + 3 ^ 40 * 225014 * 2
def baseEnd_225014 : Nat := 102702520880789213680165

theorem tailTrace_225014 : CollatzResearch.WordTrace tailWord_225014 prefixEnd_225014 102702520880789213680165 := by
  unfold tailWord_225014
  simp only [CollatzResearch.WordTrace]
  refine ⟨512933425426261386049631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5471289871213454784529397 512933425426261386049631)
  ·
    refine ⟨769400138139392079074447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 512933425426261386049631 769400138139392079074447)
    ·
      refine ⟨1154100207209088118611671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 769400138139392079074447 1154100207209088118611671)
      ·
        refine ⟨1731150310813632177917507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1154100207209088118611671 1731150310813632177917507)
        ·
          refine ⟨2596725466220448266876261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1731150310813632177917507 2596725466220448266876261)
          ·
            refine ⟨486886024916334050039299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2596725466220448266876261 486886024916334050039299)
            ·
              refine ⟨730329037374501075058949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 486886024916334050039299 730329037374501075058949)
              ·
                refine ⟨136936694507718951573553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 730329037374501075058949 136936694507718951573553)
                ·
                  refine ⟨102702520880789213680165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136936694507718951573553 102702520880789213680165)
                  ·
                    rfl

theorem cell20_225014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_225014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225014 prefixEnd_225014 := by exact prefixLift 225014
  have htrace : WordTrace (prefixWord ++ tailWord_225014) baseStart_225014 baseEnd_225014 := by
    simpa [prefixWord, tailWord_225014, baseEnd_225014] using wordTrace_append hprefix tailTrace_225014
  have hstable : (prefixWord ++ tailWord_225014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225014).length < 2 ^ (prefixWord ++ tailWord_225014).sum := by decide
  have hdescent : baseEnd_225014 < baseStart_225014 := by decide
  rcases family_descends (prefixWord ++ tailWord_225014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225025 : List Nat := [1, 2, 4, 1, 1, 1, 5, 5]
def baseStart_225025 : Nat := 118140960795 + 225025 * 2 ^ 59
def prefixEnd_225025 : Nat := 4983230072969 + 3 ^ 40 * 225025 * 2
def baseEnd_225025 : Nat := 34235847193507354771151

theorem tailTrace_225025 : CollatzResearch.WordTrace tailWord_225025 prefixEnd_225025 34235847193507354771151 := by
  unfold tailWord_225025
  simp only [CollatzResearch.WordTrace]
  refine ⟨8207336009780331055444529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5471557339853554036963019 8207336009780331055444529)
  ·
    refine ⟨6155502007335248291583397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8207336009780331055444529 6155502007335248291583397)
    ·
      refine ⟨1154156626375359054671887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6155502007335248291583397 1154156626375359054671887)
      ·
        refine ⟨1731234939563038582007831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1154156626375359054671887 1731234939563038582007831)
        ·
          refine ⟨2596852409344557873011747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1731234939563038582007831 2596852409344557873011747)
          ·
            refine ⟨3895278614016836809517621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2596852409344557873011747 3895278614016836809517621)
            ·
              refine ⟨365182370064078450892277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3895278614016836809517621 365182370064078450892277)
              ·
                refine ⟨34235847193507354771151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 365182370064078450892277 34235847193507354771151)
                ·
                  rfl

theorem cell20_225025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 5].length) (baseStart_225025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225025 prefixEnd_225025 := by exact prefixLift 225025
  have htrace : WordTrace (prefixWord ++ tailWord_225025) baseStart_225025 baseEnd_225025 := by
    simpa [prefixWord, tailWord_225025, baseEnd_225025] using wordTrace_append hprefix tailTrace_225025
  have hstable : (prefixWord ++ tailWord_225025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225025).length < 2 ^ (prefixWord ++ tailWord_225025).sum := by decide
  have hdescent : baseEnd_225025 < baseStart_225025 := by decide
  rcases family_descends (prefixWord ++ tailWord_225025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225073 : List Nat := [1, 2, 2, 3, 2, 2, 2, 4, 2]
def baseStart_225073 : Nat := 118140960795 + 225073 * 2 ^ 59
def prefixEnd_225073 : Nat := 4983230072969 + 3 ^ 40 * 225073 * 2
def baseEnd_225073 : Nat := 102729450088447230713257

theorem tailTrace_225073 : CollatzResearch.WordTrace tailWord_225073 prefixEnd_225073 102729450088447230713257 := by
  unfold tailWord_225073
  simp only [CollatzResearch.WordTrace]
  refine ⟨8209086713606435253191873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5472724475737623502127915 8209086713606435253191873)
  ·
    refine ⟨6156815035204826439893905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8209086713606435253191873 6156815035204826439893905)
    ·
      refine ⟨4617611276403619829920429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6156815035204826439893905 4617611276403619829920429)
      ·
        refine ⟨1731604228651357436220161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4617611276403619829920429 1731604228651357436220161)
        ·
          refine ⟨1298703171488518077165121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1731604228651357436220161 1298703171488518077165121)
          ·
            refine ⟨974027378616388557873841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1298703171488518077165121 974027378616388557873841)
            ·
              refine ⟨730520533962291418405381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 974027378616388557873841 730520533962291418405381)
              ·
                refine ⟨136972600117929640951009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 730520533962291418405381 136972600117929640951009)
                ·
                  refine ⟨102729450088447230713257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 136972600117929640951009 102729450088447230713257)
                  ·
                    rfl

theorem cell20_225073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 2].length) (baseStart_225073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225073 prefixEnd_225073 := by exact prefixLift 225073
  have htrace : WordTrace (prefixWord ++ tailWord_225073) baseStart_225073 baseEnd_225073 := by
    simpa [prefixWord, tailWord_225073, baseEnd_225073] using wordTrace_append hprefix tailTrace_225073
  have hstable : (prefixWord ++ tailWord_225073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225073).length < 2 ^ (prefixWord ++ tailWord_225073).sum := by decide
  have hdescent : baseEnd_225073 < baseStart_225073 := by decide
  rcases family_descends (prefixWord ++ tailWord_225073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225128 : List Nat := [2, 1, 4, 2, 1, 1, 5, 2, 2]
def baseStart_225128 : Nat := 118140960795 + 225128 * 2 ^ 59
def prefixEnd_225128 : Nat := 4983230072969 + 3 ^ 40 * 225128 * 2
def baseEnd_225128 : Nat := 102754553587111483879699

theorem tailTrace_225128 : CollatzResearch.WordTrace tailWord_225128 prefixEnd_225128 102754553587111483879699 := by
  unfold tailWord_225128
  simp only [CollatzResearch.WordTrace]
  refine ⟨4105546364203589823222019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5474061818938119764296025 4105546364203589823222019)
  ·
    refine ⟨6158319546305384734833029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4105546364203589823222019 6158319546305384734833029)
    ·
      refine ⟨1154684914932259637781193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6158319546305384734833029 1154684914932259637781193)
      ·
        refine ⟨866013686199194728335895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1154684914932259637781193 866013686199194728335895)
        ·
          refine ⟨1299020529298792092503843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866013686199194728335895 1299020529298792092503843)
          ·
            refine ⟨1948530793948188138755765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1299020529298792092503843 1948530793948188138755765)
            ·
              refine ⟨182674761932642638008353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1948530793948188138755765 182674761932642638008353)
              ·
                refine ⟨137006071449481978506265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182674761932642638008353 137006071449481978506265)
                ·
                  refine ⟨102754553587111483879699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137006071449481978506265 102754553587111483879699)
                  ·
                    rfl

theorem cell20_225128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 2].length) (baseStart_225128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225128 prefixEnd_225128 := by exact prefixLift 225128
  have htrace : WordTrace (prefixWord ++ tailWord_225128) baseStart_225128 baseEnd_225128 := by
    simpa [prefixWord, tailWord_225128, baseEnd_225128] using wordTrace_append hprefix tailTrace_225128
  have hstable : (prefixWord ++ tailWord_225128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225128).length < 2 ^ (prefixWord ++ tailWord_225128).sum := by decide
  have hdescent : baseEnd_225128 < baseStart_225128 := by decide
  rcases family_descends (prefixWord ++ tailWord_225128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225132 : List Nat := [2, 2, 1, 1, 4, 2, 3, 1, 4]
def baseStart_225132 : Nat := 118140960795 + 225132 * 2 ^ 59
def prefixEnd_225132 : Nat := 4983230072969 + 3 ^ 40 * 225132 * 2
def baseEnd_225132 : Nat := 102756379296105247746349

theorem tailTrace_225132 : CollatzResearch.WordTrace tailWord_225132 prefixEnd_225132 102756379296105247746349 := by
  unfold tailWord_225132
  simp only [CollatzResearch.WordTrace]
  refine ⟨4105619310196344164794825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5474159080261792219726433 4105619310196344164794825)
  ·
    refine ⟨3079214482647258123596119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4105619310196344164794825 3079214482647258123596119)
    ·
      refine ⟨4618821723970887185394179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3079214482647258123596119 4618821723970887185394179)
      ·
        refine ⟨6928232585956330778091269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4618821723970887185394179 6928232585956330778091269)
        ·
          refine ⟨1299043609866812020892113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6928232585956330778091269 1299043609866812020892113)
          ·
            refine ⟨974282707400109015669085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1299043609866812020892113 974282707400109015669085)
            ·
              refine ⟨365356015275040880875907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 974282707400109015669085 365356015275040880875907)
              ·
                refine ⟨548034022912561321313861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365356015275040880875907 548034022912561321313861)
                ·
                  refine ⟨102756379296105247746349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 548034022912561321313861 102756379296105247746349)
                  ·
                    rfl

theorem cell20_225132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_225132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225132 prefixEnd_225132 := by exact prefixLift 225132
  have htrace : WordTrace (prefixWord ++ tailWord_225132) baseStart_225132 baseEnd_225132 := by
    simpa [prefixWord, tailWord_225132, baseEnd_225132] using wordTrace_append hprefix tailTrace_225132
  have hstable : (prefixWord ++ tailWord_225132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225132).length < 2 ^ (prefixWord ++ tailWord_225132).sum := by decide
  have hdescent : baseEnd_225132 < baseStart_225132 := by decide
  rcases family_descends (prefixWord ++ tailWord_225132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225180 : List Nat := [2, 2, 3, 3, 1, 2, 2, 2, 3]
def baseStart_225180 : Nat := 118140960795 + 225180 * 2 ^ 59
def prefixEnd_225180 : Nat := 4983230072969 + 3 ^ 40 * 225180 * 2
def baseEnd_225180 : Nat := 102778287804030414146153

theorem tailTrace_225180 : CollatzResearch.WordTrace tailWord_225180 prefixEnd_225180 102778287804030414146153 := by
  unfold tailWord_225180
  simp only [CollatzResearch.WordTrace]
  refine ⟨4106494662109396263668497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5475326216145861684891329 4106494662109396263668497)
  ·
    refine ⟨3079870996582047197751373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4106494662109396263668497 3079870996582047197751373)
    ·
      refine ⟨1154951623718267699156765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3079870996582047197751373 1154951623718267699156765)
      ·
        refine ⟨433106858894350387183787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1154951623718267699156765 433106858894350387183787)
        ·
          refine ⟨649660288341525580775681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433106858894350387183787 649660288341525580775681)
          ·
            refine ⟨487245216256144185581761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649660288341525580775681 487245216256144185581761)
            ·
              refine ⟨365433912192108139186321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487245216256144185581761 365433912192108139186321)
              ·
                refine ⟨274075434144081104389741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 365433912192108139186321 274075434144081104389741)
                ·
                  refine ⟨102778287804030414146153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274075434144081104389741 102778287804030414146153)
                  ·
                    rfl

theorem cell20_225180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_225180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225180 prefixEnd_225180 := by exact prefixLift 225180
  have htrace : WordTrace (prefixWord ++ tailWord_225180) baseStart_225180 baseEnd_225180 := by
    simpa [prefixWord, tailWord_225180, baseEnd_225180] using wordTrace_append hprefix tailTrace_225180
  have hstable : (prefixWord ++ tailWord_225180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225180).length < 2 ^ (prefixWord ++ tailWord_225180).sum := by decide
  have hdescent : baseEnd_225180 < baseStart_225180 := by decide
  rcases family_descends (prefixWord ++ tailWord_225180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225183 : List Nat := [1, 1, 2, 5, 3, 2, 2, 2, 2]
def baseStart_225183 : Nat := 118140960795 + 225183 * 2 ^ 59
def prefixEnd_225183 : Nat := 4983230072969 + 3 ^ 40 * 225183 * 2
def baseEnd_225183 : Nat := 102779657085775737046141

theorem tailTrace_225183 : CollatzResearch.WordTrace tailWord_225183 prefixEnd_225183 102779657085775737046141 := by
  unfold tailWord_225183
  simp only [CollatzResearch.WordTrace]
  refine ⟨8213098743207924039696203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5475399162138616026464135 8213098743207924039696203)
  ·
    refine ⟨12319648114811886059544305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8213098743207924039696203 12319648114811886059544305)
    ·
      refine ⟨9239736086108914544658229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12319648114811886059544305 9239736086108914544658229)
      ·
        refine ⟨866225258072710738561709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9239736086108914544658229 866225258072710738561709)
        ·
          refine ⟨324834471777266526960641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 866225258072710738561709 324834471777266526960641)
          ·
            refine ⟨243625853832949895220481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 324834471777266526960641 243625853832949895220481)
            ·
              refine ⟨182719390374712421415361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243625853832949895220481 182719390374712421415361)
              ·
                refine ⟨137039542781034316061521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182719390374712421415361 137039542781034316061521)
                ·
                  refine ⟨102779657085775737046141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137039542781034316061521 102779657085775737046141)
                  ·
                    rfl

theorem cell20_225183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 2, 2].length) (baseStart_225183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225183 prefixEnd_225183 := by exact prefixLift 225183
  have htrace : WordTrace (prefixWord ++ tailWord_225183) baseStart_225183 baseEnd_225183 := by
    simpa [prefixWord, tailWord_225183, baseEnd_225183] using wordTrace_append hprefix tailTrace_225183
  have hstable : (prefixWord ++ tailWord_225183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225183).length < 2 ^ (prefixWord ++ tailWord_225183).sum := by decide
  have hdescent : baseEnd_225183 < baseStart_225183 := by decide
  rcases family_descends (prefixWord ++ tailWord_225183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225201 : List Nat := [1, 2, 2, 4, 2, 1, 2, 3, 3]
def baseStart_225201 : Nat := 118140960795 + 225201 * 2 ^ 59
def prefixEnd_225201 : Nat := 4983230072969 + 3 ^ 40 * 225201 * 2
def baseEnd_225201 : Nat := 102787872776247674446067

theorem tailTrace_225201 : CollatzResearch.WordTrace tailWord_225201 prefixEnd_225201 102787872776247674446067 := by
  unfold tailWord_225201
  simp only [CollatzResearch.WordTrace]
  refine ⟨8213755257142713113851457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5475836838095142075900971 8213755257142713113851457)
  ·
    refine ⟨6160316442857034835388593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8213755257142713113851457 6160316442857034835388593)
    ·
      refine ⟨4620237332142776126541445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6160316442857034835388593 4620237332142776126541445)
      ·
        refine ⟨866294499776770523726521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4620237332142776126541445 866294499776770523726521)
        ·
          refine ⟨649720874832577892794891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 866294499776770523726521 649720874832577892794891)
          ·
            refine ⟨974581312248866839192337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 649720874832577892794891 974581312248866839192337)
            ·
              refine ⟨730935984186650129394253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 974581312248866839192337 730935984186650129394253)
              ·
                refine ⟨274100994069993798522845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 730935984186650129394253 274100994069993798522845)
                ·
                  refine ⟨102787872776247674446067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274100994069993798522845 102787872776247674446067)
                  ·
                    rfl

theorem cell20_225201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 3].length) (baseStart_225201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225201 prefixEnd_225201 := by exact prefixLift 225201
  have htrace : WordTrace (prefixWord ++ tailWord_225201) baseStart_225201 baseEnd_225201 := by
    simpa [prefixWord, tailWord_225201, baseEnd_225201] using wordTrace_append hprefix tailTrace_225201
  have hstable : (prefixWord ++ tailWord_225201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225201).length < 2 ^ (prefixWord ++ tailWord_225201).sum := by decide
  have hdescent : baseEnd_225201 < baseStart_225201 := by decide
  rcases family_descends (prefixWord ++ tailWord_225201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225204 : List Nat := [2, 5, 2, 1, 2, 1, 1, 2, 4]
def baseStart_225204 : Nat := 118140960795 + 225204 * 2 ^ 59
def prefixEnd_225204 : Nat := 4983230072969 + 3 ^ 40 * 225204 * 2
def baseEnd_225204 : Nat := 102789242057992997346055

theorem tailTrace_225204 : CollatzResearch.WordTrace tailWord_225204 prefixEnd_225204 102789242057992997346055 := by
  unfold tailWord_225204
  simp only [CollatzResearch.WordTrace]
  refine ⟨4106932338065922313105333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5475909784087896417473777 4106932338065922313105333)
  ·
    refine ⟨385024906693680216853625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4106932338065922313105333 385024906693680216853625)
    ·
      refine ⟨288768680020260162640219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 385024906693680216853625 288768680020260162640219)
      ·
        refine ⟨433153020030390243960329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 288768680020260162640219 433153020030390243960329)
        ·
          refine ⟨324864765022792682970247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 433153020030390243960329 324864765022792682970247)
          ·
            refine ⟨487297147534189024455371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324864765022792682970247 487297147534189024455371)
            ·
              refine ⟨730945721301283536683057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487297147534189024455371 730945721301283536683057)
              ·
                refine ⟨548209290975962652512293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 730945721301283536683057 548209290975962652512293)
                ·
                  refine ⟨102789242057992997346055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 548209290975962652512293 102789242057992997346055)
                  ·
                    rfl

theorem cell20_225204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_225204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225204 prefixEnd_225204 := by exact prefixLift 225204
  have htrace : WordTrace (prefixWord ++ tailWord_225204) baseStart_225204 baseEnd_225204 := by
    simpa [prefixWord, tailWord_225204, baseEnd_225204] using wordTrace_append hprefix tailTrace_225204
  have hstable : (prefixWord ++ tailWord_225204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225204).length < 2 ^ (prefixWord ++ tailWord_225204).sum := by decide
  have hdescent : baseEnd_225204 < baseStart_225204 := by decide
  rcases family_descends (prefixWord ++ tailWord_225204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225215 : List Nat := [1, 1, 2, 2, 2, 1, 7, 4]
def baseStart_225215 : Nat := 118140960795 + 225215 * 2 ^ 59
def prefixEnd_225215 : Nat := 4983230072969 + 3 ^ 40 * 225215 * 2
def baseEnd_225215 : Nat := 34264754252575282659781

theorem tailTrace_225215 : CollatzResearch.WordTrace tailWord_225215 prefixEnd_225215 34264754252575282659781 := by
  unfold tailWord_225215
  simp only [CollatzResearch.WordTrace]
  refine ⟨8214265879091993504861099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5476177252727995669907399 8214265879091993504861099)
  ·
    refine ⟨12321398818637990257291649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8214265879091993504861099 12321398818637990257291649)
    ·
      refine ⟨9241049113978492692968737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12321398818637990257291649 9241049113978492692968737)
      ·
        refine ⟨6930786835483869519726553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9241049113978492692968737 6930786835483869519726553)
        ·
          refine ⟨5198090126612902139794915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6930786835483869519726553 5198090126612902139794915)
          ·
            refine ⟨7797135189919353209692373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5198090126612902139794915 7797135189919353209692373)
            ·
              refine ⟨182745356013734840852165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 7797135189919353209692373 182745356013734840852165)
              ·
                refine ⟨34264754252575282659781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182745356013734840852165 34264754252575282659781)
                ·
                  rfl

theorem cell20_225215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 4].length) (baseStart_225215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225215 prefixEnd_225215 := by exact prefixLift 225215
  have htrace : WordTrace (prefixWord ++ tailWord_225215) baseStart_225215 baseEnd_225215 := by
    simpa [prefixWord, tailWord_225215, baseEnd_225215] using wordTrace_append hprefix tailTrace_225215
  have hstable : (prefixWord ++ tailWord_225215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225215).length < 2 ^ (prefixWord ++ tailWord_225215).sum := by decide
  have hdescent : baseEnd_225215 < baseStart_225215 := by decide
  rcases family_descends (prefixWord ++ tailWord_225215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225260 : List Nat := [2, 2, 1, 1, 2, 1, 1, 7, 3]
def baseStart_225260 : Nat := 118140960795 + 225260 * 2 ^ 59
def prefixEnd_225260 : Nat := 4983230072969 + 3 ^ 40 * 225260 * 2
def baseEnd_225260 : Nat := 102814801983905691479159

theorem tailTrace_225260 : CollatzResearch.WordTrace tailWord_225260 prefixEnd_225260 102814801983905691479159 := by
  unfold tailWord_225260
  simp only [CollatzResearch.WordTrace]
  refine ⟨4107953581964483095124617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5477271442619310793499489 4107953581964483095124617)
  ·
    refine ⟨3080965186473362321343463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4107953581964483095124617 3080965186473362321343463)
    ·
      refine ⟨4621447779710043482015195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3080965186473362321343463 4621447779710043482015195)
      ·
        refine ⟨6932171669565065223022793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4621447779710043482015195 6932171669565065223022793)
        ·
          refine ⟨5199128752173798917267095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6932171669565065223022793 5199128752173798917267095)
          ·
            refine ⟨7798693128260698375900643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5199128752173798917267095 7798693128260698375900643)
            ·
              refine ⟨11698039692391047563850965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7798693128260698375900643 11698039692391047563850965)
              ·
                refine ⟨274172805290415177277757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 11698039692391047563850965 274172805290415177277757)
                ·
                  refine ⟨102814801983905691479159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274172805290415177277757 102814801983905691479159)
                  ·
                    rfl

theorem cell20_225260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_225260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225260 prefixEnd_225260 := by exact prefixLift 225260
  have htrace : WordTrace (prefixWord ++ tailWord_225260) baseStart_225260 baseEnd_225260 := by
    simpa [prefixWord, tailWord_225260, baseEnd_225260] using wordTrace_append hprefix tailTrace_225260
  have hstable : (prefixWord ++ tailWord_225260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225260).length < 2 ^ (prefixWord ++ tailWord_225260).sum := by decide
  have hdescent : baseEnd_225260 < baseStart_225260 := by decide
  rcases family_descends (prefixWord ++ tailWord_225260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225270 : List Nat := [5, 1, 1, 1, 4, 1, 1, 6]
def baseStart_225270 : Nat := 118140960795 + 225270 * 2 ^ 59
def prefixEnd_225270 : Nat := 4983230072969 + 3 ^ 40 * 225270 * 2
def baseEnd_225270 : Nat := 34273122085463367048595

theorem tailTrace_225270 : CollatzResearch.WordTrace tailWord_225270 prefixEnd_225270 34273122085463367048595 := by
  unfold tailWord_225270
  simp only [CollatzResearch.WordTrace]
  refine ⟨513516993368296118632079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5477514595928491932075509 513516993368296118632079)
  ·
    refine ⟨770275490052444177948119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 513516993368296118632079 770275490052444177948119)
    ·
      refine ⟨1155413235078666266922179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 770275490052444177948119 1155413235078666266922179)
      ·
        refine ⟨1733119852617999400383269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1155413235078666266922179 1733119852617999400383269)
        ·
          refine ⟨324959972365874887571863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1733119852617999400383269 324959972365874887571863)
          ·
            refine ⟨487439958548812331357795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324959972365874887571863 487439958548812331357795)
            ·
              refine ⟨731159937823218497036693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487439958548812331357795 731159937823218497036693)
              ·
                refine ⟨34273122085463367048595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 731159937823218497036693 34273122085463367048595)
                ·
                  rfl

theorem cell20_225270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_225270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225270 prefixEnd_225270 := by exact prefixLift 225270
  have htrace : WordTrace (prefixWord ++ tailWord_225270) baseStart_225270 baseEnd_225270 := by
    simpa [prefixWord, tailWord_225270, baseEnd_225270] using wordTrace_append hprefix tailTrace_225270
  have hstable : (prefixWord ++ tailWord_225270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225270).length < 2 ^ (prefixWord ++ tailWord_225270).sum := by decide
  have hdescent : baseEnd_225270 < baseStart_225270 := by decide
  rcases family_descends (prefixWord ++ tailWord_225270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225293 : List Nat := [1, 7, 1, 2, 1, 1, 3, 2, 2]
def baseStart_225293 : Nat := 118140960795 + 225293 * 2 ^ 59
def prefixEnd_225293 : Nat := 4983230072969 + 3 ^ 40 * 225293 * 2
def baseEnd_225293 : Nat := 102829864083104243379025

theorem tailTrace_225293 : CollatzResearch.WordTrace tailWord_225293 prefixEnd_225293 102829864083104243379025 := by
  unfold tailWord_225293
  simp only [CollatzResearch.WordTrace]
  refine ⟨8217110772809412826200533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5478073848539608550800355 8217110772809412826200533)
  ·
    refine ⟨192588533737720613114075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 8217110772809412826200533 192588533737720613114075)
    ·
      refine ⟨288882800606580919671113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 192588533737720613114075 288882800606580919671113)
      ·
        refine ⟨216662100454935689753335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288882800606580919671113 216662100454935689753335)
        ·
          refine ⟨324993150682403534630003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216662100454935689753335 324993150682403534630003)
          ·
            refine ⟨487489726023605301945005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 324993150682403534630003 487489726023605301945005)
            ·
              refine ⟨182808647258851988229377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 487489726023605301945005 182808647258851988229377)
              ·
                refine ⟨137106485444138991172033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 182808647258851988229377 137106485444138991172033)
                ·
                  refine ⟨102829864083104243379025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137106485444138991172033 102829864083104243379025)
                  ·
                    rfl

theorem cell20_225293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_225293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225293 prefixEnd_225293 := by exact prefixLift 225293
  have htrace : WordTrace (prefixWord ++ tailWord_225293) baseStart_225293 baseEnd_225293 := by
    simpa [prefixWord, tailWord_225293, baseEnd_225293] using wordTrace_append hprefix tailTrace_225293
  have hstable : (prefixWord ++ tailWord_225293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225293).length < 2 ^ (prefixWord ++ tailWord_225293).sum := by decide
  have hdescent : baseEnd_225293 < baseStart_225293 := by decide
  rcases family_descends (prefixWord ++ tailWord_225293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225301 : List Nat := [1, 3, 2, 1, 5, 2, 1, 1, 4]
def baseStart_225301 : Nat := 118140960795 + 225301 * 2 ^ 59
def prefixEnd_225301 : Nat := 4983230072969 + 3 ^ 40 * 225301 * 2
def baseEnd_225301 : Nat := 102833515501091771112325

theorem tailTrace_225301 : CollatzResearch.WordTrace tailWord_225301 prefixEnd_225301 102833515501091771112325 := by
  unfold tailWord_225301
  simp only [CollatzResearch.WordTrace]
  refine ⟨8217402556780430192491757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5478268371186953461661171 8217402556780430192491757)
  ·
    refine ⟨3081525958792661322184409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8217402556780430192491757 3081525958792661322184409)
    ·
      refine ⟨2311144469094495991638307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3081525958792661322184409 2311144469094495991638307)
      ·
        refine ⟨3466716703641743987457461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2311144469094495991638307 3466716703641743987457461)
        ·
          refine ⟨325004690966413498824137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3466716703641743987457461 325004690966413498824137)
          ·
            refine ⟨243753518224810124118103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325004690966413498824137 243753518224810124118103)
            ·
              refine ⟨365630277337215186177155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243753518224810124118103 365630277337215186177155)
              ·
                refine ⟨548445416005822779265733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365630277337215186177155 548445416005822779265733)
                ·
                  refine ⟨102833515501091771112325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 548445416005822779265733 102833515501091771112325)
                  ·
                    rfl

theorem cell20_225301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 4].length) (baseStart_225301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225301 prefixEnd_225301 := by exact prefixLift 225301
  have htrace : WordTrace (prefixWord ++ tailWord_225301) baseStart_225301 baseEnd_225301 := by
    simpa [prefixWord, tailWord_225301, baseEnd_225301] using wordTrace_append hprefix tailTrace_225301
  have hstable : (prefixWord ++ tailWord_225301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225301).length < 2 ^ (prefixWord ++ tailWord_225301).sum := by decide
  have hdescent : baseEnd_225301 < baseStart_225301 := by decide
  rcases family_descends (prefixWord ++ tailWord_225301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225381 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 6]
def baseStart_225381 : Nat := 118140960795 + 225381 * 2 ^ 59
def prefixEnd_225381 : Nat := 4983230072969 + 3 ^ 40 * 225381 * 2
def baseEnd_225381 : Nat := 102870029680967048445331

theorem tailTrace_225381 : CollatzResearch.WordTrace tailWord_225381 prefixEnd_225381 102870029680967048445331 := by
  unfold tailWord_225381
  simp only [CollatzResearch.WordTrace]
  refine ⟨8220320396490603855403997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5480213597660402570269331 8220320396490603855403997)
  ·
    refine ⟨3082620148683976445776499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8220320396490603855403997 3082620148683976445776499)
    ·
      refine ⟨4623930223025964668664749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3082620148683976445776499 4623930223025964668664749)
      ·
        refine ⟨1733973833634736750749281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4623930223025964668664749 1733973833634736750749281)
        ·
          refine ⟨1300480375226052563061961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1733973833634736750749281 1300480375226052563061961)
          ·
            refine ⟨975360281419539422296471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1300480375226052563061961 975360281419539422296471)
            ·
              refine ⟨1463040422129309133444707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 975360281419539422296471 1463040422129309133444707)
              ·
                refine ⟨2194560633193963700167061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1463040422129309133444707 2194560633193963700167061)
                ·
                  refine ⟨102870029680967048445331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2194560633193963700167061 102870029680967048445331)
                  ·
                    rfl

theorem cell20_225381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_225381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225381 prefixEnd_225381 := by exact prefixLift 225381
  have htrace : WordTrace (prefixWord ++ tailWord_225381) baseStart_225381 baseEnd_225381 := by
    simpa [prefixWord, tailWord_225381, baseEnd_225381] using wordTrace_append hprefix tailTrace_225381
  have hstable : (prefixWord ++ tailWord_225381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225381).length < 2 ^ (prefixWord ++ tailWord_225381).sum := by decide
  have hdescent : baseEnd_225381 < baseStart_225381 := by decide
  rcases family_descends (prefixWord ++ tailWord_225381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225412 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 5]
def baseStart_225412 : Nat := 118140960795 + 225412 * 2 ^ 59
def prefixEnd_225412 : Nat := 4983230072969 + 3 ^ 40 * 225412 * 2
def baseEnd_225412 : Nat := 102884178925668718411871

theorem tailTrace_225412 : CollatzResearch.WordTrace tailWord_225412 prefixEnd_225412 102884178925668718411871 := by
  unfold tailWord_225412
  simp only [CollatzResearch.WordTrace]
  refine ⟨4110725529689148074891245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5480967372918864099854993 4110725529689148074891245)
  ·
    refine ⟨1541522073633430528084217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4110725529689148074891245 1541522073633430528084217)
    ·
      refine ⟨1156141555225072896063163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1541522073633430528084217 1156141555225072896063163)
      ·
        refine ⟨1734212332837609344094745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1156141555225072896063163 1734212332837609344094745)
        ·
          refine ⟨1300659249628207008071059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1734212332837609344094745 1300659249628207008071059)
          ·
            refine ⟨1950988874442310512106589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300659249628207008071059 1950988874442310512106589)
            ·
              refine ⟨731620827915866442039971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1950988874442310512106589 731620827915866442039971)
              ·
                refine ⟨1097431241873799663059957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 731620827915866442039971 1097431241873799663059957)
                ·
                  refine ⟨102884178925668718411871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1097431241873799663059957 102884178925668718411871)
                  ·
                    rfl

theorem cell20_225412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_225412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225412 prefixEnd_225412 := by exact prefixLift 225412
  have htrace : WordTrace (prefixWord ++ tailWord_225412) baseStart_225412 baseEnd_225412 := by
    simpa [prefixWord, tailWord_225412, baseEnd_225412] using wordTrace_append hprefix tailTrace_225412
  have hstable : (prefixWord ++ tailWord_225412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225412).length < 2 ^ (prefixWord ++ tailWord_225412).sum := by decide
  have hdescent : baseEnd_225412 < baseStart_225412 := by decide
  rcases family_descends (prefixWord ++ tailWord_225412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225429 : List Nat := [1, 3, 2, 1, 1, 1, 7, 1, 3]
def baseStart_225429 : Nat := 118140960795 + 225429 * 2 ^ 59
def prefixEnd_225429 : Nat := 4983230072969 + 3 ^ 40 * 225429 * 2
def baseEnd_225429 : Nat := 102891938188892214845135

theorem tailTrace_225429 : CollatzResearch.WordTrace tailWord_225429 prefixEnd_225429 102891938188892214845135 := by
  unfold tailWord_225429
  simp only [CollatzResearch.WordTrace]
  refine ⟨8222071100316708053151341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5481380733544472035434227 8222071100316708053151341)
  ·
    refine ⟨3083276662618765519931753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8222071100316708053151341 3083276662618765519931753)
    ·
      refine ⟨2312457496964074139948815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3083276662618765519931753 2312457496964074139948815)
      ·
        refine ⟨3468686245446111209923223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2312457496964074139948815 3468686245446111209923223)
        ·
          refine ⟨5203029368169166814884835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3468686245446111209923223 5203029368169166814884835)
          ·
            refine ⟨7804544052253750222327253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5203029368169166814884835 7804544052253750222327253)
            ·
              refine ⟨182919001224697270835795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 7804544052253750222327253 182919001224697270835795)
              ·
                refine ⟨274378501837045906253693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 182919001224697270835795 274378501837045906253693)
                ·
                  refine ⟨102891938188892214845135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274378501837045906253693 102891938188892214845135)
                  ·
                    rfl

theorem cell20_225429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_225429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225429 prefixEnd_225429 := by exact prefixLift 225429
  have htrace : WordTrace (prefixWord ++ tailWord_225429) baseStart_225429 baseEnd_225429 := by
    simpa [prefixWord, tailWord_225429, baseEnd_225429] using wordTrace_append hprefix tailTrace_225429
  have hstable : (prefixWord ++ tailWord_225429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225429).length < 2 ^ (prefixWord ++ tailWord_225429).sum := by decide
  have hdescent : baseEnd_225429 < baseStart_225429 := by decide
  rcases family_descends (prefixWord ++ tailWord_225429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225470 : List Nat := [4, 2, 1, 1, 5, 1, 1, 1, 4]
def baseStart_225470 : Nat := 118140960795 + 225470 * 2 ^ 59
def prefixEnd_225470 : Nat := 4983230072969 + 3 ^ 40 * 225470 * 2
def baseEnd_225470 : Nat := 102910651706078294478301

theorem tailTrace_225470 : CollatzResearch.WordTrace tailWord_225470 prefixEnd_225470 102910651706078294478301 := by
  unfold tailWord_225470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1027945811646021506924233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5482377662112114703595909 1027945811646021506924233)
  ·
    refine ⟨770959358734516130193175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1027945811646021506924233 770959358734516130193175)
    ·
      refine ⟨1156439038101774195289763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 770959358734516130193175 1156439038101774195289763)
      ·
        refine ⟨1734658557152661292934645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1156439038101774195289763 1734658557152661292934645)
        ·
          refine ⟨162624239733061996212623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1734658557152661292934645 162624239733061996212623)
          ·
            refine ⟨243936359599592994318935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162624239733061996212623 243936359599592994318935)
            ·
              refine ⟨365904539399389491478403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 243936359599592994318935 365904539399389491478403)
              ·
                refine ⟨548856809099084237217605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 365904539399389491478403 548856809099084237217605)
                ·
                  refine ⟨102910651706078294478301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 548856809099084237217605 102910651706078294478301)
                  ·
                    rfl

theorem cell20_225470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_225470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225470 prefixEnd_225470 := by exact prefixLift 225470
  have htrace : WordTrace (prefixWord ++ tailWord_225470) baseStart_225470 baseEnd_225470 := by
    simpa [prefixWord, tailWord_225470, baseEnd_225470] using wordTrace_append hprefix tailTrace_225470
  have hstable : (prefixWord ++ tailWord_225470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225470).length < 2 ^ (prefixWord ++ tailWord_225470).sum := by decide
  have hdescent : baseEnd_225470 < baseStart_225470 := by decide
  rcases family_descends (prefixWord ++ tailWord_225470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225484 : List Nat := [2, 2, 1, 6, 1, 1, 1, 3, 3]
def baseStart_225484 : Nat := 118140960795 + 225484 * 2 ^ 59
def prefixEnd_225484 : Nat := 4983230072969 + 3 ^ 40 * 225484 * 2
def baseEnd_225484 : Nat := 102917041687556468011577

theorem tailTrace_225484 : CollatzResearch.WordTrace tailWord_225484 prefixEnd_225484 102917041687556468011577 := by
  unfold tailWord_225484
  simp only [CollatzResearch.WordTrace]
  refine ⟨4112038557558726223201753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5482718076744968297602337 4112038557558726223201753)
  ·
    refine ⟨3084028918169044667401315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4112038557558726223201753 3084028918169044667401315)
    ·
      refine ⟨4626043377253567001101973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3084028918169044667401315 4626043377253567001101973)
      ·
        refine ⟨216845783308760953176655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4626043377253567001101973 216845783308760953176655)
        ·
          refine ⟨325268674963141429764983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216845783308760953176655 325268674963141429764983)
          ·
            refine ⟨487903012444712144647475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 325268674963141429764983 487903012444712144647475)
            ·
              refine ⟨731854518667068216971213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 487903012444712144647475 731854518667068216971213)
              ·
                refine ⟨274445444500150581364205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 731854518667068216971213 274445444500150581364205)
                ·
                  refine ⟨102917041687556468011577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274445444500150581364205 102917041687556468011577)
                  ·
                    rfl

theorem cell20_225484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_225484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225484 prefixEnd_225484 := by exact prefixLift 225484
  have htrace : WordTrace (prefixWord ++ tailWord_225484) baseStart_225484 baseEnd_225484 := by
    simpa [prefixWord, tailWord_225484, baseEnd_225484] using wordTrace_append hprefix tailTrace_225484
  have hstable : (prefixWord ++ tailWord_225484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225484).length < 2 ^ (prefixWord ++ tailWord_225484).sum := by decide
  have hdescent : baseEnd_225484 < baseStart_225484 := by decide
  rcases family_descends (prefixWord ++ tailWord_225484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225526 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_225526 : Nat := 118140960795 + 225526 * 2 ^ 59
def prefixEnd_225526 : Nat := 4983230072969 + 3 ^ 40 * 225526 * 2
def baseEnd_225526 : Nat := 102936211631990988611405

theorem tailTrace_225526 : CollatzResearch.WordTrace tailWord_225526 prefixEnd_225526 102936211631990988611405 := by
  unfold tailWord_225526
  simp only [CollatzResearch.WordTrace]
  refine ⟨514100561310330851214527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5483739320643529079621621 514100561310330851214527)
  ·
    refine ⟨771150841965496276821791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 514100561310330851214527 771150841965496276821791)
    ·
      refine ⟨1156726262948244415232687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 771150841965496276821791 1156726262948244415232687)
      ·
        refine ⟨1735089394422366622849031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1156726262948244415232687 1735089394422366622849031)
        ·
          refine ⟨2602634091633549934273547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1735089394422366622849031 2602634091633549934273547)
          ·
            refine ⟨3903951137450324901410321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2602634091633549934273547 3903951137450324901410321)
            ·
              refine ⟨2927963353087743676057741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3903951137450324901410321 2927963353087743676057741)
              ·
                refine ⟨1097986257407903878521653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2927963353087743676057741 1097986257407903878521653)
                ·
                  refine ⟨102936211631990988611405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1097986257407903878521653 102936211631990988611405)
                  ·
                    rfl

theorem cell20_225526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_225526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225526 prefixEnd_225526 := by exact prefixLift 225526
  have htrace : WordTrace (prefixWord ++ tailWord_225526) baseStart_225526 baseEnd_225526 := by
    simpa [prefixWord, tailWord_225526, baseEnd_225526] using wordTrace_append hprefix tailTrace_225526
  have hstable : (prefixWord ++ tailWord_225526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225526).length < 2 ^ (prefixWord ++ tailWord_225526).sum := by decide
  have hdescent : baseEnd_225526 < baseStart_225526 := by decide
  rcases family_descends (prefixWord ++ tailWord_225526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225567 : List Nat := [1, 1, 2, 4, 3, 2, 2, 3, 2]
def baseStart_225567 : Nat := 118140960795 + 225567 * 2 ^ 59
def prefixEnd_225567 : Nat := 4983230072969 + 3 ^ 40 * 225567 * 2
def baseEnd_225567 : Nat := 102954925149177068244571

theorem tailTrace_225567 : CollatzResearch.WordTrace tailWord_225567 prefixEnd_225567 102954925149177068244571 := by
  unfold tailWord_225567
  simp only [CollatzResearch.WordTrace]
  refine ⟨8227104373816757621674955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5484736249211171747783303 8227104373816757621674955)
  ·
    refine ⟨12340656560725136432512433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8227104373816757621674955 12340656560725136432512433)
    ·
      refine ⟨9255492420543852324384325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12340656560725136432512433 9255492420543852324384325)
      ·
        refine ⟨1735404828851972310822061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9255492420543852324384325 1735404828851972310822061)
        ·
          refine ⟨650776810819489616558273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1735404828851972310822061 650776810819489616558273)
          ·
            refine ⟨488082608114617212418705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 650776810819489616558273 488082608114617212418705)
            ·
              refine ⟨366061956085962909314029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 488082608114617212418705 366061956085962909314029)
              ·
                refine ⟨137273233532236090992761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 366061956085962909314029 137273233532236090992761)
                ·
                  refine ⟨102954925149177068244571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 137273233532236090992761 102954925149177068244571)
                  ·
                    rfl

theorem cell20_225567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 2].length) (baseStart_225567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225567 prefixEnd_225567 := by exact prefixLift 225567
  have htrace : WordTrace (prefixWord ++ tailWord_225567) baseStart_225567 baseEnd_225567 := by
    simpa [prefixWord, tailWord_225567, baseEnd_225567] using wordTrace_append hprefix tailTrace_225567
  have hstable : (prefixWord ++ tailWord_225567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225567).length < 2 ^ (prefixWord ++ tailWord_225567).sum := by decide
  have hdescent : baseEnd_225567 < baseStart_225567 := by decide
  rcases family_descends (prefixWord ++ tailWord_225567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225588 : List Nat := [2, 5, 1, 1, 1, 2, 1, 3, 4]
def baseStart_225588 : Nat := 118140960795 + 225588 * 2 ^ 59
def prefixEnd_225588 : Nat := 4983230072969 + 3 ^ 40 * 225588 * 2
def baseEnd_225588 : Nat := 102964510121394328544485

theorem tailTrace_225588 : CollatzResearch.WordTrace tailWord_225588 prefixEnd_225588 102964510121394328544485 := by
  unfold tailWord_225588
  simp only [CollatzResearch.WordTrace]
  refine ⟨4113935153370339104094709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5485246871160452138792945 4113935153370339104094709)
  ·
    refine ⟨385681420628469291008879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4113935153370339104094709 385681420628469291008879)
    ·
      refine ⟨578522130942703936513319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385681420628469291008879 578522130942703936513319)
      ·
        refine ⟨867783196414055904769979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 578522130942703936513319 867783196414055904769979)
        ·
          refine ⟨1301674794621083857154969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867783196414055904769979 1301674794621083857154969)
          ·
            refine ⟨976256095965812892866227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1301674794621083857154969 976256095965812892866227)
            ·
              refine ⟨1464384143948719339299341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 976256095965812892866227 1464384143948719339299341)
              ·
                refine ⟨549144053980769752237253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1464384143948719339299341 549144053980769752237253)
                ·
                  refine ⟨102964510121394328544485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 549144053980769752237253 102964510121394328544485)
                  ·
                    rfl

theorem cell20_225588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_225588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225588 prefixEnd_225588 := by exact prefixLift 225588
  have htrace : WordTrace (prefixWord ++ tailWord_225588) baseStart_225588 baseEnd_225588 := by
    simpa [prefixWord, tailWord_225588, baseEnd_225588] using wordTrace_append hprefix tailTrace_225588
  have hstable : (prefixWord ++ tailWord_225588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225588).length < 2 ^ (prefixWord ++ tailWord_225588).sum := by decide
  have hdescent : baseEnd_225588 < baseStart_225588 := by decide
  rcases family_descends (prefixWord ++ tailWord_225588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225598 : List Nat := [4, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_225598 : Nat := 118140960795 + 225598 * 2 ^ 59
def prefixEnd_225598 : Nat := 4983230072969 + 3 ^ 40 * 225598 * 2
def baseEnd_225598 : Nat := 102969074393878738211111

theorem tailTrace_225598 : CollatzResearch.WordTrace tailWord_225598 prefixEnd_225598 102969074393878738211111 := by
  unfold tailWord_225598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1028529379588056239506681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5485490024469633277368965 1028529379588056239506681)
  ·
    refine ⟨771397034691042179630011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1028529379588056239506681 771397034691042179630011)
    ·
      refine ⟨1157095552036563269445017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 771397034691042179630011 1157095552036563269445017)
      ·
        refine ⟨867821664027422452083763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1157095552036563269445017 867821664027422452083763)
        ·
          refine ⟨1301732496041133678125645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867821664027422452083763 1301732496041133678125645)
          ·
            refine ⟨488149686015425129297117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1301732496041133678125645 488149686015425129297117)
            ·
              refine ⟨183056132255784423486419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 488149686015425129297117 183056132255784423486419)
              ·
                refine ⟨274584198383676635229629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 183056132255784423486419 274584198383676635229629)
                ·
                  refine ⟨102969074393878738211111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274584198383676635229629 102969074393878738211111)
                  ·
                    rfl

theorem cell20_225598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_225598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225598 prefixEnd_225598 := by exact prefixLift 225598
  have htrace : WordTrace (prefixWord ++ tailWord_225598) baseStart_225598 baseEnd_225598 := by
    simpa [prefixWord, tailWord_225598, baseEnd_225598] using wordTrace_append hprefix tailTrace_225598
  have hstable : (prefixWord ++ tailWord_225598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225598).length < 2 ^ (prefixWord ++ tailWord_225598).sum := by decide
  have hdescent : baseEnd_225598 < baseStart_225598 := by decide
  rcases family_descends (prefixWord ++ tailWord_225598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225616 : List Nat := [2, 1, 1, 1, 1, 7, 1, 6]
def baseStart_225616 : Nat := 118140960795 + 225616 * 2 ^ 59
def prefixEnd_225616 : Nat := 4983230072969 + 3 ^ 40 * 225616 * 2
def baseEnd_225616 : Nat := 34325763361450225203679

theorem tailTrace_225616 : CollatzResearch.WordTrace tailWord_225616 prefixEnd_225616 34325763361450225203679 := by
  unfold tailWord_225616
  simp only [CollatzResearch.WordTrace]
  refine ⟨4114445775319619495104351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5485927700426159326805801 4114445775319619495104351)
  ·
    refine ⟨6171668662979429242656527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4114445775319619495104351 6171668662979429242656527)
    ·
      refine ⟨9257502994469143863984791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6171668662979429242656527 9257502994469143863984791)
      ·
        refine ⟨13886254491703715795977187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9257502994469143863984791 13886254491703715795977187)
        ·
          refine ⟨20829381737555573693965781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13886254491703715795977187 20829381737555573693965781)
          ·
            refine ⟨488188634473958758452323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 20829381737555573693965781 488188634473958758452323)
            ·
              refine ⟨732282951710938137678485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 488188634473958758452323 732282951710938137678485)
              ·
                refine ⟨34325763361450225203679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 732282951710938137678485 34325763361450225203679)
                ·
                  rfl

theorem cell20_225616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_225616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225616 prefixEnd_225616 := by exact prefixLift 225616
  have htrace : WordTrace (prefixWord ++ tailWord_225616) baseStart_225616 baseEnd_225616 := by
    simpa [prefixWord, tailWord_225616, baseEnd_225616] using wordTrace_append hprefix tailTrace_225616
  have hstable : (prefixWord ++ tailWord_225616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225616).length < 2 ^ (prefixWord ++ tailWord_225616).sum := by decide
  have hdescent : baseEnd_225616 < baseStart_225616 := by decide
  rcases family_descends (prefixWord ++ tailWord_225616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225623 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 7]
def baseStart_225623 : Nat := 118140960795 + 225623 * 2 ^ 59
def prefixEnd_225623 : Nat := 4983230072969 + 3 ^ 40 * 225623 * 2
def baseEnd_225623 : Nat := 102980485075089762377675

theorem tailTrace_225623 : CollatzResearch.WordTrace tailWord_225623 prefixEnd_225623 102980485075089762377675 := by
  unfold tailWord_225623
  simp only [CollatzResearch.WordTrace]
  refine ⟨8229146861613879185713523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5486097907742586123809015 8229146861613879185713523)
  ·
    refine ⟨12343720292420818778570285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8229146861613879185713523 12343720292420818778570285)
    ·
      refine ⟨4628895109657807041963857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12343720292420818778570285 4628895109657807041963857)
      ·
        refine ⟨3471671332243355281472893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4628895109657807041963857 3471671332243355281472893)
        ·
          refine ⟨1301876749591258230552335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3471671332243355281472893 1301876749591258230552335)
          ·
            refine ⟨1952815124386887345828503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1301876749591258230552335 1952815124386887345828503)
            ·
              refine ⟨2929222686580331018742755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1952815124386887345828503 2929222686580331018742755)
              ·
                refine ⟨4393834029870496528114133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2929222686580331018742755 4393834029870496528114133)
                ·
                  refine ⟨102980485075089762377675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4393834029870496528114133 102980485075089762377675)
                  ·
                    rfl

theorem cell20_225623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 7].length) (baseStart_225623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225623 prefixEnd_225623 := by exact prefixLift 225623
  have htrace : WordTrace (prefixWord ++ tailWord_225623) baseStart_225623 baseEnd_225623 := by
    simpa [prefixWord, tailWord_225623, baseEnd_225623] using wordTrace_append hprefix tailTrace_225623
  have hstable : (prefixWord ++ tailWord_225623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225623).length < 2 ^ (prefixWord ++ tailWord_225623).sum := by decide
  have hdescent : baseEnd_225623 < baseStart_225623 := by decide
  rcases family_descends (prefixWord ++ tailWord_225623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225640 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 5]
def baseStart_225640 : Nat := 118140960795 + 225640 * 2 ^ 59
def prefixEnd_225640 : Nat := 4983230072969 + 3 ^ 40 * 225640 * 2
def baseEnd_225640 : Nat := 102988244338313258810939

theorem tailTrace_225640 : CollatzResearch.WordTrace tailWord_225640 prefixEnd_225640 102988244338313258810939 := by
  unfold tailWord_225640
  simp only [CollatzResearch.WordTrace]
  refine ⟨4114883451276145544541187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5486511268368194059388249 4114883451276145544541187)
  ·
    refine ⟨6172325176914218316811781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4114883451276145544541187 6172325176914218316811781)
    ·
      refine ⟨1157310970671415934402209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6172325176914218316811781 1157310970671415934402209)
      ·
        refine ⟨867983228003561950801657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1157310970671415934402209 867983228003561950801657)
        ·
          refine ⟨650987421002671463101243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 867983228003561950801657 650987421002671463101243)
          ·
            refine ⟨976481131504007194651865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 650987421002671463101243 976481131504007194651865)
            ·
              refine ⟨732360848628005395988899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 976481131504007194651865 732360848628005395988899)
              ·
                refine ⟨1098541272942008093983349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 732360848628005395988899 1098541272942008093983349)
                ·
                  refine ⟨102988244338313258810939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1098541272942008093983349 102988244338313258810939)
                  ·
                    rfl

theorem cell20_225640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_225640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225640 prefixEnd_225640 := by exact prefixLift 225640
  have htrace : WordTrace (prefixWord ++ tailWord_225640) baseStart_225640 baseEnd_225640 := by
    simpa [prefixWord, tailWord_225640, baseEnd_225640] using wordTrace_append hprefix tailTrace_225640
  have hstable : (prefixWord ++ tailWord_225640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225640).length < 2 ^ (prefixWord ++ tailWord_225640).sum := by decide
  have hdescent : baseEnd_225640 < baseStart_225640 := by decide
  rcases family_descends (prefixWord ++ tailWord_225640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225761 : List Nat := [1, 2, 3, 1, 2, 2, 4, 1, 4]
def baseStart_225761 : Nat := 118140960795 + 225761 * 2 ^ 59
def prefixEnd_225761 : Nat := 4983230072969 + 3 ^ 40 * 225761 * 2
def baseEnd_225761 : Nat := 103043472035374615777111

theorem tailTrace_225761 : CollatzResearch.WordTrace tailWord_225761 prefixEnd_225761 103043472035374615777111 := by
  unfold tailWord_225761
  simp only [CollatzResearch.WordTrace]
  refine ⟨8234180135113928754237137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5489453423409285836158091 8234180135113928754237137)
  ·
    refine ⟨6175635101335446565677853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8234180135113928754237137 6175635101335446565677853)
    ·
      refine ⟨2315863163000792462129195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6175635101335446565677853 2315863163000792462129195)
      ·
        refine ⟨3473794744501188693193793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2315863163000792462129195 3473794744501188693193793)
        ·
          refine ⟨2605346058375891519895345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3473794744501188693193793 2605346058375891519895345)
          ·
            refine ⟨1954009543781918639921509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2605346058375891519895345 1954009543781918639921509)
            ·
              refine ⟨366376789459109744985283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1954009543781918639921509 366376789459109744985283)
              ·
                refine ⟨549565184188664617477925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366376789459109744985283 549565184188664617477925)
                ·
                  refine ⟨103043472035374615777111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 549565184188664617477925 103043472035374615777111)
                  ·
                    rfl

theorem cell20_225761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 4].length) (baseStart_225761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225761 prefixEnd_225761 := by exact prefixLift 225761
  have htrace : WordTrace (prefixWord ++ tailWord_225761) baseStart_225761 baseEnd_225761 := by
    simpa [prefixWord, tailWord_225761, baseEnd_225761] using wordTrace_append hprefix tailTrace_225761
  have hstable : (prefixWord ++ tailWord_225761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225761).length < 2 ^ (prefixWord ++ tailWord_225761).sum := by decide
  have hdescent : baseEnd_225761 < baseStart_225761 := by decide
  rcases family_descends (prefixWord ++ tailWord_225761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225781 : List Nat := [1, 3, 5, 1, 2, 2, 2, 4]
def baseStart_225781 : Nat := 118140960795 + 225781 * 2 ^ 59
def prefixEnd_225781 : Nat := 4983230072969 + 3 ^ 40 * 225781 * 2
def baseEnd_225781 : Nat := 34350866860114478370121

theorem tailTrace_225781 : CollatzResearch.WordTrace tailWord_225781 prefixEnd_225781 34350866860114478370121 := by
  unfold tailWord_225781
  simp only [CollatzResearch.WordTrace]
  refine ⟨8234909595041472169965197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5489939730027648113310131 8234909595041472169965197)
  ·
    refine ⟨3088091098140552063736949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8234909595041472169965197 3088091098140552063736949)
    ·
      refine ⟨289508540450676755975339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3088091098140552063736949 289508540450676755975339)
      ·
        refine ⟨434262810676015133963009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 289508540450676755975339 434262810676015133963009)
        ·
          refine ⟨325697108007011350472257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 434262810676015133963009 325697108007011350472257)
          ·
            refine ⟨244272831005258512854193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325697108007011350472257 244272831005258512854193)
            ·
              refine ⟨183204623253943884640645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 244272831005258512854193 183204623253943884640645)
              ·
                refine ⟨34350866860114478370121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183204623253943884640645 34350866860114478370121)
                ·
                  rfl

theorem cell20_225781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 4].length) (baseStart_225781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225781 prefixEnd_225781 := by exact prefixLift 225781
  have htrace : WordTrace (prefixWord ++ tailWord_225781) baseStart_225781 baseEnd_225781 := by
    simpa [prefixWord, tailWord_225781, baseEnd_225781] using wordTrace_append hprefix tailTrace_225781
  have hstable : (prefixWord ++ tailWord_225781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225781).length < 2 ^ (prefixWord ++ tailWord_225781).sum := by decide
  have hdescent : baseEnd_225781 < baseStart_225781 := by decide
  rcases family_descends (prefixWord ++ tailWord_225781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225806 : List Nat := [4, 1, 1, 2, 3, 1, 8]
def baseStart_225806 : Nat := 118140960795 + 225806 * 2 ^ 59
def prefixEnd_225806 : Nat := 4983230072969 + 3 ^ 40 * 225806 * 2
def baseEnd_225806 : Nat := 11451556806839384364103

theorem tailTrace_225806 : CollatzResearch.WordTrace tailWord_225806 prefixEnd_225806 11451556806839384364103 := by
  unfold tailWord_225806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1029477677493862679953159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5490547613300600959750181 1029477677493862679953159)
  ·
    refine ⟨1544216516240794019929739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1029477677493862679953159 1544216516240794019929739)
    ·
      refine ⟨2316324774361191029894609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1544216516240794019929739 2316324774361191029894609)
      ·
        refine ⟨1737243580770893272420957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2316324774361191029894609 1737243580770893272420957)
        ·
          refine ⟨651466342789084977157859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1737243580770893272420957 651466342789084977157859)
          ·
            refine ⟨977199514183627465736789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 651466342789084977157859 977199514183627465736789)
            ·
              refine ⟨11451556806839384364103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 977199514183627465736789 11451556806839384364103)
              ·
                rfl

theorem cell20_225806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 8].length) (baseStart_225806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225806 prefixEnd_225806 := by exact prefixLift 225806
  have htrace : WordTrace (prefixWord ++ tailWord_225806) baseStart_225806 baseEnd_225806 := by
    simpa [prefixWord, tailWord_225806, baseEnd_225806] using wordTrace_append hprefix tailTrace_225806
  have hstable : (prefixWord ++ tailWord_225806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225806).length < 2 ^ (prefixWord ++ tailWord_225806).sum := by decide
  have hdescent : baseEnd_225806 < baseStart_225806 := by decide
  rcases family_descends (prefixWord ++ tailWord_225806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225813 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 5]
def baseStart_225813 : Nat := 118140960795 + 225813 * 2 ^ 59
def prefixEnd_225813 : Nat := 4983230072969 + 3 ^ 40 * 225813 * 2
def baseEnd_225813 : Nat := 103067206252293546043565

theorem tailTrace_225813 : CollatzResearch.WordTrace tailWord_225813 prefixEnd_225813 103067206252293546043565 := by
  unfold tailWord_225813
  simp only [CollatzResearch.WordTrace]
  refine ⟨8236076730925541635130093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5490717820617027756753395 8236076730925541635130093)
  ·
    refine ⟨3088528774097078113173785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8236076730925541635130093 3088528774097078113173785)
    ·
      refine ⟨2316396580572808584880339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3088528774097078113173785 2316396580572808584880339)
      ·
        refine ⟨3474594870859212877320509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2316396580572808584880339 3474594870859212877320509)
        ·
          refine ⟨1302973076572204828995191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3474594870859212877320509 1302973076572204828995191)
          ·
            refine ⟨1954459614858307243492787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1302973076572204828995191 1954459614858307243492787)
            ·
              refine ⟨2931689422287460865239181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1954459614858307243492787 2931689422287460865239181)
              ·
                refine ⟨1099383533357797824464693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2931689422287460865239181 1099383533357797824464693)
                ·
                  refine ⟨103067206252293546043565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1099383533357797824464693 103067206252293546043565)
                  ·
                    rfl

theorem cell20_225813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_225813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225813 prefixEnd_225813 := by exact prefixLift 225813
  have htrace : WordTrace (prefixWord ++ tailWord_225813) baseStart_225813 baseEnd_225813 := by
    simpa [prefixWord, tailWord_225813, baseEnd_225813] using wordTrace_append hprefix tailTrace_225813
  have hstable : (prefixWord ++ tailWord_225813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225813).length < 2 ^ (prefixWord ++ tailWord_225813).sum := by decide
  have hdescent : baseEnd_225813 < baseStart_225813 := by decide
  rcases family_descends (prefixWord ++ tailWord_225813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225816 : List Nat := [2, 1, 2, 3, 3, 3, 1, 1, 4]
def baseStart_225816 : Nat := 118140960795 + 225816 * 2 ^ 59
def prefixEnd_225816 : Nat := 4983230072969 + 3 ^ 40 * 225816 * 2
def baseEnd_225816 : Nat := 103068575534038868943553

theorem tailTrace_225816 : CollatzResearch.WordTrace tailWord_225816 prefixEnd_225816 103068575534038868943553 := by
  unfold tailWord_225816
  simp only [CollatzResearch.WordTrace]
  refine ⟨4118093074957336573744651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5490790766609782098326201 4118093074957336573744651)
  ·
    refine ⟨6177139612436004860616977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4118093074957336573744651 6177139612436004860616977)
    ·
      refine ⟨4632854709327003645462733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6177139612436004860616977 4632854709327003645462733)
      ·
        refine ⟨1737320515997626367048525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4632854709327003645462733 1737320515997626367048525)
        ·
          refine ⟨651495193499109887643197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1737320515997626367048525 651495193499109887643197)
          ·
            refine ⟨244310697562166207866199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 651495193499109887643197 244310697562166207866199)
            ·
              refine ⟨366466046343249311799299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 244310697562166207866199 366466046343249311799299)
              ·
                refine ⟨549699069514873967698949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 366466046343249311799299 549699069514873967698949)
                ·
                  refine ⟨103068575534038868943553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 549699069514873967698949 103068575534038868943553)
                  ·
                    rfl

theorem cell20_225816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 1, 4].length) (baseStart_225816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225816 prefixEnd_225816 := by exact prefixLift 225816
  have htrace : WordTrace (prefixWord ++ tailWord_225816) baseStart_225816 baseEnd_225816 := by
    simpa [prefixWord, tailWord_225816, baseEnd_225816] using wordTrace_append hprefix tailTrace_225816
  have hstable : (prefixWord ++ tailWord_225816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225816).length < 2 ^ (prefixWord ++ tailWord_225816).sum := by decide
  have hdescent : baseEnd_225816 < baseStart_225816 := by decide
  rcases family_descends (prefixWord ++ tailWord_225816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225868 : List Nat := [2, 2, 1, 3, 1, 2, 4, 2, 3]
def baseStart_225868 : Nat := 118140960795 + 225868 * 2 ^ 59
def prefixEnd_225868 : Nat := 4983230072969 + 3 ^ 40 * 225868 * 2
def baseEnd_225868 : Nat := 103092309750957799210007

theorem tailTrace_225868 : CollatzResearch.WordTrace tailWord_225868 prefixEnd_225868 103092309750957799210007 := by
  unfold tailWord_225868
  simp only [CollatzResearch.WordTrace]
  refine ⟨4119041372863143014191129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5492055163817524018921505 4119041372863143014191129)
  ·
    refine ⟨3089281029647357260643347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4119041372863143014191129 3089281029647357260643347)
    ·
      refine ⟨4633921544471035890965021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3089281029647357260643347 4633921544471035890965021)
      ·
        refine ⟨1737720579176638459111883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4633921544471035890965021 1737720579176638459111883)
        ·
          refine ⟨2606580868764957688667825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1737720579176638459111883 2606580868764957688667825)
          ·
            refine ⟨1954935651573718266500869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2606580868764957688667825 1954935651573718266500869)
            ·
              refine ⟨366550434670072174968913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1954935651573718266500869 366550434670072174968913)
              ·
                refine ⟨274912826002554131226685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 366550434670072174968913 274912826002554131226685)
                ·
                  refine ⟨103092309750957799210007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 274912826002554131226685 103092309750957799210007)
                  ·
                    rfl

theorem cell20_225868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_225868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225868 prefixEnd_225868 := by exact prefixLift 225868
  have htrace : WordTrace (prefixWord ++ tailWord_225868) baseStart_225868 baseEnd_225868 := by
    simpa [prefixWord, tailWord_225868, baseEnd_225868] using wordTrace_append hprefix tailTrace_225868
  have hstable : (prefixWord ++ tailWord_225868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225868).length < 2 ^ (prefixWord ++ tailWord_225868).sum := by decide
  have hdescent : baseEnd_225868 < baseStart_225868 := by decide
  rcases family_descends (prefixWord ++ tailWord_225868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225903 : List Nat := [1, 1, 2, 1, 3, 2, 2, 8]
def baseStart_225903 : Nat := 118140960795 + 225903 * 2 ^ 59
def prefixEnd_225903 : Nat := 4983230072969 + 3 ^ 40 * 225903 * 2
def baseEnd_225903 : Nat := 34369428234884411014399

theorem tailTrace_225903 : CollatzResearch.WordTrace tailWord_225903 prefixEnd_225903 34369428234884411014399 := by
  unfold tailWord_225903
  simp only [CollatzResearch.WordTrace]
  refine ⟨8239359300599487005906363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5492906200399658003937575 8239359300599487005906363)
  ·
    refine ⟨12359038950899230508859545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8239359300599487005906363 12359038950899230508859545)
    ·
      refine ⟨9269279213174422881644659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12359038950899230508859545 9269279213174422881644659)
      ·
        refine ⟨13903918819761634322466989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9269279213174422881644659 13903918819761634322466989)
        ·
          refine ⟨5213969557410612870925121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13903918819761634322466989 5213969557410612870925121)
          ·
            refine ⟨3910477168057959653193841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5213969557410612870925121 3910477168057959653193841)
            ·
              refine ⟨2932857876043469739895381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3910477168057959653193841 2932857876043469739895381)
              ·
                refine ⟨34369428234884411014399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2932857876043469739895381 34369428234884411014399)
                ·
                  rfl

theorem cell20_225903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 8].length) (baseStart_225903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225903 prefixEnd_225903 := by exact prefixLift 225903
  have htrace : WordTrace (prefixWord ++ tailWord_225903) baseStart_225903 baseEnd_225903 := by
    simpa [prefixWord, tailWord_225903, baseEnd_225903] using wordTrace_append hprefix tailTrace_225903
  have hstable : (prefixWord ++ tailWord_225903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225903).length < 2 ^ (prefixWord ++ tailWord_225903).sum := by decide
  have hdescent : baseEnd_225903 < baseStart_225903 := by decide
  rcases family_descends (prefixWord ++ tailWord_225903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_225927 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 5]
def baseStart_225927 : Nat := 118140960795 + 225927 * 2 ^ 59
def prefixEnd_225927 : Nat := 4983230072969 + 3 ^ 40 * 225927 * 2
def baseEnd_225927 : Nat := 103119238958615816243099

theorem tailTrace_225927 : CollatzResearch.WordTrace tailWord_225927 prefixEnd_225927 103119238958615816243099 := by
  unfold tailWord_225927
  simp only [CollatzResearch.WordTrace]
  refine ⟨8240234652512539104780035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5493489768341692736520023 8240234652512539104780035)
  ·
    refine ⟨12360351978768808657170053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8240234652512539104780035 12360351978768808657170053)
    ·
      refine ⟨2317565996019151623219385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12360351978768808657170053 2317565996019151623219385)
      ·
        refine ⟨1738174497014363717414539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2317565996019151623219385 1738174497014363717414539)
        ·
          refine ⟨2607261745521545576121809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1738174497014363717414539 2607261745521545576121809)
          ·
            refine ⟨1955446309141159182091357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2607261745521545576121809 1955446309141159182091357)
            ·
              refine ⟨733292365927934693284259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1955446309141159182091357 733292365927934693284259)
              ·
                refine ⟨1099938548891902039926389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 733292365927934693284259 1099938548891902039926389)
                ·
                  refine ⟨103119238958615816243099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1099938548891902039926389 103119238958615816243099)
                  ·
                    rfl

theorem cell20_225927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 5].length) (baseStart_225927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_225927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_225927 prefixEnd_225927 := by exact prefixLift 225927
  have htrace : WordTrace (prefixWord ++ tailWord_225927) baseStart_225927 baseEnd_225927 := by
    simpa [prefixWord, tailWord_225927, baseEnd_225927] using wordTrace_append hprefix tailTrace_225927
  have hstable : (prefixWord ++ tailWord_225927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_225927).length < 2 ^ (prefixWord ++ tailWord_225927).sum := by decide
  have hdescent : baseEnd_225927 < baseStart_225927 := by decide
  rcases family_descends (prefixWord ++ tailWord_225927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
