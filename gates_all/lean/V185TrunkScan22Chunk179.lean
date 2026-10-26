import V185TrunkScan22Chunk178

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1597287 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 1, 8]
def baseStart_1597287 : Nat := 118140960795 + 1597287 * 2 ^ 59
def prefixEnd_1597287 : Nat := 4983230072969 + 3 ^ 40 * 1597287 * 2
def baseEnd_1597287 : Nat := 546783982785464893977811

theorem tailTrace_1597287 : CollatzResearch.WordTrace tailWord_1597287 prefixEnd_1597287 546783982785464893977811 := by
  unfold tailWord_1597287
  simp only [CollatzResearch.WordTrace]
  refine ⟨58257842964309468746398115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38838561976206312497598743 58257842964309468746398115)
  ·
    refine ⟨87386764446464203119597173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58257842964309468746398115 87386764446464203119597173)
    ·
      refine ⟨8192509166856019042462235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87386764446464203119597173 8192509166856019042462235)
      ·
        refine ⟨12288763750284028563693353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8192509166856019042462235 12288763750284028563693353)
        ·
          refine ⟨9216572812713021422770015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12288763750284028563693353 9216572812713021422770015)
          ·
            refine ⟨13824859219069532134155023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9216572812713021422770015 13824859219069532134155023)
            ·
              refine ⟨20737288828604298201232535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13824859219069532134155023 20737288828604298201232535)
              ·
                refine ⟨31105933242906447301848803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20737288828604298201232535 31105933242906447301848803)
                ·
                  refine ⟨46658899864359670952773205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31105933242906447301848803 46658899864359670952773205)
                  ·
                    refine ⟨546783982785464893977811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46658899864359670952773205 546783982785464893977811)
                    ·
                      rfl

theorem cell22_1597287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_1597287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597287 prefixEnd_1597287 := by exact prefixLift 1597287
  have htrace : WordTrace (prefixWord ++ tailWord_1597287) baseStart_1597287 baseEnd_1597287 := by
    simpa [prefixWord, tailWord_1597287, baseEnd_1597287] using wordTrace_append hprefix tailTrace_1597287
  have hstable : (prefixWord ++ tailWord_1597287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597287).length < 2 ^ (prefixWord ++ tailWord_1597287).sum := by decide
  have hdescent : baseEnd_1597287 < baseStart_1597287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597317 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 1, 7]
def baseStart_1597317 : Nat := 118140960795 + 1597317 * 2 ^ 59
def prefixEnd_1597317 : Nat := 4983230072969 + 3 ^ 40 * 1597317 * 2
def baseEnd_1597317 : Nat := 546794252398554815727719

theorem tailTrace_1597317 : CollatzResearch.WordTrace tailWord_1597317 prefixEnd_1597317 546794252398554815727719 := by
  unfold tailWord_1597317
  simp only [CollatzResearch.WordTrace]
  refine ⟨58258937154200783869990205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38839291436133855913326803 58258937154200783869990205)
  ·
    refine ⟨21847101432825293951246327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58258937154200783869990205 21847101432825293951246327)
    ·
      refine ⟨32770652149237940926869491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21847101432825293951246327 32770652149237940926869491)
      ·
        refine ⟨49155978223856911390304237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32770652149237940926869491 49155978223856911390304237)
        ·
          refine ⟨18433491833946341771364089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49155978223856911390304237 18433491833946341771364089)
          ·
            refine ⟨13825118875459756328523067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18433491833946341771364089 13825118875459756328523067)
            ·
              refine ⟨20737678313189634492784601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13825118875459756328523067 20737678313189634492784601)
              ·
                refine ⟨15553258734892225869588451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20737678313189634492784601 15553258734892225869588451)
                ·
                  refine ⟨23329888102338338804382677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15553258734892225869588451 23329888102338338804382677)
                  ·
                    refine ⟨546794252398554815727719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23329888102338338804382677 546794252398554815727719)
                    ·
                      rfl

theorem cell22_1597317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_1597317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597317 prefixEnd_1597317 := by exact prefixLift 1597317
  have htrace : WordTrace (prefixWord ++ tailWord_1597317) baseStart_1597317 baseEnd_1597317 := by
    simpa [prefixWord, tailWord_1597317, baseEnd_1597317] using wordTrace_append hprefix tailTrace_1597317
  have hstable : (prefixWord ++ tailWord_1597317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597317).length < 2 ^ (prefixWord ++ tailWord_1597317).sum := by decide
  have hdescent : baseEnd_1597317 < baseStart_1597317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597336 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 7]
def baseStart_1597336 : Nat := 118140960795 + 1597336 * 2 ^ 59
def prefixEnd_1597336 : Nat := 4983230072969 + 3 ^ 40 * 1597336 * 2
def baseEnd_1597336 : Nat := 182266918828948366500887

theorem tailTrace_1597336 : CollatzResearch.WordTrace tailWord_1597336 prefixEnd_1597336 182266918828948366500887 := by
  unfold tailWord_1597336
  simp only [CollatzResearch.WordTrace]
  refine ⟨29129815070565975057465931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38839753427421300076621241 29129815070565975057465931)
  ·
    refine ⟨43694722605848962586198897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29129815070565975057465931 43694722605848962586198897)
    ·
      refine ⟨32771041954386721939649173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43694722605848962586198897 32771041954386721939649173)
      ·
        refine ⟨1536142591611877590921055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 32771041954386721939649173 1536142591611877590921055)
        ·
          refine ⟨2304213887417816386381583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1536142591611877590921055 2304213887417816386381583)
          ·
            refine ⟨3456320831126724579572375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2304213887417816386381583 3456320831126724579572375)
            ·
              refine ⟨5184481246690086869358563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3456320831126724579572375 5184481246690086869358563)
              ·
                refine ⟨7776721870035130304037845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5184481246690086869358563 7776721870035130304037845)
                ·
                  refine ⟨182266918828948366500887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7776721870035130304037845 182266918828948366500887)
                  ·
                    rfl

theorem cell22_1597336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 7].length) (baseStart_1597336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597336 prefixEnd_1597336 := by exact prefixLift 1597336
  have htrace : WordTrace (prefixWord ++ tailWord_1597336) baseStart_1597336 baseEnd_1597336 := by
    simpa [prefixWord, tailWord_1597336, baseEnd_1597336] using wordTrace_append hprefix tailTrace_1597336
  have hstable : (prefixWord ++ tailWord_1597336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597336).length < 2 ^ (prefixWord ++ tailWord_1597336).sum := by decide
  have hdescent : baseEnd_1597336 < baseStart_1597336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597392 : List Nat := [2, 1, 1, 1, 1, 2, 14]
def baseStart_1597392 : Nat := 118140960795 + 1597392 * 2 ^ 59
def prefixEnd_1597392 : Nat := 4983230072969 + 3 ^ 40 * 1597392 * 2
def baseEnd_1597392 : Nat := 20252589867825171114907

theorem tailTrace_1597392 : CollatzResearch.WordTrace tailWord_1597392 prefixEnd_1597392 20252589867825171114907 := by
  unfold tailWord_1597392
  simp only [CollatzResearch.WordTrace]
  refine ⟨29130836314464535839485215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38841115085952714452646953 29130836314464535839485215)
  ·
    refine ⟨43696254471696803759227823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29130836314464535839485215 43696254471696803759227823)
    ·
      refine ⟨65544381707545205638841735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43696254471696803759227823 65544381707545205638841735)
      ·
        refine ⟨98316572561317808458262603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65544381707545205638841735 98316572561317808458262603)
        ·
          refine ⟨147474858841976712687393905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98316572561317808458262603 147474858841976712687393905)
          ·
            refine ⟨110606144131482534515545429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147474858841976712687393905 110606144131482534515545429)
            ·
              refine ⟨20252589867825171114907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 110606144131482534515545429 20252589867825171114907)
              ·
                rfl

theorem cell22_1597392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 14].length) (baseStart_1597392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597392 prefixEnd_1597392 := by exact prefixLift 1597392
  have htrace : WordTrace (prefixWord ++ tailWord_1597392) baseStart_1597392 baseEnd_1597392 := by
    simpa [prefixWord, tailWord_1597392, baseEnd_1597392] using wordTrace_append hprefix tailTrace_1597392
  have hstable : (prefixWord ++ tailWord_1597392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597392).length < 2 ^ (prefixWord ++ tailWord_1597392).sum := by decide
  have hdescent : baseEnd_1597392 < baseStart_1597392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597396 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_1597396 : Nat := 118140960795 + 1597396 * 2 ^ 59
def prefixEnd_1597396 : Nat := 4983230072969 + 3 ^ 40 * 1597396 * 2
def baseEnd_1597396 : Nat := 546821295713024943002477

theorem tailTrace_1597396 : CollatzResearch.WordTrace tailWord_1597396 prefixEnd_1597396 546821295713024943002477 := by
  unfold tailWord_1597396
  simp only [CollatzResearch.WordTrace]
  refine ⟨29130909260457290181058021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38841212347276386908077361 29130909260457290181058021)
  ·
    refine ⟨5462045486335741908948379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29130909260457290181058021 5462045486335741908948379)
    ·
      refine ⟨8193068229503612863422569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5462045486335741908948379 8193068229503612863422569)
      ·
        refine ⟨6144801172127709647566927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8193068229503612863422569 6144801172127709647566927)
        ·
          refine ⟨9217201758191564471350391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6144801172127709647566927 9217201758191564471350391)
          ·
            refine ⟨13825802637287346707025587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9217201758191564471350391 13825802637287346707025587)
            ·
              refine ⟨20738703955931020060538381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13825802637287346707025587 20738703955931020060538381)
              ·
                refine ⟨7777013983474132522701893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20738703955931020060538381 7777013983474132522701893)
                ·
                  refine ⟨1458190121901399848006605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7777013983474132522701893 1458190121901399848006605)
                  ·
                    refine ⟨546821295713024943002477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1458190121901399848006605 546821295713024943002477)
                    ·
                      rfl

theorem cell22_1597396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_1597396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597396 prefixEnd_1597396 := by exact prefixLift 1597396
  have htrace : WordTrace (prefixWord ++ tailWord_1597396) baseStart_1597396 baseEnd_1597396 := by
    simpa [prefixWord, tailWord_1597396, baseEnd_1597396] using wordTrace_append hprefix tailTrace_1597396
  have hstable : (prefixWord ++ tailWord_1597396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597396).length < 2 ^ (prefixWord ++ tailWord_1597396).sum := by decide
  have hdescent : baseEnd_1597396 < baseStart_1597396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597404 : List Nat := [2, 2, 6, 1, 2, 1, 2, 1, 5]
def baseStart_1597404 : Nat := 118140960795 + 1597404 * 2 ^ 59
def prefixEnd_1597404 : Nat := 4983230072969 + 3 ^ 40 * 1597404 * 2
def baseEnd_1597404 : Nat := 182274678092171862934151

theorem tailTrace_1597404 : CollatzResearch.WordTrace tailWord_1597404 prefixEnd_1597404 182274678092171862934151 := by
  unfold tailWord_1597404
  simp only [CollatzResearch.WordTrace]
  refine ⟨29131055152442798864203633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38841406869923731818938177 29131055152442798864203633)
  ·
    refine ⟨21848291364332099148152725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29131055152442798864203633 21848291364332099148152725)
    ·
      refine ⟨1024138657703067147569659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21848291364332099148152725 1024138657703067147569659)
      ·
        refine ⟨1536207986554600721354489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1024138657703067147569659 1536207986554600721354489)
        ·
          refine ⟨1152155989915950541015867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1536207986554600721354489 1152155989915950541015867)
          ·
            refine ⟨1728233984873925811523801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1152155989915950541015867 1728233984873925811523801)
            ·
              refine ⟨1296175488655444358642851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1728233984873925811523801 1296175488655444358642851)
              ·
                refine ⟨1944263232983166537964277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1296175488655444358642851 1944263232983166537964277)
                ·
                  refine ⟨182274678092171862934151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1944263232983166537964277 182274678092171862934151)
                  ·
                    rfl

theorem cell22_1597404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_1597404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597404 prefixEnd_1597404 := by exact prefixLift 1597404
  have htrace : WordTrace (prefixWord ++ tailWord_1597404) baseStart_1597404 baseEnd_1597404 := by
    simpa [prefixWord, tailWord_1597404, baseEnd_1597404] using wordTrace_append hprefix tailTrace_1597404
  have hstable : (prefixWord ++ tailWord_1597404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597404).length < 2 ^ (prefixWord ++ tailWord_1597404).sum := by decide
  have hdescent : baseEnd_1597404 < baseStart_1597404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597460 : List Nat := [2, 4, 3, 2, 1, 2, 1, 7]
def baseStart_1597460 : Nat := 118140960795 + 1597460 * 2 ^ 59
def prefixEnd_1597460 : Nat := 4983230072969 + 3 ^ 40 * 1597460 * 2
def baseEnd_1597460 : Nat := 60760356024550012155809

theorem tailTrace_1597460 : CollatzResearch.WordTrace tailWord_1597460 prefixEnd_1597460 60760356024550012155809 := by
  unfold tailWord_1597460
  simp only [CollatzResearch.WordTrace]
  refine ⟨29132076396341359646222917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38842768528455146194963889 29132076396341359646222917)
  ·
    refine ⟨5462264324314004933666797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29132076396341359646222917 5462264324314004933666797)
    ·
      refine ⟨2048349121617751850125049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5462264324314004933666797 2048349121617751850125049)
      ·
        refine ⟨1536261841213313887593787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2048349121617751850125049 1536261841213313887593787)
        ·
          refine ⟨2304392761819970831390681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1536261841213313887593787 2304392761819970831390681)
          ·
            refine ⟨1728294571364978123543011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2304392761819970831390681 1728294571364978123543011)
            ·
              refine ⟨2592441857047467185314517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1728294571364978123543011 2592441857047467185314517)
              ·
                refine ⟨60760356024550012155809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2592441857047467185314517 60760356024550012155809)
                ·
                  rfl

theorem cell22_1597460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 7].length) (baseStart_1597460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597460 prefixEnd_1597460 := by exact prefixLift 1597460
  have htrace : WordTrace (prefixWord ++ tailWord_1597460) baseStart_1597460 baseEnd_1597460 := by
    simpa [prefixWord, tailWord_1597460, baseEnd_1597460] using wordTrace_append hprefix tailTrace_1597460
  have hstable : (prefixWord ++ tailWord_1597460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597460).length < 2 ^ (prefixWord ++ tailWord_1597460).sum := by decide
  have hdescent : baseEnd_1597460 < baseStart_1597460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597529 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 3, 6]
def baseStart_1597529 : Nat := 118140960795 + 1597529 * 2 ^ 59
def prefixEnd_1597529 : Nat := 4983230072969 + 3 ^ 40 * 1597529 * 2
def baseEnd_1597529 : Nat := 546866824331056929427069

theorem tailTrace_1597529 : CollatzResearch.WordTrace tailWord_1597529 prefixEnd_1597529 546866824331056929427069 := by
  unfold tailWord_1597529
  simp only [CollatzResearch.WordTrace]
  refine ⟨58266669429432744076707641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38844446286288496051138427 58266669429432744076707641)
  ·
    refine ⟨43700002072074558057530731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58266669429432744076707641 43700002072074558057530731)
    ·
      refine ⟨65550003108111837086296097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43700002072074558057530731 65550003108111837086296097)
      ·
        refine ⟨49162502331083877814722073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65550003108111837086296097 49162502331083877814722073)
        ·
          refine ⟨36871876748312908361041555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49162502331083877814722073 36871876748312908361041555)
          ·
            refine ⟨55307815122469362541562333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36871876748312908361041555 55307815122469362541562333)
            ·
              refine ⟨20740430670926010953085875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55307815122469362541562333 20740430670926010953085875)
              ·
                refine ⟨31110646006389016429628813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20740430670926010953085875 31110646006389016429628813)
                ·
                  refine ⟨11666492252395881161110805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31110646006389016429628813 11666492252395881161110805)
                  ·
                    refine ⟨546866824331056929427069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11666492252395881161110805 546866824331056929427069)
                    ·
                      rfl

theorem cell22_1597529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_1597529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597529 prefixEnd_1597529 := by exact prefixLift 1597529
  have htrace : WordTrace (prefixWord ++ tailWord_1597529) baseStart_1597529 baseEnd_1597529 := by
    simpa [prefixWord, tailWord_1597529, baseEnd_1597529] using wordTrace_append hprefix tailTrace_1597529
  have hstable : (prefixWord ++ tailWord_1597529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597529).length < 2 ^ (prefixWord ++ tailWord_1597529).sum := by decide
  have hdescent : baseEnd_1597529 < baseStart_1597529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597533 : List Nat := [1, 4, 4, 1, 1, 1, 2, 2, 6]
def baseStart_1597533 : Nat := 118140960795 + 1597533 * 2 ^ 59
def prefixEnd_1597533 : Nat := 4983230072969 + 3 ^ 40 * 1597533 * 2
def baseEnd_1597533 : Nat := 182289397870934084109019

theorem tailTrace_1597533 : CollatzResearch.WordTrace tailWord_1597533 prefixEnd_1597533 182289397870934084109019 := by
  unfold tailWord_1597533
  simp only [CollatzResearch.WordTrace]
  refine ⟨58266815321418252759853253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38844543547612168506568835 58266815321418252759853253)
  ·
    refine ⟨10925027872765922392472485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58266815321418252759853253 10925027872765922392472485)
    ·
      refine ⟨2048442726143610448588591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10925027872765922392472485 2048442726143610448588591)
      ·
        refine ⟨3072664089215415672882887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2048442726143610448588591 3072664089215415672882887)
        ·
          refine ⟨4608996133823123509324331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3072664089215415672882887 4608996133823123509324331)
          ·
            refine ⟨6913494200734685263986497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4608996133823123509324331 6913494200734685263986497)
            ·
              refine ⟨5185120650551013947989873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6913494200734685263986497 5185120650551013947989873)
              ·
                refine ⟨3888840487913260460992405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5185120650551013947989873 3888840487913260460992405)
                ·
                  refine ⟨182289397870934084109019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3888840487913260460992405 182289397870934084109019)
                  ·
                    rfl

theorem cell22_1597533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_1597533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597533 prefixEnd_1597533 := by exact prefixLift 1597533
  have htrace : WordTrace (prefixWord ++ tailWord_1597533) baseStart_1597533 baseEnd_1597533 := by
    simpa [prefixWord, tailWord_1597533, baseEnd_1597533] using wordTrace_append hprefix tailTrace_1597533
  have hstable : (prefixWord ++ tailWord_1597533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597533).length < 2 ^ (prefixWord ++ tailWord_1597533).sum := by decide
  have hdescent : baseEnd_1597533 < baseStart_1597533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597561 : List Nat := [1, 2, 1, 3, 4, 3, 8]
def baseStart_1597561 : Nat := 118140960795 + 1597561 * 2 ^ 59
def prefixEnd_1597561 : Nat := 4983230072969 + 3 ^ 40 * 1597561 * 2
def baseEnd_1597561 : Nat := 20254732540185907875073

theorem tailTrace_1597561 : CollatzResearch.WordTrace tailWord_1597561 prefixEnd_1597561 20254732540185907875073 := by
  unfold tailWord_1597561
  simp only [CollatzResearch.WordTrace]
  refine ⟨58267836565316813541872537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38845224376877875694581691 58267836565316813541872537)
  ·
    refine ⟨43700877423987610156404403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58267836565316813541872537 43700877423987610156404403)
    ·
      refine ⟨65551316135981415234606605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43700877423987610156404403 65551316135981415234606605)
      ·
        refine ⟨24581743550993030712977477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65551316135981415234606605 24581743550993030712977477)
        ·
          refine ⟨4609076915811193258683277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24581743550993030712977477 4609076915811193258683277)
          ·
            refine ⟨1728403843429197472006229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4609076915811193258683277 1728403843429197472006229)
            ·
              refine ⟨20254732540185907875073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1728403843429197472006229 20254732540185907875073)
              ·
                rfl

theorem cell22_1597561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 8].length) (baseStart_1597561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597561 prefixEnd_1597561 := by exact prefixLift 1597561
  have htrace : WordTrace (prefixWord ++ tailWord_1597561) baseStart_1597561 baseEnd_1597561 := by
    simpa [prefixWord, tailWord_1597561, baseEnd_1597561] using wordTrace_append hprefix tailTrace_1597561
  have hstable : (prefixWord ++ tailWord_1597561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597561).length < 2 ^ (prefixWord ++ tailWord_1597561).sum := by decide
  have hdescent : baseEnd_1597561 < baseStart_1597561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597623 : List Nat := [1, 1, 3, 1, 4, 3, 2, 2, 5]
def baseStart_1597623 : Nat := 118140960795 + 1597623 * 2 ^ 59
def prefixEnd_1597623 : Nat := 4983230072969 + 3 ^ 40 * 1597623 * 2
def baseEnd_1597623 : Nat := 182299667484024005858927

theorem tailTrace_1597623 : CollatzResearch.WordTrace tailWord_1597623 prefixEnd_1597623 182299667484024005858927 := by
  unfold tailWord_1597623
  simp only [CollatzResearch.WordTrace]
  refine ⟨58270097891092198130629523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38846731927394798753753015 58270097891092198130629523)
  ·
    refine ⟨87405146836638297195944285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58270097891092198130629523 87405146836638297195944285)
    ·
      refine ⟨32776930063739361448479107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87405146836638297195944285 32776930063739361448479107)
      ·
        refine ⟨49165395095609042172718661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32776930063739361448479107 49165395095609042172718661)
        ·
          refine ⟨9218511580426695407384749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49165395095609042172718661 9218511580426695407384749)
          ·
            refine ⟨3456941842660010777769281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9218511580426695407384749 3456941842660010777769281)
            ·
              refine ⟨2592706381995008083326961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3456941842660010777769281 2592706381995008083326961)
              ·
                refine ⟨1944529786496256062495221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2592706381995008083326961 1944529786496256062495221)
                ·
                  refine ⟨182299667484024005858927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1944529786496256062495221 182299667484024005858927)
                  ·
                    rfl

theorem cell22_1597623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 2, 5].length) (baseStart_1597623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597623 prefixEnd_1597623 := by exact prefixLift 1597623
  have htrace : WordTrace (prefixWord ++ tailWord_1597623) baseStart_1597623 baseEnd_1597623 := by
    simpa [prefixWord, tailWord_1597623, baseEnd_1597623] using wordTrace_append hprefix tailTrace_1597623
  have hstable : (prefixWord ++ tailWord_1597623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597623).length < 2 ^ (prefixWord ++ tailWord_1597623).sum := by decide
  have hdescent : baseEnd_1597623 < baseStart_1597623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597683 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 4, 3]
def baseStart_1597683 : Nat := 118140960795 + 1597683 * 2 ^ 59
def prefixEnd_1597683 : Nat := 4983230072969 + 3 ^ 40 * 1597683 * 2
def baseEnd_1597683 : Nat := 546919541678251861076597

theorem tailTrace_1597683 : CollatzResearch.WordTrace tailWord_1597683 prefixEnd_1597683 546919541678251861076597 := by
  unfold tailWord_1597683
  simp only [CollatzResearch.WordTrace]
  refine ⟨58272286270874828377813703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38848190847249885585209135 58272286270874828377813703)
  ·
    refine ⟨87408429406312242566720555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58272286270874828377813703 87408429406312242566720555)
    ·
      refine ⟨131112644109468363850080833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87408429406312242566720555 131112644109468363850080833)
      ·
        refine ⟨98334483082101272887560625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131112644109468363850080833 98334483082101272887560625)
        ·
          refine ⟨73750862311575954665670469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98334483082101272887560625 73750862311575954665670469)
          ·
            refine ⟨13828286683420491499813213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73750862311575954665670469 13828286683420491499813213)
            ·
              refine ⟨5185607506282684312429955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13828286683420491499813213 5185607506282684312429955)
              ·
                refine ⟨7778411259424026468644933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5185607506282684312429955 7778411259424026468644933)
                ·
                  refine ⟨1458452111142004962870925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7778411259424026468644933 1458452111142004962870925)
                  ·
                    refine ⟨546919541678251861076597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1458452111142004962870925 546919541678251861076597)
                    ·
                      rfl

theorem cell22_1597683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 3].length) (baseStart_1597683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597683 prefixEnd_1597683 := by exact prefixLift 1597683
  have htrace : WordTrace (prefixWord ++ tailWord_1597683) baseStart_1597683 baseEnd_1597683 := by
    simpa [prefixWord, tailWord_1597683, baseEnd_1597683] using wordTrace_append hprefix tailTrace_1597683
  have hstable : (prefixWord ++ tailWord_1597683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597683).length < 2 ^ (prefixWord ++ tailWord_1597683).sum := by decide
  have hdescent : baseEnd_1597683 < baseStart_1597683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597713 : List Nat := [1, 2, 2, 1, 1, 5, 4, 6]
def baseStart_1597713 : Nat := 118140960795 + 1597713 * 2 ^ 59
def prefixEnd_1597713 : Nat := 4983230072969 + 3 ^ 40 * 1597713 * 2
def baseEnd_1597713 : Nat := 60769979032371309202945

theorem tailTrace_1597713 : CollatzResearch.WordTrace tailWord_1597713 prefixEnd_1597713 60769979032371309202945 := by
  unfold tailWord_1597713
  simp only [CollatzResearch.WordTrace]
  refine ⟨58273380460766143501405793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38848920307177429000937195 58273380460766143501405793)
  ·
    refine ⟨43705035345574607626054345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58273380460766143501405793 43705035345574607626054345)
    ·
      refine ⟨32778776509180955719540759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43705035345574607626054345 32778776509180955719540759)
      ·
        refine ⟨49168164763771433579311139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32778776509180955719540759 49168164763771433579311139)
        ·
          refine ⟨73752247145657150368966709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49168164763771433579311139 73752247145657150368966709)
          ·
            refine ⟨6914273169905357847090629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73752247145657150368966709 6914273169905357847090629)
            ·
              refine ⟨1296426219357254596329493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6914273169905357847090629 1296426219357254596329493)
              ·
                refine ⟨60769979032371309202945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1296426219357254596329493 60769979032371309202945)
                ·
                  rfl

theorem cell22_1597713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 6].length) (baseStart_1597713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597713 prefixEnd_1597713 := by exact prefixLift 1597713
  have htrace : WordTrace (prefixWord ++ tailWord_1597713) baseStart_1597713 baseEnd_1597713 := by
    simpa [prefixWord, tailWord_1597713, baseEnd_1597713] using wordTrace_append hprefix tailTrace_1597713
  have hstable : (prefixWord ++ tailWord_1597713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597713).length < 2 ^ (prefixWord ++ tailWord_1597713).sum := by decide
  have hdescent : baseEnd_1597713 < baseStart_1597713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597854 : List Nat := [4, 3, 1, 2, 1, 1, 2, 4, 4]
def baseStart_1597854 : Nat := 118140960795 + 1597854 * 2 ^ 59
def prefixEnd_1597854 : Nat := 4983230072969 + 3 ^ 40 * 1597854 * 2
def baseEnd_1597854 : Nat := 182326026157621471683691

theorem tailTrace_1597854 : CollatzResearch.WordTrace tailWord_1597854 prefixEnd_1597854 182326026157621471683691 := by
  unfold tailWord_1597854
  simp only [CollatzResearch.WordTrace]
  refine ⟨7284815394156915572786077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38852348768836883054859077 7284815394156915572786077)
  ·
    refine ⟨2731805772808843339794779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7284815394156915572786077 2731805772808843339794779)
    ·
      refine ⟨4097708659213265009692169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2731805772808843339794779 4097708659213265009692169)
      ·
        refine ⟨3073281494409948757269127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4097708659213265009692169 3073281494409948757269127)
        ·
          refine ⟨4609922241614923135903691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3073281494409948757269127 4609922241614923135903691)
          ·
            refine ⟨6914883362422384703855537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4609922241614923135903691 6914883362422384703855537)
            ·
              refine ⟨5186162521816788527891653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6914883362422384703855537 5186162521816788527891653)
              ·
                refine ⟨972405472840647848979685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5186162521816788527891653 972405472840647848979685)
                ·
                  refine ⟨182326026157621471683691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 972405472840647848979685 182326026157621471683691)
                  ·
                    rfl

theorem cell22_1597854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_1597854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597854 prefixEnd_1597854 := by exact prefixLift 1597854
  have htrace : WordTrace (prefixWord ++ tailWord_1597854) baseStart_1597854 baseEnd_1597854 := by
    simpa [prefixWord, tailWord_1597854, baseEnd_1597854] using wordTrace_append hprefix tailTrace_1597854
  have hstable : (prefixWord ++ tailWord_1597854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597854).length < 2 ^ (prefixWord ++ tailWord_1597854).sum := by decide
  have hdescent : baseEnd_1597854 < baseStart_1597854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597869 : List Nat := [1, 5, 2, 2, 2, 2, 1, 1, 1, 5]
def baseStart_1597869 : Nat := 118140960795 + 1597869 * 2 ^ 59
def prefixEnd_1597869 : Nat := 4983230072969 + 3 ^ 40 * 1597869 * 2
def baseEnd_1597869 : Nat := 546983213279409375926027

theorem tailTrace_1597869 : CollatzResearch.WordTrace tailWord_1597869 prefixEnd_1597869 546983213279409375926027 := by
  unfold tailWord_1597869
  simp only [CollatzResearch.WordTrace]
  refine ⟨58279070248200982144084661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38852713498800654762723107 58279070248200982144084661)
  ·
    refine ⟨5463662835768842076007937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58279070248200982144084661 5463662835768842076007937)
    ·
      refine ⟨4097747126826631557005953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5463662835768842076007937 4097747126826631557005953)
      ·
        refine ⟨3073310345119973667754465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4097747126826631557005953 3073310345119973667754465)
        ·
          refine ⟨2304982758839980250815849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3073310345119973667754465 2304982758839980250815849)
          ·
            refine ⟨1728737069129985188111887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2304982758839980250815849 1728737069129985188111887)
            ·
              refine ⟨2593105603694977782167831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1728737069129985188111887 2593105603694977782167831)
              ·
                refine ⟨3889658405542466673251747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2593105603694977782167831 3889658405542466673251747)
                ·
                  refine ⟨5834487608313700009877621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3889658405542466673251747 5834487608313700009877621)
                  ·
                    refine ⟨546983213279409375926027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5834487608313700009877621 546983213279409375926027)
                    ·
                      rfl

theorem cell22_1597869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_1597869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597869 prefixEnd_1597869 := by exact prefixLift 1597869
  have htrace : WordTrace (prefixWord ++ tailWord_1597869) baseStart_1597869 baseEnd_1597869 := by
    simpa [prefixWord, tailWord_1597869, baseEnd_1597869] using wordTrace_append hprefix tailTrace_1597869
  have hstable : (prefixWord ++ tailWord_1597869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597869).length < 2 ^ (prefixWord ++ tailWord_1597869).sum := by decide
  have hdescent : baseEnd_1597869 < baseStart_1597869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597965 : List Nat := [1, 7, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_1597965 : Nat := 118140960795 + 1597965 * 2 ^ 59
def prefixEnd_1597965 : Nat := 4983230072969 + 3 ^ 40 * 1597965 * 2
def baseEnd_1597965 : Nat := 547016076041297125525733

theorem tailTrace_1597965 : CollatzResearch.WordTrace tailWord_1597965 prefixEnd_1597965 547016076041297125525733 := by
  unfold tailWord_1597965
  simp only [CollatzResearch.WordTrace]
  refine ⟨58282571655853190539579349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38855047770568793693052899 58282571655853190539579349)
  ·
    refine ⟨1365997773184059153271391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 58282571655853190539579349 1365997773184059153271391)
    ·
      refine ⟨2048996659776088729907087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1365997773184059153271391 2048996659776088729907087)
      ·
        refine ⟨3073494989664133094860631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2048996659776088729907087 3073494989664133094860631)
        ·
          refine ⟨4610242484496199642290947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3073494989664133094860631 4610242484496199642290947)
          ·
            refine ⟨6915363726744299463436421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4610242484496199642290947 6915363726744299463436421)
            ·
              refine ⟨1296630698764556149394329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6915363726744299463436421 1296630698764556149394329)
              ·
                refine ⟨972473024073417112045747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1296630698764556149394329 972473024073417112045747)
                ·
                  refine ⟨1458709536110125668068621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 972473024073417112045747 1458709536110125668068621)
                  ·
                    refine ⟨547016076041297125525733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1458709536110125668068621 547016076041297125525733)
                    ·
                      rfl

theorem cell22_1597965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_1597965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597965 prefixEnd_1597965 := by exact prefixLift 1597965
  have htrace : WordTrace (prefixWord ++ tailWord_1597965) baseStart_1597965 baseEnd_1597965 := by
    simpa [prefixWord, tailWord_1597965, baseEnd_1597965] using wordTrace_append hprefix tailTrace_1597965
  have hstable : (prefixWord ++ tailWord_1597965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597965).length < 2 ^ (prefixWord ++ tailWord_1597965).sum := by decide
  have hdescent : baseEnd_1597965 < baseStart_1597965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597985 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 1, 6]
def baseStart_1597985 : Nat := 118140960795 + 1597985 * 2 ^ 59
def prefixEnd_1597985 : Nat := 4983230072969 + 3 ^ 40 * 1597985 * 2
def baseEnd_1597985 : Nat := 547022922450023740025671

theorem tailTrace_1597985 : CollatzResearch.WordTrace tailWord_1597985 prefixEnd_1597985 547022922450023740025671 := by
  unfold tailWord_1597985
  simp only [CollatzResearch.WordTrace]
  refine ⟨58283301115780733955307409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38855534077187155970204939 58283301115780733955307409)
  ·
    refine ⟨43712475836835550466480557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58283301115780733955307409 43712475836835550466480557)
    ·
      refine ⟨16392178438813331424930209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43712475836835550466480557 16392178438813331424930209)
      ·
        refine ⟨12294133829109998568697657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16392178438813331424930209 12294133829109998568697657)
        ·
          refine ⟨9220600371832498926523243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12294133829109998568697657 9220600371832498926523243)
          ·
            refine ⟨13830900557748748389784865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9220600371832498926523243 13830900557748748389784865)
            ·
              refine ⟨10373175418311561292338649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13830900557748748389784865 10373175418311561292338649)
              ·
                refine ⟨7779881563733670969253987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10373175418311561292338649 7779881563733670969253987)
                ·
                  refine ⟨11669822345600506453880981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7779881563733670969253987 11669822345600506453880981)
                  ·
                    refine ⟨547022922450023740025671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11669822345600506453880981 547022922450023740025671)
                    ·
                      rfl

theorem cell22_1597985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_1597985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597985 prefixEnd_1597985 := by exact prefixLift 1597985
  have htrace : WordTrace (prefixWord ++ tailWord_1597985) baseStart_1597985 baseEnd_1597985 := by
    simpa [prefixWord, tailWord_1597985, baseEnd_1597985] using wordTrace_append hprefix tailTrace_1597985
  have hstable : (prefixWord ++ tailWord_1597985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597985).length < 2 ^ (prefixWord ++ tailWord_1597985).sum := by decide
  have hdescent : baseEnd_1597985 < baseStart_1597985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1597987 : List Nat := [1, 1, 1, 4, 4, 2, 2, 1, 1, 5]
def baseStart_1597987 : Nat := 118140960795 + 1597987 * 2 ^ 59
def prefixEnd_1597987 : Nat := 4983230072969 + 3 ^ 40 * 1597987 * 2
def baseEnd_1597987 : Nat := 547023607090896401475665

theorem tailTrace_1597987 : CollatzResearch.WordTrace tailWord_1597987 prefixEnd_1597987 547023607090896401475665 := by
  unfold tailWord_1597987
  simp only [CollatzResearch.WordTrace]
  refine ⟨58283374061773488296880215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38855582707848992197920143 58283374061773488296880215)
  ·
    refine ⟨87425061092660232445320323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58283374061773488296880215 87425061092660232445320323)
    ·
      refine ⟨131137591638990348667980485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87425061092660232445320323 131137591638990348667980485)
      ·
        refine ⟨24588298432310690375246341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131137591638990348667980485 24588298432310690375246341)
        ·
          refine ⟨4610305956058254445358689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24588298432310690375246341 4610305956058254445358689)
          ·
            refine ⟨3457729467043690834019017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4610305956058254445358689 3457729467043690834019017)
            ·
              refine ⟨2593297100282768125514263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3457729467043690834019017 2593297100282768125514263)
              ·
                refine ⟨3889945650424152188271395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2593297100282768125514263 3889945650424152188271395)
                ·
                  refine ⟨5834918475636228282407093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3889945650424152188271395 5834918475636228282407093)
                  ·
                    refine ⟨547023607090896401475665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5834918475636228282407093 547023607090896401475665)
                    ·
                      rfl

theorem cell22_1597987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 5].length) (baseStart_1597987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1597987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1597987 prefixEnd_1597987 := by exact prefixLift 1597987
  have htrace : WordTrace (prefixWord ++ tailWord_1597987) baseStart_1597987 baseEnd_1597987 := by
    simpa [prefixWord, tailWord_1597987, baseEnd_1597987] using wordTrace_append hprefix tailTrace_1597987
  have hstable : (prefixWord ++ tailWord_1597987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1597987).length < 2 ^ (prefixWord ++ tailWord_1597987).sum := by decide
  have hdescent : baseEnd_1597987 < baseStart_1597987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1597987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598002 : List Nat := [3, 2, 1, 1, 2, 1, 5, 1, 2, 4]
def baseStart_1598002 : Nat := 118140960795 + 1598002 * 2 ^ 59
def prefixEnd_1598002 : Nat := 4983230072969 + 3 ^ 40 * 1598002 * 2
def baseEnd_1598002 : Nat := 547028741897441362350619

theorem tailTrace_1598002 : CollatzResearch.WordTrace tailWord_1598002 prefixEnd_1598002 547028741897441362350619 := by
  unfold tailWord_1598002
  simp only [CollatzResearch.WordTrace]
  refine ⟨14570980289179786464669065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38855947437812763905784173 14570980289179786464669065)
  ·
    refine ⟨10928235216884839848501799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14570980289179786464669065 10928235216884839848501799)
    ·
      refine ⟨16392352825327259772752699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10928235216884839848501799 16392352825327259772752699)
      ·
        refine ⟨24588529237990889659129049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16392352825327259772752699 24588529237990889659129049)
        ·
          refine ⟨18441396928493167244346787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24588529237990889659129049 18441396928493167244346787)
          ·
            refine ⟨27662095392739750866520181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18441396928493167244346787 27662095392739750866520181)
            ·
              refine ⟨2593321443069351643736267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27662095392739750866520181 2593321443069351643736267)
              ·
                refine ⟨3889982164604027465604401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2593321443069351643736267 3889982164604027465604401)
                ·
                  refine ⟨2917486623453020599203301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3889982164604027465604401 2917486623453020599203301)
                  ·
                    refine ⟨547028741897441362350619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2917486623453020599203301 547028741897441362350619)
                    ·
                      rfl

theorem cell22_1598002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_1598002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598002 prefixEnd_1598002 := by exact prefixLift 1598002
  have htrace : WordTrace (prefixWord ++ tailWord_1598002) baseStart_1598002 baseEnd_1598002 := by
    simpa [prefixWord, tailWord_1598002, baseEnd_1598002] using wordTrace_append hprefix tailTrace_1598002
  have hstable : (prefixWord ++ tailWord_1598002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598002).length < 2 ^ (prefixWord ++ tailWord_1598002).sum := by decide
  have hdescent : baseEnd_1598002 < baseStart_1598002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598006 : List Nat := [5, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_1598006 : Nat := 118140960795 + 1598006 * 2 ^ 59
def prefixEnd_1598006 : Nat := 4983230072969 + 3 ^ 40 * 1598006 * 2
def baseEnd_1598006 : Nat := 182343370393062228416869

theorem tailTrace_1598006 : CollatzResearch.WordTrace tailWord_1598006 prefixEnd_1598006 182343370393062228416869 := by
  unfold tailWord_1598006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3642754190544040908863867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38856044699136436361214581 3642754190544040908863867)
  ·
    refine ⟨5464131285816061363295801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3642754190544040908863867 5464131285816061363295801)
    ·
      refine ⟨4098098464362046022471851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5464131285816061363295801 4098098464362046022471851)
      ·
        refine ⟨6147147696543069033707777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4098098464362046022471851 6147147696543069033707777)
        ·
          refine ⟨4610360772407301775280833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6147147696543069033707777 4610360772407301775280833)
          ·
            refine ⟨3457770579305476331460625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4610360772407301775280833 3457770579305476331460625)
            ·
              refine ⟨2593327934479107248595469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3457770579305476331460625 2593327934479107248595469)
              ·
                refine ⟨972497975429665218223301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2593327934479107248595469 972497975429665218223301)
                ·
                  refine ⟨182343370393062228416869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 972497975429665218223301 182343370393062228416869)
                  ·
                    rfl

theorem cell22_1598006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_1598006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598006 prefixEnd_1598006 := by exact prefixLift 1598006
  have htrace : WordTrace (prefixWord ++ tailWord_1598006) baseStart_1598006 baseEnd_1598006 := by
    simpa [prefixWord, tailWord_1598006, baseEnd_1598006] using wordTrace_append hprefix tailTrace_1598006
  have hstable : (prefixWord ++ tailWord_1598006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598006).length < 2 ^ (prefixWord ++ tailWord_1598006).sum := by decide
  have hdescent : baseEnd_1598006 < baseStart_1598006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598030 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 1, 8]
def baseStart_1598030 : Nat := 118140960795 + 1598030 * 2 ^ 59
def prefixEnd_1598030 : Nat := 4983230072969 + 3 ^ 40 * 1598030 * 2
def baseEnd_1598030 : Nat := 547038326869658622650533

theorem tailTrace_1598030 : CollatzResearch.WordTrace tailWord_1598030 prefixEnd_1598030 547038326869658622650533 := by
  unfold tailWord_1598030
  simp only [CollatzResearch.WordTrace]
  refine ⟨7285617800077213330086943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38856628267078471093797029 7285617800077213330086943)
  ·
    refine ⟨10928426700115819995130415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7285617800077213330086943 10928426700115819995130415)
    ·
      refine ⟨16392640050173729992695623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10928426700115819995130415 16392640050173729992695623)
      ·
        refine ⟨24588960075260594989043435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16392640050173729992695623 24588960075260594989043435)
        ·
          refine ⟨36883440112890892483565153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24588960075260594989043435 36883440112890892483565153)
          ·
            refine ⟨27662580084668169362673865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36883440112890892483565153 27662580084668169362673865)
            ·
              refine ⟨20746935063501127022005399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27662580084668169362673865 20746935063501127022005399)
              ·
                refine ⟨31120402595251690533008099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20746935063501127022005399 31120402595251690533008099)
                ·
                  refine ⟨46680603892877535799512149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31120402595251690533008099 46680603892877535799512149)
                  ·
                    refine ⟨547038326869658622650533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46680603892877535799512149 547038326869658622650533)
                    ·
                      rfl

theorem cell22_1598030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_1598030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598030 prefixEnd_1598030 := by exact prefixLift 1598030
  have htrace : WordTrace (prefixWord ++ tailWord_1598030) baseStart_1598030 baseEnd_1598030 := by
    simpa [prefixWord, tailWord_1598030, baseEnd_1598030] using wordTrace_append hprefix tailTrace_1598030
  have hstable : (prefixWord ++ tailWord_1598030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598030).length < 2 ^ (prefixWord ++ tailWord_1598030).sum := by decide
  have hdescent : baseEnd_1598030 < baseStart_1598030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598060 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 1, 7]
def baseStart_1598060 : Nat := 118140960795 + 1598060 * 2 ^ 59
def prefixEnd_1598060 : Nat := 4983230072969 + 3 ^ 40 * 1598060 * 2
def baseEnd_1598060 : Nat := 547048596482748544400441

theorem tailTrace_1598060 : CollatzResearch.WordTrace tailWord_1598060 prefixEnd_1598060 547048596482748544400441 := by
  unfold tailWord_1598060
  simp only [CollatzResearch.WordTrace]
  refine ⟨29143018295254510882143817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38857357727006014509525089 29143018295254510882143817)
  ·
    refine ⟨21857263721440883161607863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29143018295254510882143817 21857263721440883161607863)
    ·
      refine ⟨32785895582161324742411795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21857263721440883161607863 32785895582161324742411795)
      ·
        refine ⟨49178843373241987113617693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32785895582161324742411795 49178843373241987113617693)
        ·
          refine ⟨18442066264965745167606635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49178843373241987113617693 18442066264965745167606635)
          ·
            refine ⟨27663099397448617751409953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18442066264965745167606635 27663099397448617751409953)
            ·
              refine ⟨20747324548086463313557465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27663099397448617751409953 20747324548086463313557465)
              ·
                refine ⟨15560493411064847485168099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20747324548086463313557465 15560493411064847485168099)
                ·
                  refine ⟨23340740116597271227752149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15560493411064847485168099 23340740116597271227752149)
                  ·
                    refine ⟨547048596482748544400441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23340740116597271227752149 547048596482748544400441)
                    ·
                      rfl

theorem cell22_1598060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_1598060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598060 prefixEnd_1598060 := by exact prefixLift 1598060
  have htrace : WordTrace (prefixWord ++ tailWord_1598060) baseStart_1598060 baseEnd_1598060 := by
    simpa [prefixWord, tailWord_1598060, baseEnd_1598060] using wordTrace_append hprefix tailTrace_1598060
  have hstable : (prefixWord ++ tailWord_1598060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598060).length < 2 ^ (prefixWord ++ tailWord_1598060).sum := by decide
  have hdescent : baseEnd_1598060 < baseStart_1598060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598062 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 7]
def baseStart_1598062 : Nat := 118140960795 + 1598062 * 2 ^ 59
def prefixEnd_1598062 : Nat := 4983230072969 + 3 ^ 40 * 1598062 * 2
def baseEnd_1598062 : Nat := 182349760374540401950145

theorem tailTrace_1598062 : CollatzResearch.WordTrace tailWord_1598062 prefixEnd_1598062 182349760374540401950145 := by
  unfold tailWord_1598062
  simp only [CollatzResearch.WordTrace]
  refine ⟨7285763692062722013232555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38857406357667850737240293 7285763692062722013232555)
  ·
    refine ⟨10928645538094083019848833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7285763692062722013232555 10928645538094083019848833)
    ·
      refine ⟨8196484153570562264886625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10928645538094083019848833 8196484153570562264886625)
      ·
        refine ⟨6147363115177921698664969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8196484153570562264886625 6147363115177921698664969)
        ·
          refine ⟨4610522336383441273998727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6147363115177921698664969 4610522336383441273998727)
          ·
            refine ⟨6915783504575161910998091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4610522336383441273998727 6915783504575161910998091)
            ·
              refine ⟨10373675256862742866497137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6915783504575161910998091 10373675256862742866497137)
              ·
                refine ⟨7780256442647057149872853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10373675256862742866497137 7780256442647057149872853)
                ·
                  refine ⟨182349760374540401950145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7780256442647057149872853 182349760374540401950145)
                  ·
                    rfl

theorem cell22_1598062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_1598062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598062 prefixEnd_1598062 := by exact prefixLift 1598062
  have htrace : WordTrace (prefixWord ++ tailWord_1598062) baseStart_1598062 baseEnd_1598062 := by
    simpa [prefixWord, tailWord_1598062, baseEnd_1598062] using wordTrace_append hprefix tailTrace_1598062
  have hstable : (prefixWord ++ tailWord_1598062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598062).length < 2 ^ (prefixWord ++ tailWord_1598062).sum := by decide
  have hdescent : baseEnd_1598062 < baseStart_1598062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598109 : List Nat := [1, 4, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_1598109 : Nat := 118140960795 + 1598109 * 2 ^ 59
def prefixEnd_1598109 : Nat := 4983230072969 + 3 ^ 40 * 1598109 * 2
def baseEnd_1598109 : Nat := 547065370184128749925291

theorem tailTrace_1598109 : CollatzResearch.WordTrace tailWord_1598109 prefixEnd_1598109 547065370184128749925291 := by
  unfold tailWord_1598109
  simp only [CollatzResearch.WordTrace]
  refine ⟨58287823767331503132821381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38858549178221002088547587 58287823767331503132821381)
  ·
    refine ⟨10928966956374656837404009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58287823767331503132821381 10928966956374656837404009)
    ·
      refine ⟨8196725217280992628053007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10928966956374656837404009 8196725217280992628053007)
      ·
        refine ⟨12295087825921488942079511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8196725217280992628053007 12295087825921488942079511)
        ·
          refine ⟨18442631738882233413119267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12295087825921488942079511 18442631738882233413119267)
          ·
            refine ⟨27663947608323350119678901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18442631738882233413119267 27663947608323350119678901)
            ·
              refine ⟨2593495088280314073719897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27663947608323350119678901 2593495088280314073719897)
              ·
                refine ⟨1945121316210235555289923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2593495088280314073719897 1945121316210235555289923)
                ·
                  refine ⟨2917681974315353332934885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1945121316210235555289923 2917681974315353332934885)
                  ·
                    refine ⟨547065370184128749925291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2917681974315353332934885 547065370184128749925291)
                    ·
                      rfl

theorem cell22_1598109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_1598109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598109 prefixEnd_1598109 := by exact prefixLift 1598109
  have htrace : WordTrace (prefixWord ++ tailWord_1598109) baseStart_1598109 baseEnd_1598109 := by
    simpa [prefixWord, tailWord_1598109, baseEnd_1598109] using wordTrace_append hprefix tailTrace_1598109
  have hstable : (prefixWord ++ tailWord_1598109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598109).length < 2 ^ (prefixWord ++ tailWord_1598109).sum := by decide
  have hdescent : baseEnd_1598109 < baseStart_1598109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598134 : List Nat := [5, 1, 3, 1, 3, 1, 2, 2, 1, 3]
def baseStart_1598134 : Nat := 118140960795 + 1598134 * 2 ^ 59
def prefixEnd_1598134 : Nat := 4983230072969 + 3 ^ 40 * 1598134 * 2
def baseEnd_1598134 : Nat := 547073928195037018050215

theorem tailTrace_1598134 : CollatzResearch.WordTrace tailWord_1598134 prefixEnd_1598134 547073928195037018050215 := by
  unfold tailWord_1598134
  simp only [CollatzResearch.WordTrace]
  refine ⟨3643045974515058275155091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38859157061493954934987637 3643045974515058275155091)
  ·
    refine ⟨5464568961772587412732637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3643045974515058275155091 5464568961772587412732637)
    ·
      refine ⟨2049213360664720279774739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5464568961772587412732637 2049213360664720279774739)
      ·
        refine ⟨3073820040997080419662109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2049213360664720279774739 3073820040997080419662109)
        ·
          refine ⟨1152682515373905157373291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3073820040997080419662109 1152682515373905157373291)
          ·
            refine ⟨1729023773060857736059937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1152682515373905157373291 1729023773060857736059937)
            ·
              refine ⟨1296767829795643302044953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1729023773060857736059937 1296767829795643302044953)
              ·
                refine ⟨972575872346732476533715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1296767829795643302044953 972575872346732476533715)
                ·
                  refine ⟨1458863808520098714800573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 972575872346732476533715 1458863808520098714800573)
                  ·
                    refine ⟨547073928195037018050215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1458863808520098714800573 547073928195037018050215)
                    ·
                      rfl

theorem cell22_1598134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_1598134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598134 prefixEnd_1598134 := by exact prefixLift 1598134
  have htrace : WordTrace (prefixWord ++ tailWord_1598134) baseStart_1598134 baseEnd_1598134 := by
    simpa [prefixWord, tailWord_1598134, baseEnd_1598134] using wordTrace_append hprefix tailTrace_1598134
  have hstable : (prefixWord ++ tailWord_1598134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598134).length < 2 ^ (prefixWord ++ tailWord_1598134).sum := by decide
  have hdescent : baseEnd_1598134 < baseStart_1598134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598135 : List Nat := [1, 1, 3, 1, 16]
def baseStart_1598135 : Nat := 118140960795 + 1598135 * 2 ^ 59
def prefixEnd_1598135 : Nat := 4983230072969 + 3 ^ 40 * 1598135 * 2
def baseEnd_1598135 : Nat := 2251334446565733945577

theorem tailTrace_1598135 : CollatzResearch.WordTrace tailWord_1598135 prefixEnd_1598135 2251334446565733945577 := by
  unfold tailWord_1598135
  simp only [CollatzResearch.WordTrace]
  refine ⟨58288772065237309573267859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38859181376824873048845239 58288772065237309573267859)
  ·
    refine ⟨87433158097855964359901789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58288772065237309573267859 87433158097855964359901789)
    ·
      refine ⟨32787434286695986634963171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87433158097855964359901789 32787434286695986634963171)
      ·
        refine ⟨49181151430043979952444757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32787434286695986634963171 49181151430043979952444757)
        ·
          refine ⟨2251334446565733945577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 49181151430043979952444757 2251334446565733945577)
          ·
            rfl

theorem cell22_1598135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 16].length) (baseStart_1598135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598135 prefixEnd_1598135 := by exact prefixLift 1598135
  have htrace : WordTrace (prefixWord ++ tailWord_1598135) baseStart_1598135 baseEnd_1598135 := by
    simpa [prefixWord, tailWord_1598135, baseEnd_1598135] using wordTrace_append hprefix tailTrace_1598135
  have hstable : (prefixWord ++ tailWord_1598135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598135).length < 2 ^ (prefixWord ++ tailWord_1598135).sum := by decide
  have hdescent : baseEnd_1598135 < baseStart_1598135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598141 : List Nat := [1, 4, 1, 2, 1, 3, 4, 2, 4]
def baseStart_1598141 : Nat := 118140960795 + 1598141 * 2 ^ 59
def prefixEnd_1598141 : Nat := 4983230072969 + 3 ^ 40 * 1598141 * 2
def baseEnd_1598141 : Nat := 182358774812697111041731

theorem tailTrace_1598141 : CollatzResearch.WordTrace tailWord_1598141 prefixEnd_1598141 182358774812697111041731 := by
  unfold tailWord_1598141
  simp only [CollatzResearch.WordTrace]
  refine ⟨58288990903215572597986277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38859327268810381731990851 58288990903215572597986277)
  ·
    refine ⟨10929185794352919862122427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58288990903215572597986277 10929185794352919862122427)
    ·
      refine ⟨16393778691529379793183641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10929185794352919862122427 16393778691529379793183641)
      ·
        refine ⟨12295334018647034844887731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16393778691529379793183641 12295334018647034844887731)
        ·
          refine ⟨18443001027970552267331597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12295334018647034844887731 18443001027970552267331597)
          ·
            refine ⟨6916125385488957100249349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18443001027970552267331597 6916125385488957100249349)
            ·
              refine ⟨1296773509779179456296753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6916125385488957100249349 1296773509779179456296753)
              ·
                refine ⟨972580132334384592222565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1296773509779179456296753 972580132334384592222565)
                ·
                  refine ⟨182358774812697111041731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 972580132334384592222565 182358774812697111041731)
                  ·
                    rfl

theorem cell22_1598141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_1598141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598141 prefixEnd_1598141 := by exact prefixLift 1598141
  have htrace : WordTrace (prefixWord ++ tailWord_1598141) baseStart_1598141 baseEnd_1598141 := by
    simpa [prefixWord, tailWord_1598141, baseEnd_1598141] using wordTrace_append hprefix tailTrace_1598141
  have hstable : (prefixWord ++ tailWord_1598141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598141).length < 2 ^ (prefixWord ++ tailWord_1598141).sum := by decide
  have hdescent : baseEnd_1598141 < baseStart_1598141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598152 : List Nat := [2, 1, 3, 1, 2, 3, 3, 7]
def baseStart_1598152 : Nat := 118140960795 + 1598152 * 2 ^ 59
def prefixEnd_1598152 : Nat := 4983230072969 + 3 ^ 40 * 1598152 * 2
def baseEnd_1598152 : Nat := 60786676662543441233351

theorem tailTrace_1598152 : CollatzResearch.WordTrace tailWord_1598152 prefixEnd_1598152 60786676662543441233351 := by
  unfold tailWord_1598152
  simp only [CollatzResearch.WordTrace]
  refine ⟨29144696053087860738318355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38859594737450480984424473 29144696053087860738318355)
  ·
    refine ⟨43717044079631791107477533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29144696053087860738318355 43717044079631791107477533)
    ·
      refine ⟨16393891529861921665304075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43717044079631791107477533 16393891529861921665304075)
      ·
        refine ⟨24590837294792882497956113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16393891529861921665304075 24590837294792882497956113)
        ·
          refine ⟨18443127971094661873467085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24590837294792882497956113 18443127971094661873467085)
          ·
            refine ⟨6916172989160498202550157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18443127971094661873467085 6916172989160498202550157)
            ·
              refine ⟨2593564870935186825956309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6916172989160498202550157 2593564870935186825956309)
              ·
                refine ⟨60786676662543441233351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2593564870935186825956309 60786676662543441233351)
                ·
                  rfl

theorem cell22_1598152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 7].length) (baseStart_1598152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598152 prefixEnd_1598152 := by exact prefixLift 1598152
  have htrace : WordTrace (prefixWord ++ tailWord_1598152) baseStart_1598152 baseEnd_1598152 := by
    simpa [prefixWord, tailWord_1598152, baseEnd_1598152] using wordTrace_append hprefix tailTrace_1598152
  have hstable : (prefixWord ++ tailWord_1598152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598152).length < 2 ^ (prefixWord ++ tailWord_1598152).sum := by decide
  have hdescent : baseEnd_1598152 < baseStart_1598152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598156 : List Nat := [2, 2, 1, 5, 1, 1, 2, 3, 2, 3]
def baseStart_1598156 : Nat := 118140960795 + 1598156 * 2 ^ 59
def prefixEnd_1598156 : Nat := 4983230072969 + 3 ^ 40 * 1598156 * 2
def baseEnd_1598156 : Nat := 547081459244636294000147

theorem tailTrace_1598156 : CollatzResearch.WordTrace tailWord_1598156 prefixEnd_1598156 547081459244636294000147 := by
  unfold tailWord_1598156
  simp only [CollatzResearch.WordTrace]
  refine ⟨29144768999080615079891161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38859691998774153439854881 29144768999080615079891161)
  ·
    refine ⟨21858576749310461309918371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29144768999080615079891161 21858576749310461309918371)
    ·
      refine ⟨32787865123965691964877557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21858576749310461309918371 32787865123965691964877557)
      ·
        refine ⟨3073862355371783621707271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32787865123965691964877557 3073862355371783621707271)
        ·
          refine ⟨4610793533057675432560907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3073862355371783621707271 4610793533057675432560907)
          ·
            refine ⟨6916190299586513148841361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4610793533057675432560907 6916190299586513148841361)
            ·
              refine ⟨5187142724689884861631021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6916190299586513148841361 5187142724689884861631021)
              ·
                refine ⟨1945178521758706823111633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5187142724689884861631021 1945178521758706823111633)
                ·
                  refine ⟨1458883891319030117333725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1945178521758706823111633 1458883891319030117333725)
                  ·
                    refine ⟨547081459244636294000147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1458883891319030117333725 547081459244636294000147)
                    ·
                      rfl

theorem cell22_1598156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 3, 2, 3].length) (baseStart_1598156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598156 prefixEnd_1598156 := by exact prefixLift 1598156
  have htrace : WordTrace (prefixWord ++ tailWord_1598156) baseStart_1598156 baseEnd_1598156 := by
    simpa [prefixWord, tailWord_1598156, baseEnd_1598156] using wordTrace_append hprefix tailTrace_1598156
  have hstable : (prefixWord ++ tailWord_1598156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598156).length < 2 ^ (prefixWord ++ tailWord_1598156).sum := by decide
  have hdescent : baseEnd_1598156 < baseStart_1598156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598259 : List Nat := [1, 1, 1, 2, 6, 1, 3, 1, 6]
def baseStart_1598259 : Nat := 118140960795 + 1598259 * 2 ^ 59
def prefixEnd_1598259 : Nat := 4983230072969 + 3 ^ 40 * 1598259 * 2
def baseEnd_1598259 : Nat := 182372239416526119558277

theorem tailTrace_1598259 : CollatzResearch.WordTrace tailWord_1598259 prefixEnd_1598259 182372239416526119558277 := by
  unfold tailWord_1598259
  simp only [CollatzResearch.WordTrace]
  refine ⟨58293294716788078750781831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38862196477858719167187887 58293294716788078750781831)
  ·
    refine ⟨87439942075182118126172747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58293294716788078750781831 87439942075182118126172747)
    ·
      refine ⟨131159913112773177189259121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87439942075182118126172747 131159913112773177189259121)
      ·
        refine ⟨98369934834579882891944341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131159913112773177189259121 98369934834579882891944341)
        ·
          refine ⟨4611090695370932010559891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98369934834579882891944341 4611090695370932010559891)
          ·
            refine ⟨6916636043056398015839837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4611090695370932010559891 6916636043056398015839837)
            ·
              refine ⟨2593738516146149255939939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6916636043056398015839837 2593738516146149255939939)
              ·
                refine ⟨3890607774219223883909909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2593738516146149255939939 3890607774219223883909909)
                ·
                  refine ⟨182372239416526119558277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3890607774219223883909909 182372239416526119558277)
                  ·
                    rfl

theorem cell22_1598259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 6].length) (baseStart_1598259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598259 prefixEnd_1598259 := by exact prefixLift 1598259
  have htrace : WordTrace (prefixWord ++ tailWord_1598259) baseStart_1598259 baseEnd_1598259 := by
    simpa [prefixWord, tailWord_1598259, baseEnd_1598259] using wordTrace_append hprefix tailTrace_1598259
  have hstable : (prefixWord ++ tailWord_1598259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598259).length < 2 ^ (prefixWord ++ tailWord_1598259).sum := by decide
  have hdescent : baseEnd_1598259 < baseStart_1598259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598272 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 3, 6]
def baseStart_1598272 : Nat := 118140960795 + 1598272 * 2 ^ 59
def prefixEnd_1598272 : Nat := 4983230072969 + 3 ^ 40 * 1598272 * 2
def baseEnd_1598272 : Nat := 547121168415250658099791

theorem tailTrace_1598272 : CollatzResearch.WordTrace tailWord_1598272 prefixEnd_1598272 547121168415250658099791 := by
  unfold tailWord_1598272
  simp only [CollatzResearch.WordTrace]
  refine ⟨29146884432870490985502535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38862512577160654647336713 29146884432870490985502535)
  ·
    refine ⟨43720326649305736478253803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29146884432870490985502535 43720326649305736478253803)
    ·
      refine ⟨65580489973958604717380705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43720326649305736478253803 65580489973958604717380705)
      ·
        refine ⟨49185367480468953538035529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65580489973958604717380705 49185367480468953538035529)
        ·
          refine ⟨36889025610351715153526647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49185367480468953538035529 36889025610351715153526647)
          ·
            refine ⟨55333538415527572730289971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36889025610351715153526647 55333538415527572730289971)
            ·
              refine ⟨83000307623291359095434957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55333538415527572730289971 83000307623291359095434957)
              ·
                refine ⟨31125115358734259660788109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83000307623291359095434957 31125115358734259660788109)
                ·
                  refine ⟨11671918259525347372795541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31125115358734259660788109 11671918259525347372795541)
                  ·
                    refine ⟨547121168415250658099791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11671918259525347372795541 547121168415250658099791)
                    ·
                      rfl

theorem cell22_1598272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_1598272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598272 prefixEnd_1598272 := by exact prefixLift 1598272
  have htrace : WordTrace (prefixWord ++ tailWord_1598272) baseStart_1598272 baseEnd_1598272 := by
    simpa [prefixWord, tailWord_1598272, baseEnd_1598272] using wordTrace_append hprefix tailTrace_1598272
  have hstable : (prefixWord ++ tailWord_1598272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598272).length < 2 ^ (prefixWord ++ tailWord_1598272).sum := by decide
  have hdescent : baseEnd_1598272 < baseStart_1598272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598308 : List Nat := [2, 3, 1, 1, 4, 2, 2, 2, 2, 3]
def baseStart_1598308 : Nat := 118140960795 + 1598308 * 2 ^ 59
def prefixEnd_1598308 : Nat := 4983230072969 + 3 ^ 40 * 1598308 * 2
def baseEnd_1598308 : Nat := 547133491950958564199681

theorem tailTrace_1598308 : CollatzResearch.WordTrace tailWord_1598308 prefixEnd_1598308 547133491950958564199681 := by
  unfold tailWord_1598308
  simp only [CollatzResearch.WordTrace]
  refine ⟨29147540946805280059657789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38863387929073706746210385 29147540946805280059657789)
  ·
    refine ⟨10930327855051980022371671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29147540946805280059657789 10930327855051980022371671)
    ·
      refine ⟨16395491782577970033557507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10930327855051980022371671 16395491782577970033557507)
      ·
        refine ⟨24593237673866955050336261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16395491782577970033557507 24593237673866955050336261)
        ·
          refine ⟨4611232063850054071938049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24593237673866955050336261 4611232063850054071938049)
          ·
            refine ⟨3458424047887540553953537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4611232063850054071938049 3458424047887540553953537)
            ·
              refine ⟨2593818035915655415465153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3458424047887540553953537 2593818035915655415465153)
              ·
                refine ⟨1945363526936741561598865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2593818035915655415465153 1945363526936741561598865)
                ·
                  refine ⟨1459022645202556171199149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1945363526936741561598865 1459022645202556171199149)
                  ·
                    refine ⟨547133491950958564199681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1459022645202556171199149 547133491950958564199681)
                    ·
                      rfl

theorem cell22_1598308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_1598308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598308 prefixEnd_1598308 := by exact prefixLift 1598308
  have htrace : WordTrace (prefixWord ++ tailWord_1598308) baseStart_1598308 baseEnd_1598308 := by
    simpa [prefixWord, tailWord_1598308, baseEnd_1598308] using wordTrace_append hprefix tailTrace_1598308
  have hstable : (prefixWord ++ tailWord_1598308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598308).length < 2 ^ (prefixWord ++ tailWord_1598308).sum := by decide
  have hdescent : baseEnd_1598308 < baseStart_1598308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598319 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 7, 3]
def baseStart_1598319 : Nat := 118140960795 + 1598319 * 2 ^ 59
def prefixEnd_1598319 : Nat := 4983230072969 + 3 ^ 40 * 1598319 * 2
def baseEnd_1598319 : Nat := 547137257475758202174647

theorem tailTrace_1598319 : CollatzResearch.WordTrace tailWord_1598319 prefixEnd_1598319 547137257475758202174647 := by
  unfold tailWord_1598319
  simp only [CollatzResearch.WordTrace]
  refine ⟨58295483096570708997966011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38863655397713805998644007 58295483096570708997966011)
  ·
    refine ⟨87443224644856063496949017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58295483096570708997966011 87443224644856063496949017)
    ·
      refine ⟨65582418483642047622711763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87443224644856063496949017 65582418483642047622711763)
      ·
        refine ⟨98373627725463071434067645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65582418483642047622711763 98373627725463071434067645)
        ·
          refine ⟨36890110397048651787775367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98373627725463071434067645 36890110397048651787775367)
          ·
            refine ⟨55335165595572977681663051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36890110397048651787775367 55335165595572977681663051)
            ·
              refine ⟨83002748393359466522494577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55335165595572977681663051 83002748393359466522494577)
              ·
                refine ⟨62252061295019599891870933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83002748393359466522494577 62252061295019599891870933)
                ·
                  refine ⟨1459032686602021872465725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 62252061295019599891870933 1459032686602021872465725)
                  ·
                    refine ⟨547137257475758202174647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1459032686602021872465725 547137257475758202174647)
                    ·
                      rfl

theorem cell22_1598319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 3].length) (baseStart_1598319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598319 prefixEnd_1598319 := by exact prefixLift 1598319
  have htrace : WordTrace (prefixWord ++ tailWord_1598319) baseStart_1598319 baseEnd_1598319 := by
    simpa [prefixWord, tailWord_1598319, baseEnd_1598319] using wordTrace_append hprefix tailTrace_1598319
  have hstable : (prefixWord ++ tailWord_1598319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598319).length < 2 ^ (prefixWord ++ tailWord_1598319).sum := by decide
  have hdescent : baseEnd_1598319 < baseStart_1598319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598370 : List Nat := [3, 3, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_1598370 : Nat := 118140960795 + 1598370 * 2 ^ 59
def prefixEnd_1598370 : Nat := 4983230072969 + 3 ^ 40 * 1598370 * 2
def baseEnd_1598370 : Nat := 547154715818011069149491

theorem tailTrace_1598370 : CollatzResearch.WordTrace tailWord_1598370 prefixEnd_1598370 547154715818011069149491 := by
  unfold tailWord_1598370
  simp only [CollatzResearch.WordTrace]
  refine ⟨14574335804846486177018141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38864895479590629805381709 14574335804846486177018141)
  ·
    refine ⟨5465375926817432316381803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14574335804846486177018141 5465375926817432316381803)
    ·
      refine ⟨8198063890226148474572705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5465375926817432316381803 8198063890226148474572705)
      ·
        refine ⟨6148547917669611355929529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8198063890226148474572705 6148547917669611355929529)
        ·
          refine ⟨4611410938252208516947147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6148547917669611355929529 4611410938252208516947147)
          ·
            refine ⟨6917116407378312775420721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4611410938252208516947147 6917116407378312775420721)
            ·
              refine ⟨5187837305533734581565541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6917116407378312775420721 5187837305533734581565541)
              ·
                refine ⟨972719494787575234043539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5187837305533734581565541 972719494787575234043539)
                ·
                  refine ⟨1459079242181362851065309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 972719494787575234043539 1459079242181362851065309)
                  ·
                    refine ⟨547154715818011069149491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1459079242181362851065309 547154715818011069149491)
                    ·
                      rfl

theorem cell22_1598370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_1598370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598370 prefixEnd_1598370 := by exact prefixLift 1598370
  have htrace : WordTrace (prefixWord ++ tailWord_1598370) baseStart_1598370 baseEnd_1598370 := by
    simpa [prefixWord, tailWord_1598370, baseEnd_1598370] using wordTrace_append hprefix tailTrace_1598370
  have hstable : (prefixWord ++ tailWord_1598370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598370).length < 2 ^ (prefixWord ++ tailWord_1598370).sum := by decide
  have hdescent : baseEnd_1598370 < baseStart_1598370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598394 : List Nat := [3, 1, 1, 1, 2, 1, 3, 4, 6]
def baseStart_1598394 : Nat := 118140960795 + 1598394 * 2 ^ 59
def prefixEnd_1598394 : Nat := 4983230072969 + 3 ^ 40 * 1598394 * 2
def baseEnd_1598394 : Nat := 182387643836161002183139

theorem tailTrace_1598394 : CollatzResearch.WordTrace tailWord_1598394 prefixEnd_1598394 182387643836161002183139 := by
  unfold tailWord_1598394
  simp only [CollatzResearch.WordTrace]
  refine ⟨14574554642824749201736559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38865479047532664537964157 14574554642824749201736559)
  ·
    refine ⟨21861831964237123802604839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14574554642824749201736559 21861831964237123802604839)
    ·
      refine ⟨32792747946355685703907259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21861831964237123802604839 32792747946355685703907259)
      ·
        refine ⟨49189121919533528555860889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32792747946355685703907259 49189121919533528555860889)
        ·
          refine ⟨36891841439650146416895667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49189121919533528555860889 36891841439650146416895667)
          ·
            refine ⟨55337762159475219625343501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36891841439650146416895667 55337762159475219625343501)
            ·
              refine ⟨20751660809803207359503813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55337762159475219625343501 20751660809803207359503813)
              ·
                refine ⟨3890936401838101379906965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20751660809803207359503813 3890936401838101379906965)
                ·
                  refine ⟨182387643836161002183139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3890936401838101379906965 182387643836161002183139)
                  ·
                    rfl

theorem cell22_1598394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_1598394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598394 prefixEnd_1598394 := by exact prefixLift 1598394
  have htrace : WordTrace (prefixWord ++ tailWord_1598394) baseStart_1598394 baseEnd_1598394 := by
    simpa [prefixWord, tailWord_1598394, baseEnd_1598394] using wordTrace_append hprefix tailTrace_1598394
  have hstable : (prefixWord ++ tailWord_1598394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598394).length < 2 ^ (prefixWord ++ tailWord_1598394).sum := by decide
  have hdescent : baseEnd_1598394 < baseStart_1598394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598404 : List Nat := [2, 3, 3, 3, 1, 2, 1, 3, 1, 3]
def baseStart_1598404 : Nat := 118140960795 + 1598404 * 2 ^ 59
def prefixEnd_1598404 : Nat := 4983230072969 + 3 ^ 40 * 1598404 * 2
def baseEnd_1598404 : Nat := 547166354712846313799387

theorem tailTrace_1598404 : CollatzResearch.WordTrace tailWord_1598404 prefixEnd_1598404 547166354712846313799387 := by
  unfold tailWord_1598404
  simp only [CollatzResearch.WordTrace]
  refine ⟨29149291650631384257405133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38865722200841845676540177 29149291650631384257405133)
  ·
    refine ⟨10930984368986769096526925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29149291650631384257405133 10930984368986769096526925)
    ·
      refine ⟨4099119138370038411197597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10930984368986769096526925 4099119138370038411197597)
      ·
        refine ⟨1537169676888764404199099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4099119138370038411197597 1537169676888764404199099)
        ·
          refine ⟨2305754515333146606298649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1537169676888764404199099 2305754515333146606298649)
          ·
            refine ⟨1729315886499859954723987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2305754515333146606298649 1729315886499859954723987)
            ·
              refine ⟨2593973829749789932085981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1729315886499859954723987 2593973829749789932085981)
              ·
                refine ⟨972740186156171224532243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2593973829749789932085981 972740186156171224532243)
                ·
                  refine ⟨1459110279234256836798365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 972740186156171224532243 1459110279234256836798365)
                  ·
                    refine ⟨547166354712846313799387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1459110279234256836798365 547166354712846313799387)
                    ·
                      rfl

theorem cell22_1598404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_1598404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598404 prefixEnd_1598404 := by exact prefixLift 1598404
  have htrace : WordTrace (prefixWord ++ tailWord_1598404) baseStart_1598404 baseEnd_1598404 := by
    simpa [prefixWord, tailWord_1598404, baseEnd_1598404] using wordTrace_append hprefix tailTrace_1598404
  have hstable : (prefixWord ++ tailWord_1598404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598404).length < 2 ^ (prefixWord ++ tailWord_1598404).sum := by decide
  have hdescent : baseEnd_1598404 < baseStart_1598404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598501 : List Nat := [1, 3, 1, 2, 2, 2, 1, 5, 5]
def baseStart_1598501 : Nat := 118140960795 + 1598501 * 2 ^ 59
def prefixEnd_1598501 : Nat := 4983230072969 + 3 ^ 40 * 1598501 * 2
def baseEnd_1598501 : Nat := 182399853265056798041363

theorem tailTrace_1598501 : CollatzResearch.WordTrace tailWord_1598501 prefixEnd_1598501 182399853265056798041363 := by
  unfold tailWord_1598501
  simp only [CollatzResearch.WordTrace]
  refine ⟨58302121181911354081091357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38868080787940902720727571 58302121181911354081091357)
  ·
    refine ⟨21863295443216757780409259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58302121181911354081091357 21863295443216757780409259)
    ·
      refine ⟨32794943164825136670613889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21863295443216757780409259 32794943164825136670613889)
      ·
        refine ⟨24596207373618852502960417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32794943164825136670613889 24596207373618852502960417)
        ·
          refine ⟨18447155530214139377220313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24596207373618852502960417 18447155530214139377220313)
          ·
            refine ⟨13835366647660604532915235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18447155530214139377220313 13835366647660604532915235)
            ·
              refine ⟨20753049971490906799372853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13835366647660604532915235 20753049971490906799372853)
              ·
                refine ⟨1945598434827272512441205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20753049971490906799372853 1945598434827272512441205)
                ·
                  refine ⟨182399853265056798041363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1945598434827272512441205 182399853265056798041363)
                  ·
                    rfl

theorem cell22_1598501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_1598501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598501 prefixEnd_1598501 := by exact prefixLift 1598501
  have htrace : WordTrace (prefixWord ++ tailWord_1598501) baseStart_1598501 baseEnd_1598501 := by
    simpa [prefixWord, tailWord_1598501, baseEnd_1598501] using wordTrace_append hprefix tailTrace_1598501
  have hstable : (prefixWord ++ tailWord_1598501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598501).length < 2 ^ (prefixWord ++ tailWord_1598501).sum := by decide
  have hdescent : baseEnd_1598501 < baseStart_1598501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598576 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 1, 6]
def baseStart_1598576 : Nat := 118140960795 + 1598576 * 2 ^ 59
def prefixEnd_1598576 : Nat := 4983230072969 + 3 ^ 40 * 1598576 * 2
def baseEnd_1598576 : Nat := 547225233827895198498859

theorem tailTrace_1598576 : CollatzResearch.WordTrace tailWord_1598576 prefixEnd_1598576 547225233827895198498859 := by
  unfold tailWord_1598576
  simp only [CollatzResearch.WordTrace]
  refine ⟨29152428328319820945035791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38869904437759761260047721 29152428328319820945035791)
  ·
    refine ⟨43728642492479731417553687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29152428328319820945035791 43728642492479731417553687)
    ·
      refine ⟨65592963738719597126330531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43728642492479731417553687 65592963738719597126330531)
      ·
        refine ⟨98389445608079395689495797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65592963738719597126330531 98389445608079395689495797)
        ·
          refine ⟨9224010525757443345890231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98389445608079395689495797 9224010525757443345890231)
          ·
            refine ⟨13836015788636165018835347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9224010525757443345890231 13836015788636165018835347)
            ·
              refine ⟨20754023682954247528253021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13836015788636165018835347 20754023682954247528253021)
              ·
                refine ⟨7782758881107842823094883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20754023682954247528253021 7782758881107842823094883)
                ·
                  refine ⟨11674138321661764234642325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7782758881107842823094883 11674138321661764234642325)
                  ·
                    refine ⟨547225233827895198498859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11674138321661764234642325 547225233827895198498859)
                    ·
                      rfl

theorem cell22_1598576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_1598576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598576 prefixEnd_1598576 := by exact prefixLift 1598576
  have htrace : WordTrace (prefixWord ++ tailWord_1598576) baseStart_1598576 baseEnd_1598576 := by
    simpa [prefixWord, tailWord_1598576, baseEnd_1598576] using wordTrace_append hprefix tailTrace_1598576
  have hstable : (prefixWord ++ tailWord_1598576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598576).length < 2 ^ (prefixWord ++ tailWord_1598576).sum := by decide
  have hdescent : baseEnd_1598576 < baseStart_1598576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598578 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 6, 3]
def baseStart_1598578 : Nat := 118140960795 + 1598578 * 2 ^ 59
def prefixEnd_1598578 : Nat := 4983230072969 + 3 ^ 40 * 1598578 * 2
def baseEnd_1598578 : Nat := 547225918468767859948853

theorem tailTrace_1598578 : CollatzResearch.WordTrace tailWord_1598578 prefixEnd_1598578 547225918468767859948853 := by
  unfold tailWord_1598578
  simp only [CollatzResearch.WordTrace]
  refine ⟨14576232400658099057911097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38869953068421597487762925 14576232400658099057911097)
  ·
    refine ⟨10932174300493574293433323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14576232400658099057911097 10932174300493574293433323)
    ·
      refine ⟨16398261450740361440149985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10932174300493574293433323 16398261450740361440149985)
      ·
        refine ⟨12298696088055271080112489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16398261450740361440149985 12298696088055271080112489)
        ·
          refine ⟨9224022066041453310084367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12298696088055271080112489 9224022066041453310084367)
          ·
            refine ⟨13836033099062179965126551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9224022066041453310084367 13836033099062179965126551)
            ·
              refine ⟨20754049648593269947689827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13836033099062179965126551 20754049648593269947689827)
              ·
                refine ⟨31131074472889904921534741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20754049648593269947689827 31131074472889904921534741)
                ·
                  refine ⟨1459269115916714293196941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31131074472889904921534741 1459269115916714293196941)
                  ·
                    refine ⟨547225918468767859948853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1459269115916714293196941 547225918468767859948853)
                    ·
                      rfl

theorem cell22_1598578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_1598578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598578 prefixEnd_1598578 := by exact prefixLift 1598578
  have htrace : WordTrace (prefixWord ++ tailWord_1598578) baseStart_1598578 baseEnd_1598578 := by
    simpa [prefixWord, tailWord_1598578, baseEnd_1598578] using wordTrace_append hprefix tailTrace_1598578
  have hstable : (prefixWord ++ tailWord_1598578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598578).length < 2 ^ (prefixWord ++ tailWord_1598578).sum := by decide
  have hdescent : baseEnd_1598578 < baseStart_1598578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598593 : List Nat := [1, 2, 4, 2, 2, 1, 1, 1, 4, 4]
def baseStart_1598593 : Nat := 118140960795 + 1598593 * 2 ^ 59
def prefixEnd_1598593 : Nat := 4983230072969 + 3 ^ 40 * 1598593 * 2
def baseEnd_1598593 : Nat := 547231053275312820823807

theorem tailTrace_1598593 : CollatzResearch.WordTrace tailWord_1598593 prefixEnd_1598593 547231053275312820823807 := by
  unfold tailWord_1598593
  simp only [CollatzResearch.WordTrace]
  refine ⟨58305476697578053793440433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38870317798385369195626955 58305476697578053793440433)
  ·
    refine ⟨43729107523183540345080325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58305476697578053793440433 43729107523183540345080325)
    ·
      refine ⟨8199207660596913814702561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43729107523183540345080325 8199207660596913814702561)
      ·
        refine ⟨6149405745447685361026921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8199207660596913814702561 6149405745447685361026921)
        ·
          refine ⟨4612054309085764020770191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6149405745447685361026921 4612054309085764020770191)
          ·
            refine ⟨6918081463628646031155287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4612054309085764020770191 6918081463628646031155287)
            ·
              refine ⟨10377122195442969046732931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6918081463628646031155287 10377122195442969046732931)
              ·
                refine ⟨15565683293164453570099397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10377122195442969046732931 15565683293164453570099397)
                ·
                  refine ⟨2918565617468335044393637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15565683293164453570099397 2918565617468335044393637)
                  ·
                    refine ⟨547231053275312820823807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2918565617468335044393637 547231053275312820823807)
                    ·
                      rfl

theorem cell22_1598593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_1598593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598593 prefixEnd_1598593 := by exact prefixLift 1598593
  have htrace : WordTrace (prefixWord ++ tailWord_1598593) baseStart_1598593 baseEnd_1598593 := by
    simpa [prefixWord, tailWord_1598593, baseEnd_1598593] using wordTrace_append hprefix tailTrace_1598593
  have hstable : (prefixWord ++ tailWord_1598593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598593).length < 2 ^ (prefixWord ++ tailWord_1598593).sum := by decide
  have hdescent : baseEnd_1598593 < baseStart_1598593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598597 : List Nat := [1, 3, 1, 1, 6, 1, 3, 2, 4]
def baseStart_1598597 : Nat := 118140960795 + 1598597 * 2 ^ 59
def prefixEnd_1598597 : Nat := 4983230072969 + 3 ^ 40 * 1598597 * 2
def baseEnd_1598597 : Nat := 182410807519019381241265

theorem tailTrace_1598597 : CollatzResearch.WordTrace tailWord_1598597 prefixEnd_1598597 182410807519019381241265 := by
  unfold tailWord_1598597
  simp only [CollatzResearch.WordTrace]
  refine ⟨58305622589563562476586045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38870415059709041651057363 58305622589563562476586045)
  ·
    refine ⟨21864608471086335928719767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58305622589563562476586045 21864608471086335928719767)
    ·
      refine ⟨32796912706629503893079651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21864608471086335928719767 32796912706629503893079651)
      ·
        refine ⟨49195369059944255839619477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32796912706629503893079651 49195369059944255839619477)
        ·
          refine ⟨2306032924684886992482163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49195369059944255839619477 2306032924684886992482163)
          ·
            refine ⟨3459049387027330488723245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306032924684886992482163 3459049387027330488723245)
            ·
              refine ⟨1297143520135248933271217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3459049387027330488723245 1297143520135248933271217)
              ·
                refine ⟨972857640101436699953413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1297143520135248933271217 972857640101436699953413)
                ·
                  refine ⟨182410807519019381241265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 972857640101436699953413 182410807519019381241265)
                  ·
                    rfl

theorem cell22_1598597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_1598597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598597 prefixEnd_1598597 := by exact prefixLift 1598597
  have htrace : WordTrace (prefixWord ++ tailWord_1598597) baseStart_1598597 baseEnd_1598597 := by
    simpa [prefixWord, tailWord_1598597, baseEnd_1598597] using wordTrace_append hprefix tailTrace_1598597
  have hstable : (prefixWord ++ tailWord_1598597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598597).length < 2 ^ (prefixWord ++ tailWord_1598597).sum := by decide
  have hdescent : baseEnd_1598597 < baseStart_1598597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598636 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 7]
def baseStart_1598636 : Nat := 118140960795 + 1598636 * 2 ^ 59
def prefixEnd_1598636 : Nat := 4983230072969 + 3 ^ 40 * 1598636 * 2
def baseEnd_1598636 : Nat := 182415257684691680666225

theorem tailTrace_1598636 : CollatzResearch.WordTrace tailWord_1598636 prefixEnd_1598636 182415257684691680666225 := by
  unfold tailWord_1598636
  simp only [CollatzResearch.WordTrace]
  refine ⟨29153522518211136068627881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38871363357614848091503841 29153522518211136068627881)
  ·
    refine ⟨21865141888658352051470911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29153522518211136068627881 21865141888658352051470911)
    ·
      refine ⟨32797712832987528077206367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21865141888658352051470911 32797712832987528077206367)
      ·
        refine ⟨49196569249481292115809551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32797712832987528077206367 49196569249481292115809551)
        ·
          refine ⟨73794853874221938173714327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49196569249481292115809551 73794853874221938173714327)
          ·
            refine ⟨110692280811332907260571491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73794853874221938173714327 110692280811332907260571491)
            ·
              refine ⟨166038421216999360890857237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110692280811332907260571491 166038421216999360890857237)
              ·
                refine ⟨7783050994546845041758933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 166038421216999360890857237 7783050994546845041758933)
                ·
                  refine ⟨182415257684691680666225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7783050994546845041758933 182415257684691680666225)
                  ·
                    rfl

theorem cell22_1598636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_1598636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598636 prefixEnd_1598636 := by exact prefixLift 1598636
  have htrace : WordTrace (prefixWord ++ tailWord_1598636) baseStart_1598636 baseEnd_1598636 := by
    simpa [prefixWord, tailWord_1598636, baseEnd_1598636] using wordTrace_append hprefix tailTrace_1598636
  have hstable : (prefixWord ++ tailWord_1598636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598636).length < 2 ^ (prefixWord ++ tailWord_1598636).sum := by decide
  have hdescent : baseEnd_1598636 < baseStart_1598636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598646 : List Nat := [5, 1, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_1598646 : Nat := 118140960795 + 1598646 * 2 ^ 59
def prefixEnd_1598646 : Nat := 4983230072969 + 3 ^ 40 * 1598646 * 2
def baseEnd_1598646 : Nat := 547249196258438349248645

theorem tailTrace_1598646 : CollatzResearch.WordTrace tailWord_1598646 prefixEnd_1598646 547249196258438349248645 := by
  unfold tailWord_1598646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3644213110399127740319987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38871606510924029230079861 3644213110399127740319987)
  ·
    refine ⟨5466319665598691610479981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3644213110399127740319987 5466319665598691610479981)
    ·
      refine ⟨2049869874599509353929993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5466319665598691610479981 2049869874599509353929993)
      ·
        refine ⟨1537402405949632015447495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2049869874599509353929993 1537402405949632015447495)
        ·
          refine ⟨2306103608924448023171243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1537402405949632015447495 2306103608924448023171243)
          ·
            refine ⟨3459155413386672034756865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306103608924448023171243 3459155413386672034756865)
            ·
              refine ⟨2594366560040004026067649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3459155413386672034756865 2594366560040004026067649)
              ·
                refine ⟨1945774920030003019550737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2594366560040004026067649 1945774920030003019550737)
                ·
                  refine ⟨1459331190022502264663053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1945774920030003019550737 1459331190022502264663053)
                  ·
                    refine ⟨547249196258438349248645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1459331190022502264663053 547249196258438349248645)
                    ·
                      rfl

theorem cell22_1598646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_1598646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598646 prefixEnd_1598646 := by exact prefixLift 1598646
  have htrace : WordTrace (prefixWord ++ tailWord_1598646) baseStart_1598646 baseEnd_1598646 := by
    simpa [prefixWord, tailWord_1598646, baseEnd_1598646] using wordTrace_append hprefix tailTrace_1598646
  have hstable : (prefixWord ++ tailWord_1598646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598646).length < 2 ^ (prefixWord ++ tailWord_1598646).sum := by decide
  have hdescent : baseEnd_1598646 < baseStart_1598646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598653 : List Nat := [1, 4, 1, 2, 1, 1, 3, 4, 5]
def baseStart_1598653 : Nat := 118140960795 + 1598653 * 2 ^ 59
def prefixEnd_1598653 : Nat := 4983230072969 + 3 ^ 40 * 1598653 * 2
def baseEnd_1598653 : Nat := 182417197500497554774541

theorem tailTrace_1598653 : CollatzResearch.WordTrace tailWord_1598653 prefixEnd_1598653 182417197500497554774541 := by
  unfold tailWord_1598653
  simp only [CollatzResearch.WordTrace]
  refine ⟨58307665077360684040624613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38871776718240456027083075 58307665077360684040624613)
  ·
    refine ⟨10932687202005128257617115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58307665077360684040624613 10932687202005128257617115)
    ·
      refine ⟨16399030803007692386425673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10932687202005128257617115 16399030803007692386425673)
      ·
        refine ⟨12299273102255769289819255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16399030803007692386425673 12299273102255769289819255)
        ·
          refine ⟨18448909653383653934728883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12299273102255769289819255 18448909653383653934728883)
          ·
            refine ⟨27673364480075480902093325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18448909653383653934728883 27673364480075480902093325)
            ·
              refine ⟨10377511680028305338284997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27673364480075480902093325 10377511680028305338284997)
              ·
                refine ⟨1945783440005307250928437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10377511680028305338284997 1945783440005307250928437)
                ·
                  refine ⟨182417197500497554774541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1945783440005307250928437 182417197500497554774541)
                  ·
                    rfl

theorem cell22_1598653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_1598653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598653 prefixEnd_1598653 := by exact prefixLift 1598653
  have htrace : WordTrace (prefixWord ++ tailWord_1598653) baseStart_1598653 baseEnd_1598653 := by
    simpa [prefixWord, tailWord_1598653, baseEnd_1598653] using wordTrace_append hprefix tailTrace_1598653
  have hstable : (prefixWord ++ tailWord_1598653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598653).length < 2 ^ (prefixWord ++ tailWord_1598653).sum := by decide
  have hdescent : baseEnd_1598653 < baseStart_1598653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598700 : List Nat := [2, 2, 1, 1, 2, 5, 1, 3, 1, 4]
def baseStart_1598700 : Nat := 118140960795 + 1598700 * 2 ^ 59
def prefixEnd_1598700 : Nat := 4983230072969 + 3 ^ 40 * 1598700 * 2
def baseEnd_1598700 : Nat := 547267681562000208398479

theorem tailTrace_1598700 : CollatzResearch.WordTrace tailWord_1598700 prefixEnd_1598700 547267681562000208398479 := by
  unfold tailWord_1598700
  simp only [CollatzResearch.WordTrace]
  refine ⟨29154689654095205533792777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38872919538793607378390369 29154689654095205533792777)
  ·
    refine ⟨21866017240571404150344583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29154689654095205533792777 21866017240571404150344583)
    ·
      refine ⟨32799025860857106225516875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21866017240571404150344583 32799025860857106225516875)
      ·
        refine ⟨49198538791285659338275313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32799025860857106225516875 49198538791285659338275313)
        ·
          refine ⟨36898904093464244503706485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49198538791285659338275313 36898904093464244503706485)
          ·
            refine ⟨3459272258762272922222483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36898904093464244503706485 3459272258762272922222483)
            ·
              refine ⟨5188908388143409383333725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3459272258762272922222483 5188908388143409383333725)
              ·
                refine ⟨1945840645553778518750147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5188908388143409383333725 1945840645553778518750147)
                ·
                  refine ⟨2918760968330667778125221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1945840645553778518750147 2918760968330667778125221)
                  ·
                    refine ⟨547267681562000208398479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2918760968330667778125221 547267681562000208398479)
                    ·
                      rfl

theorem cell22_1598700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 4].length) (baseStart_1598700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598700 prefixEnd_1598700 := by exact prefixLift 1598700
  have htrace : WordTrace (prefixWord ++ tailWord_1598700) baseStart_1598700 baseEnd_1598700 := by
    simpa [prefixWord, tailWord_1598700, baseEnd_1598700] using wordTrace_append hprefix tailTrace_1598700
  have hstable : (prefixWord ++ tailWord_1598700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598700).length < 2 ^ (prefixWord ++ tailWord_1598700).sum := by decide
  have hdescent : baseEnd_1598700 < baseStart_1598700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598743 : List Nat := [1, 1, 3, 4, 1, 1, 3, 8]
def baseStart_1598743 : Nat := 118140960795 + 1598743 * 2 ^ 59
def prefixEnd_1598743 : Nat := 4983230072969 + 3 ^ 40 * 1598743 * 2
def baseEnd_1598743 : Nat := 60809155704529158841483

theorem tailTrace_1598743 : CollatzResearch.WordTrace tailWord_1598743 prefixEnd_1598743 60809155704529158841483 := by
  unfold tailWord_1598743
  simp only [CollatzResearch.WordTrace]
  refine ⟨58310947647034629411400883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38873965098023086274267255 58310947647034629411400883)
  ·
    refine ⟨87466421470551944117101325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58310947647034629411400883 87466421470551944117101325)
    ·
      refine ⟨32799908051456979043912997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87466421470551944117101325 32799908051456979043912997)
      ·
        refine ⟨6149982759648183570733687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32799908051456979043912997 6149982759648183570733687)
        ·
          refine ⟨9224974139472275356100531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6149982759648183570733687 9224974139472275356100531)
          ·
            refine ⟨13837461209208413034150797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9224974139472275356100531 13837461209208413034150797)
            ·
              refine ⟨5189047953453154887806549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13837461209208413034150797 5189047953453154887806549)
              ·
                refine ⟨60809155704529158841483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5189047953453154887806549 60809155704529158841483)
                ·
                  rfl

theorem cell22_1598743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 8].length) (baseStart_1598743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598743 prefixEnd_1598743 := by exact prefixLift 1598743
  have htrace : WordTrace (prefixWord ++ tailWord_1598743) baseStart_1598743 baseEnd_1598743 := by
    simpa [prefixWord, tailWord_1598743, baseEnd_1598743] using wordTrace_append hprefix tailTrace_1598743
  have hstable : (prefixWord ++ tailWord_1598743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598743).length < 2 ^ (prefixWord ++ tailWord_1598743).sum := by decide
  have hdescent : baseEnd_1598743 < baseStart_1598743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598749 : List Nat := [1, 4, 2, 3, 1, 3, 1, 3, 4]
def baseStart_1598749 : Nat := 118140960795 + 1598749 * 2 ^ 59
def prefixEnd_1598749 : Nat := 4983230072969 + 3 ^ 40 * 1598749 * 2
def baseEnd_1598749 : Nat := 182428151754460137974443

theorem tailTrace_1598749 : CollatzResearch.WordTrace tailWord_1598749 prefixEnd_1598749 182428151754460137974443 := by
  unfold tailWord_1598749
  simp only [CollatzResearch.WordTrace]
  refine ⟨58311166485012892436119301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38874110990008594957412867 58311166485012892436119301)
  ·
    refine ⟨10933343715939917331772369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58311166485012892436119301 10933343715939917331772369)
    ·
      refine ⟨8200007786954937998829277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10933343715939917331772369 8200007786954937998829277)
      ·
        refine ⟨3075002920108101749560979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8200007786954937998829277 3075002920108101749560979)
        ·
          refine ⟨4612504380162152624341469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3075002920108101749560979 4612504380162152624341469)
          ·
            refine ⟨1729689142560807234128051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4612504380162152624341469 1729689142560807234128051)
            ·
              refine ⟨2594533713841210851192077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1729689142560807234128051 2594533713841210851192077)
              ·
                refine ⟨972950142690454069197029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2594533713841210851192077 972950142690454069197029)
                ·
                  refine ⟨182428151754460137974443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 972950142690454069197029 182428151754460137974443)
                  ·
                    rfl

theorem cell22_1598749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_1598749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598749 prefixEnd_1598749 := by exact prefixLift 1598749
  have htrace : WordTrace (prefixWord ++ tailWord_1598749) baseStart_1598749 baseEnd_1598749 := by
    simpa [prefixWord, tailWord_1598749, baseEnd_1598749] using wordTrace_append hprefix tailTrace_1598749
  have hstable : (prefixWord ++ tailWord_1598749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598749).length < 2 ^ (prefixWord ++ tailWord_1598749).sum := by decide
  have hdescent : baseEnd_1598749 < baseStart_1598749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598760 : List Nat := [2, 1, 5, 1, 2, 3, 8]
def baseStart_1598760 : Nat := 118140960795 + 1598760 * 2 ^ 59
def prefixEnd_1598760 : Nat := 4983230072969 + 3 ^ 40 * 1598760 * 2
def baseEnd_1598760 : Nat := 20269934103265927848085

theorem tailTrace_1598760 : CollatzResearch.WordTrace tailWord_1598760 prefixEnd_1598760 20269934103265927848085 := by
  unfold tailWord_1598760
  simp only [CollatzResearch.WordTrace]
  refine ⟨29155783843986520657384867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38874378458648694209846489 29155783843986520657384867)
  ·
    refine ⟨43733675765979780986077301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29155783843986520657384867 43733675765979780986077301)
    ·
      refine ⟨4100032103060604467444747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43733675765979780986077301 4100032103060604467444747)
      ·
        refine ⟨6150048154590906701167121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4100032103060604467444747 6150048154590906701167121)
        ·
          refine ⟨4612536115943180025875341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6150048154590906701167121 4612536115943180025875341)
          ·
            refine ⟨1729701043478692509703253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4612536115943180025875341 1729701043478692509703253)
            ·
              refine ⟨20269934103265927848085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1729701043478692509703253 20269934103265927848085)
              ·
                rfl

theorem cell22_1598760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 8].length) (baseStart_1598760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598760 prefixEnd_1598760 := by exact prefixLift 1598760
  have htrace : WordTrace (prefixWord ++ tailWord_1598760) baseStart_1598760 baseEnd_1598760 := by
    simpa [prefixWord, tailWord_1598760, baseEnd_1598760] using wordTrace_append hprefix tailTrace_1598760
  have hstable : (prefixWord ++ tailWord_1598760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598760).length < 2 ^ (prefixWord ++ tailWord_1598760).sum := by decide
  have hdescent : baseEnd_1598760 < baseStart_1598760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598762 : List Nat := [3, 1, 4, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1598762 : Nat := 118140960795 + 1598762 * 2 ^ 59
def prefixEnd_1598762 : Nat := 4983230072969 + 3 ^ 40 * 1598762 * 2
def baseEnd_1598762 : Nat := 547288905429052713348289

theorem tailTrace_1598762 : CollatzResearch.WordTrace tailWord_1598762 prefixEnd_1598762 547288905429052713348289 := by
  unfold tailWord_1598762
  simp only [CollatzResearch.WordTrace]
  refine ⟨14577910158491448914085635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38874427089310530437561693 14577910158491448914085635)
  ·
    refine ⟨21866865237737173371128453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14577910158491448914085635 21866865237737173371128453)
    ·
      refine ⟨4100037232075720007086585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21866865237737173371128453 4100037232075720007086585)
      ·
        refine ⟨3075027924056790005314939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4100037232075720007086585 3075027924056790005314939)
        ·
          refine ⟨4612541886085185007972409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3075027924056790005314939 4612541886085185007972409)
          ·
            refine ⟨3459406414563888755979307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4612541886085185007972409 3459406414563888755979307)
            ·
              refine ⟨5189109621845833133968961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3459406414563888755979307 5189109621845833133968961)
              ·
                refine ⟨3891832216384374850476721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5189109621845833133968961 3891832216384374850476721)
                ·
                  refine ⟨2918874162288281137857541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3891832216384374850476721 2918874162288281137857541)
                  ·
                    refine ⟨547288905429052713348289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2918874162288281137857541 547288905429052713348289)
                    ·
                      rfl

theorem cell22_1598762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1598762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598762 prefixEnd_1598762 := by exact prefixLift 1598762
  have htrace : WordTrace (prefixWord ++ tailWord_1598762) baseStart_1598762 baseEnd_1598762 := by
    simpa [prefixWord, tailWord_1598762, baseEnd_1598762] using wordTrace_append hprefix tailTrace_1598762
  have hstable : (prefixWord ++ tailWord_1598762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598762).length < 2 ^ (prefixWord ++ tailWord_1598762).sum := by decide
  have hdescent : baseEnd_1598762 < baseStart_1598762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598826 : List Nat := [3, 1, 3, 3, 2, 1, 1, 4, 1, 3]
def baseStart_1598826 : Nat := 118140960795 + 1598826 * 2 ^ 59
def prefixEnd_1598826 : Nat := 4983230072969 + 3 ^ 40 * 1598826 * 2
def baseEnd_1598826 : Nat := 547310813936977879748093

theorem tailTrace_1598826 : CollatzResearch.WordTrace tailWord_1598826 prefixEnd_1598826 547310813936977879748093 := by
  unfold tailWord_1598826
  simp only [CollatzResearch.WordTrace]
  refine ⟨14578493726433483646668083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38875983270489289724448221 14578493726433483646668083)
  ·
    refine ⟨21867740589650225470002125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14578493726433483646668083 21867740589650225470002125)
    ·
      refine ⟨8200402721118834551250797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21867740589650225470002125 8200402721118834551250797)
      ·
        refine ⟨3075151020419562956719049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8200402721118834551250797 3075151020419562956719049)
        ·
          refine ⟨2306363265314672217539287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3075151020419562956719049 2306363265314672217539287)
          ·
            refine ⟨3459544897972008326308931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306363265314672217539287 3459544897972008326308931)
            ·
              refine ⟨5189317346958012489463397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3459544897972008326308931 5189317346958012489463397)
              ·
                refine ⟨972997002554627341774387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5189317346958012489463397 972997002554627341774387)
                ·
                  refine ⟨1459495503831941012661581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 972997002554627341774387 1459495503831941012661581)
                  ·
                    refine ⟨547310813936977879748093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1459495503831941012661581 547310813936977879748093)
                    ·
                      rfl

theorem cell22_1598826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_1598826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598826 prefixEnd_1598826 := by exact prefixLift 1598826
  have htrace : WordTrace (prefixWord ++ tailWord_1598826) baseStart_1598826 baseEnd_1598826 := by
    simpa [prefixWord, tailWord_1598826, baseEnd_1598826] using wordTrace_append hprefix tailTrace_1598826
  have hstable : (prefixWord ++ tailWord_1598826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598826).length < 2 ^ (prefixWord ++ tailWord_1598826).sum := by decide
  have hdescent : baseEnd_1598826 < baseStart_1598826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598837 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1598837 : Nat := 118140960795 + 1598837 * 2 ^ 59
def prefixEnd_1598837 : Nat := 4983230072969 + 3 ^ 40 * 1598837 * 2
def baseEnd_1598837 : Nat := 547314579461777517723059

theorem tailTrace_1598837 : CollatzResearch.WordTrace tailWord_1598837 prefixEnd_1598837 547314579461777517723059 := by
  unfold tailWord_1598837
  simp only [CollatzResearch.WordTrace]
  refine ⟨58314376108694083465322765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38876250739129388976881843 58314376108694083465322765)
  ·
    refine ⟨21867891040760281299496037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58314376108694083465322765 21867891040760281299496037)
    ·
      refine ⟨4100229570142552743655507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21867891040760281299496037 4100229570142552743655507)
      ·
        refine ⟨6150344355213829115483261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4100229570142552743655507 6150344355213829115483261)
        ·
          refine ⟨2306379133205185918306223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6150344355213829115483261 2306379133205185918306223)
          ·
            refine ⟨3459568699807778877459335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306379133205185918306223 3459568699807778877459335)
            ·
              refine ⟨5189353049711668316189003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3459568699807778877459335 5189353049711668316189003)
              ·
                refine ⟨7784029574567502474283505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5189353049711668316189003 7784029574567502474283505)
                ·
                  refine ⟨5838022180925626855712629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7784029574567502474283505 5838022180925626855712629)
                  ·
                    refine ⟨547314579461777517723059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5838022180925626855712629 547314579461777517723059)
                    ·
                      rfl

theorem cell22_1598837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1598837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598837 prefixEnd_1598837 := by exact prefixLift 1598837
  have htrace : WordTrace (prefixWord ++ tailWord_1598837) baseStart_1598837 baseEnd_1598837 := by
    simpa [prefixWord, tailWord_1598837, baseEnd_1598837] using wordTrace_append hprefix tailTrace_1598837
  have hstable : (prefixWord ++ tailWord_1598837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598837).length < 2 ^ (prefixWord ++ tailWord_1598837).sum := by decide
  have hdescent : baseEnd_1598837 < baseStart_1598837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598865 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 6, 3]
def baseStart_1598865 : Nat := 118140960795 + 1598865 * 2 ^ 59
def prefixEnd_1598865 : Nat := 4983230072969 + 3 ^ 40 * 1598865 * 2
def baseEnd_1598865 : Nat := 547324164433994778022973

theorem tailTrace_1598865 : CollatzResearch.WordTrace tailWord_1598865 prefixEnd_1598865 547324164433994778022973 := by
  unfold tailWord_1598865
  simp only [CollatzResearch.WordTrace]
  refine ⟨58315397352592644247342049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38876931568395096164894699 58315397352592644247342049)
  ·
    refine ⟨43736548014444483185506537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58315397352592644247342049 43736548014444483185506537)
    ·
      refine ⟨32802411010833362389129903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43736548014444483185506537 32802411010833362389129903)
      ·
        refine ⟨49203616516250043583694855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32802411010833362389129903 49203616516250043583694855)
        ·
          refine ⟨73805424774375065375542283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49203616516250043583694855 73805424774375065375542283)
          ·
            refine ⟨110708137161562598063313425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73805424774375065375542283 110708137161562598063313425)
            ·
              refine ⟨83031102871171948547485069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110708137161562598063313425 83031102871171948547485069)
              ·
                refine ⟨31136663576689480705306901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83031102871171948547485069 31136663576689480705306901)
                ·
                  refine ⟨1459531105157319408061261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31136663576689480705306901 1459531105157319408061261)
                  ·
                    refine ⟨547324164433994778022973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1459531105157319408061261 547324164433994778022973)
                    ·
                      rfl

theorem cell22_1598865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_1598865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598865 prefixEnd_1598865 := by exact prefixLift 1598865
  have htrace : WordTrace (prefixWord ++ tailWord_1598865) baseStart_1598865 baseEnd_1598865 := by
    simpa [prefixWord, tailWord_1598865, baseEnd_1598865] using wordTrace_append hprefix tailTrace_1598865
  have hstable : (prefixWord ++ tailWord_1598865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598865).length < 2 ^ (prefixWord ++ tailWord_1598865).sum := by decide
  have hdescent : baseEnd_1598865 < baseStart_1598865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598880 : List Nat := [2, 1, 1, 4, 1, 2, 2, 1, 4, 4]
def baseStart_1598880 : Nat := 118140960795 + 1598880 * 2 ^ 59
def prefixEnd_1598880 : Nat := 4983230072969 + 3 ^ 40 * 1598880 * 2
def baseEnd_1598880 : Nat := 547329299240539738897927

theorem tailTrace_1598880 : CollatzResearch.WordTrace tailWord_1598880 prefixEnd_1598880 547329299240539738897927 := by
  unfold tailWord_1598880
  simp only [CollatzResearch.WordTrace]
  refine ⟨29157972223769150904569047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38877296298358867872758729 29157972223769150904569047)
  ·
    refine ⟨43736958335653726356853571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29157972223769150904569047 43736958335653726356853571)
    ·
      refine ⟨65605437503480589535280357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43736958335653726356853571 65605437503480589535280357)
      ·
        refine ⟨12301019531902610537865067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65605437503480589535280357 12301019531902610537865067)
        ·
          refine ⟨18451529297853915806797601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12301019531902610537865067 18451529297853915806797601)
          ·
            refine ⟨13838646973390436855098201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18451529297853915806797601 13838646973390436855098201)
            ·
              refine ⟨10378985230042827641323651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13838646973390436855098201 10378985230042827641323651)
              ·
                refine ⟨15568477845064241461985477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10378985230042827641323651 15568477845064241461985477)
                ·
                  refine ⟨2919089595949545274122277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15568477845064241461985477 2919089595949545274122277)
                  ·
                    refine ⟨547329299240539738897927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2919089595949545274122277 547329299240539738897927)
                    ·
                      rfl

theorem cell22_1598880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_1598880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598880 prefixEnd_1598880 := by exact prefixLift 1598880
  have htrace : WordTrace (prefixWord ++ tailWord_1598880) baseStart_1598880 baseEnd_1598880 := by
    simpa [prefixWord, tailWord_1598880, baseEnd_1598880] using wordTrace_append hprefix tailTrace_1598880
  have hstable : (prefixWord ++ tailWord_1598880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598880).length < 2 ^ (prefixWord ++ tailWord_1598880).sum := by decide
  have hdescent : baseEnd_1598880 < baseStart_1598880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1598910 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_1598910 : Nat := 118140960795 + 1598910 * 2 ^ 59
def prefixEnd_1598910 : Nat := 4983230072969 + 3 ^ 40 * 1598910 * 2
def baseEnd_1598910 : Nat := 547339568853629660647835

theorem tailTrace_1598910 : CollatzResearch.WordTrace tailWord_1598910 prefixEnd_1598910 547339568853629660647835 := by
  unfold tailWord_1598910
  simp only [CollatzResearch.WordTrace]
  refine ⟨7289629829678702116591273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38878025758286411288486789 7289629829678702116591273)
  ·
    refine ⟨5467222372259026587443455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7289629829678702116591273 5467222372259026587443455)
    ·
      refine ⟨8200833558388539881165183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5467222372259026587443455 8200833558388539881165183)
      ·
        refine ⟨12301250337582809821747775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8200833558388539881165183 12301250337582809821747775)
        ·
          refine ⟨18451875506374214732621663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12301250337582809821747775 18451875506374214732621663)
          ·
            refine ⟨27677813259561322098932495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18451875506374214732621663 27677813259561322098932495)
            ·
              refine ⟨41516719889341983148398743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27677813259561322098932495 41516719889341983148398743)
              ·
                refine ⟨62275079834012974722598115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41516719889341983148398743 62275079834012974722598115)
                ·
                  refine ⟨93412619751019462083897173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62275079834012974722598115 93412619751019462083897173)
                  ·
                    refine ⟨547339568853629660647835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 93412619751019462083897173 547339568853629660647835)
                    ·
                      rfl

theorem cell22_1598910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_1598910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1598910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1598910 prefixEnd_1598910 := by exact prefixLift 1598910
  have htrace : WordTrace (prefixWord ++ tailWord_1598910) baseStart_1598910 baseEnd_1598910 := by
    simpa [prefixWord, tailWord_1598910, baseEnd_1598910] using wordTrace_append hprefix tailTrace_1598910
  have hstable : (prefixWord ++ tailWord_1598910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1598910).length < 2 ^ (prefixWord ++ tailWord_1598910).sum := by decide
  have hdescent : baseEnd_1598910 < baseStart_1598910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1598910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599032 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 1, 6]
def baseStart_1599032 : Nat := 118140960795 + 1599032 * 2 ^ 59
def prefixEnd_1599032 : Nat := 4983230072969 + 3 ^ 40 * 1599032 * 2
def baseEnd_1599032 : Nat := 547381331946862009097461

theorem tailTrace_1599032 : CollatzResearch.WordTrace tailWord_1599032 prefixEnd_1599032 547381331946862009097461 := by
  unfold tailWord_1599032
  simp only [CollatzResearch.WordTrace]
  refine ⟨29160744171493815884335675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38880992228658421179114233 29160744171493815884335675)
  ·
    refine ⟨43741116257240723826503513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29160744171493815884335675 43741116257240723826503513)
    ·
      refine ⟨32805837192930542869877635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43741116257240723826503513 32805837192930542869877635)
      ·
        refine ⟨49208755789395814304816453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32805837192930542869877635 49208755789395814304816453)
        ·
          refine ⟨9226641710511715182153085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49208755789395814304816453 9226641710511715182153085)
          ·
            refine ⟨3459990641441893193307407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9226641710511715182153085 3459990641441893193307407)
            ·
              refine ⟨5189985962162839789961111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3459990641441893193307407 5189985962162839789961111)
              ·
                refine ⟨7784978943244259684941667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5189985962162839789961111 7784978943244259684941667)
                ·
                  refine ⟨11677468414866389527412501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7784978943244259684941667 11677468414866389527412501)
                  ·
                    refine ⟨547381331946862009097461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11677468414866389527412501 547381331946862009097461)
                    ·
                      rfl

theorem cell22_1599032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_1599032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599032 prefixEnd_1599032 := by exact prefixLift 1599032
  have htrace : WordTrace (prefixWord ++ tailWord_1599032) baseStart_1599032 baseEnd_1599032 := by
    simpa [prefixWord, tailWord_1599032, baseEnd_1599032] using wordTrace_append hprefix tailTrace_1599032
  have hstable : (prefixWord ++ tailWord_1599032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599032).length < 2 ^ (prefixWord ++ tailWord_1599032).sum := by decide
  have hdescent : baseEnd_1599032 < baseStart_1599032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599036 : List Nat := [2, 2, 2, 2, 4, 1, 2, 3, 4]
def baseStart_1599036 : Nat := 118140960795 + 1599036 * 2 ^ 59
def prefixEnd_1599036 : Nat := 4983230072969 + 3 ^ 40 * 1599036 * 2
def baseEnd_1599036 : Nat := 182460900409535777332483

theorem tailTrace_1599036 : CollatzResearch.WordTrace tailWord_1599036 prefixEnd_1599036 182460900409535777332483 := by
  unfold tailWord_1599036
  simp only [CollatzResearch.WordTrace]
  refine ⟨29160817117486570225908481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38881089489982093634544641 29160817117486570225908481)
  ·
    refine ⟨21870612838114927669431361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29160817117486570225908481 21870612838114927669431361)
    ·
      refine ⟨16402959628586195752073521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21870612838114927669431361 16402959628586195752073521)
      ·
        refine ⟨12302219721439646814055141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16402959628586195752073521 12302219721439646814055141)
        ·
          refine ⟨2306666197769933777635339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12302219721439646814055141 2306666197769933777635339)
          ·
            refine ⟨3459999296654900666453009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306666197769933777635339 3459999296654900666453009)
            ·
              refine ⟨2594999472491175499839757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3459999296654900666453009 2594999472491175499839757)
              ·
                refine ⟨973124802184190812439909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2594999472491175499839757 973124802184190812439909)
                ·
                  refine ⟨182460900409535777332483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 973124802184190812439909 182460900409535777332483)
                  ·
                    rfl

theorem cell22_1599036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_1599036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599036 prefixEnd_1599036 := by exact prefixLift 1599036
  have htrace : WordTrace (prefixWord ++ tailWord_1599036) baseStart_1599036 baseEnd_1599036 := by
    simpa [prefixWord, tailWord_1599036, baseEnd_1599036] using wordTrace_append hprefix tailTrace_1599036
  have hstable : (prefixWord ++ tailWord_1599036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599036).length < 2 ^ (prefixWord ++ tailWord_1599036).sum := by decide
  have hdescent : baseEnd_1599036 < baseStart_1599036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599047 : List Nat := [1, 1, 4, 1, 5, 1, 9]
def baseStart_1599047 : Nat := 118140960795 + 1599047 * 2 ^ 59
def prefixEnd_1599047 : Nat := 4983230072969 + 3 ^ 40 * 1599047 * 2
def baseEnd_1599047 : Nat := 20273572842718776665645

theorem tailTrace_1599047 : CollatzResearch.WordTrace tailWord_1599047 prefixEnd_1599047 20273572842718776665645 := by
  unfold tailWord_1599047
  simp only [CollatzResearch.WordTrace]
  refine ⟨58322035437933289330467395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38881356958622192886978263 58322035437933289330467395)
  ·
    refine ⟨87483053156899933995701093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58322035437933289330467395 87483053156899933995701093)
    ·
      refine ⟨16403072466918737624193955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87483053156899933995701093 16403072466918737624193955)
      ·
        refine ⟨24604608700378106436290933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16403072466918737624193955 24604608700378106436290933)
        ·
          refine ⟨2306682065660447478402275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24604608700378106436290933 2306682065660447478402275)
          ·
            refine ⟨3460023098490671217603413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2306682065660447478402275 3460023098490671217603413)
            ·
              refine ⟨20273572842718776665645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3460023098490671217603413 20273572842718776665645)
              ·
                rfl

theorem cell22_1599047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 9].length) (baseStart_1599047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599047 prefixEnd_1599047 := by exact prefixLift 1599047
  have htrace : WordTrace (prefixWord ++ tailWord_1599047) baseStart_1599047 baseEnd_1599047 := by
    simpa [prefixWord, tailWord_1599047, baseEnd_1599047] using wordTrace_append hprefix tailTrace_1599047
  have hstable : (prefixWord ++ tailWord_1599047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599047).length < 2 ^ (prefixWord ++ tailWord_1599047).sum := by decide
  have hdescent : baseEnd_1599047 < baseStart_1599047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599068 : List Nat := [2, 2, 4, 1, 2, 2, 3, 1, 2, 3]
def baseStart_1599068 : Nat := 118140960795 + 1599068 * 2 ^ 59
def prefixEnd_1599068 : Nat := 4983230072969 + 3 ^ 40 * 1599068 * 2
def baseEnd_1599068 : Nat := 547393655482569915197351

theorem tailTrace_1599068 : CollatzResearch.WordTrace tailWord_1599068 prefixEnd_1599068 547393655482569915197351 := by
  unfold tailWord_1599068
  simp only [CollatzResearch.WordTrace]
  refine ⟨29161400685428604958490929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38881867580571473277987905 29161400685428604958490929)
  ·
    refine ⟨21871050514071453718868197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29161400685428604958490929 21871050514071453718868197)
    ·
      refine ⟨4100821971388397572287787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21871050514071453718868197 4100821971388397572287787)
      ·
        refine ⟨6151232957082596358431681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4100821971388397572287787 6151232957082596358431681)
        ·
          refine ⟨4613424717811947268823761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6151232957082596358431681 4613424717811947268823761)
          ·
            refine ⟨3460068538358960451617821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4613424717811947268823761 3460068538358960451617821)
            ·
              refine ⟨1297525701884610169356683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3460068538358960451617821 1297525701884610169356683)
              ·
                refine ⟨1946288552826915254035025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1297525701884610169356683 1946288552826915254035025)
                ·
                  refine ⟨1459716414620186440526269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1946288552826915254035025 1459716414620186440526269)
                  ·
                    refine ⟨547393655482569915197351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1459716414620186440526269 547393655482569915197351)
                    ·
                      rfl

theorem cell22_1599068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_1599068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599068 prefixEnd_1599068 := by exact prefixLift 1599068
  have htrace : WordTrace (prefixWord ++ tailWord_1599068) baseStart_1599068 baseEnd_1599068 := by
    simpa [prefixWord, tailWord_1599068, baseEnd_1599068] using wordTrace_append hprefix tailTrace_1599068
  have hstable : (prefixWord ++ tailWord_1599068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599068).length < 2 ^ (prefixWord ++ tailWord_1599068).sum := by decide
  have hdescent : baseEnd_1599068 < baseStart_1599068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599079 : List Nat := [1, 1, 5, 1, 1, 1, 4, 2, 3, 3]
def baseStart_1599079 : Nat := 118140960795 + 1599079 * 2 ^ 59
def prefixEnd_1599079 : Nat := 4983230072969 + 3 ^ 40 * 1599079 * 2
def baseEnd_1599079 : Nat := 547397421007369553172317

theorem tailTrace_1599079 : CollatzResearch.WordTrace tailWord_1599079 prefixEnd_1599079 547397421007369553172317 := by
  unfold tailWord_1599079
  simp only [CollatzResearch.WordTrace]
  refine ⟨58323202573817358795632291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38882135049211572530421527 58323202573817358795632291)
  ·
    refine ⟨87484803860726038193448437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58323202573817358795632291 87484803860726038193448437)
    ·
      refine ⟨8201700361943066080635791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87484803860726038193448437 8201700361943066080635791)
      ·
        refine ⟨12302550542914599120953687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8201700361943066080635791 12302550542914599120953687)
        ·
          refine ⟨18453825814371898681430531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12302550542914599120953687 18453825814371898681430531)
          ·
            refine ⟨27680738721557848022145797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18453825814371898681430531 27680738721557848022145797)
            ·
              refine ⟨5190138510292096504152337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27680738721557848022145797 5190138510292096504152337)
              ·
                refine ⟨3892603882719072378114253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5190138510292096504152337 3892603882719072378114253)
                ·
                  refine ⟨1459726456019652141792845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3892603882719072378114253 1459726456019652141792845)
                  ·
                    refine ⟨547397421007369553172317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1459726456019652141792845 547397421007369553172317)
                    ·
                      rfl

theorem cell22_1599079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_1599079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599079 prefixEnd_1599079 := by exact prefixLift 1599079
  have htrace : WordTrace (prefixWord ++ tailWord_1599079) baseStart_1599079 baseEnd_1599079 := by
    simpa [prefixWord, tailWord_1599079, baseEnd_1599079] using wordTrace_append hprefix tailTrace_1599079
  have hstable : (prefixWord ++ tailWord_1599079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599079).length < 2 ^ (prefixWord ++ tailWord_1599079).sum := by decide
  have hdescent : baseEnd_1599079 < baseStart_1599079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599152 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 3, 5]
def baseStart_1599152 : Nat := 118140960795 + 1599152 * 2 ^ 59
def prefixEnd_1599152 : Nat := 4983230072969 + 3 ^ 40 * 1599152 * 2
def baseEnd_1599152 : Nat := 547422410399221696097093

theorem tailTrace_1599152 : CollatzResearch.WordTrace tailWord_1599152 prefixEnd_1599152 547422410399221696097093 := by
  unfold tailWord_1599152
  simp only [CollatzResearch.WordTrace]
  refine ⟨29162932551276446131519855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38883910068368594842026473 29162932551276446131519855)
  ·
    refine ⟨43744398826914669197279783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29162932551276446131519855 43744398826914669197279783)
    ·
      refine ⟨65616598240372003795919675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43744398826914669197279783 65616598240372003795919675)
      ·
        refine ⟨98424897360558005693879513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65616598240372003795919675 98424897360558005693879513)
        ·
          refine ⟨73818673020418504270409635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98424897360558005693879513 73818673020418504270409635)
          ·
            refine ⟨110728009530627756405614453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73818673020418504270409635 110728009530627756405614453)
            ·
              refine ⟨10380750893496352163026355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 110728009530627756405614453 10380750893496352163026355)
              ·
                refine ⟨15571126340244528244539533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10380750893496352163026355 15571126340244528244539533)
                ·
                  refine ⟨5839172377591698091702325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15571126340244528244539533 5839172377591698091702325)
                  ·
                    refine ⟨547422410399221696097093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5839172377591698091702325 547422410399221696097093)
                    ·
                      rfl

theorem cell22_1599152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_1599152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599152 prefixEnd_1599152 := by exact prefixLift 1599152
  have htrace : WordTrace (prefixWord ++ tailWord_1599152) baseStart_1599152 baseEnd_1599152 := by
    simpa [prefixWord, tailWord_1599152, baseEnd_1599152] using wordTrace_append hprefix tailTrace_1599152
  have hstable : (prefixWord ++ tailWord_1599152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599152).length < 2 ^ (prefixWord ++ tailWord_1599152).sum := by decide
  have hdescent : baseEnd_1599152 < baseStart_1599152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599186 : List Nat := [3, 2, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_1599186 : Nat := 118140960795 + 1599186 * 2 ^ 59
def prefixEnd_1599186 : Nat := 4983230072969 + 3 ^ 40 * 1599186 * 2
def baseEnd_1599186 : Nat := 547434049294056940746989

theorem tailTrace_1599186 : CollatzResearch.WordTrace tailWord_1599186 prefixEnd_1599186 547434049294056940746989 := by
  unfold tailWord_1599186
  simp only [CollatzResearch.WordTrace]
  refine ⟨14581776296107429017444353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38884736789619810713184941 14581776296107429017444353)
  ·
    refine ⟨10936332222080571763083265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14581776296107429017444353 10936332222080571763083265)
    ·
      refine ⟨8202249166560428822312449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10936332222080571763083265 8202249166560428822312449)
      ·
        refine ⟨6151686874920321616734337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8202249166560428822312449 6151686874920321616734337)
        ·
          refine ⟨4613765156190241212550753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6151686874920321616734337 4613765156190241212550753)
          ·
            refine ⟨3460323867142680909413065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4613765156190241212550753 3460323867142680909413065)
            ·
              refine ⟨2595242900357010682059799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3460323867142680909413065 2595242900357010682059799)
              ·
                refine ⟨3892864350535516023089699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2595242900357010682059799 3892864350535516023089699)
                ·
                  refine ⟨5839296525803274034634549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3892864350535516023089699 5839296525803274034634549)
                  ·
                    refine ⟨547434049294056940746989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5839296525803274034634549 547434049294056940746989)
                    ·
                      rfl

theorem cell22_1599186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_1599186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599186 prefixEnd_1599186 := by exact prefixLift 1599186
  have htrace : WordTrace (prefixWord ++ tailWord_1599186) baseStart_1599186 baseEnd_1599186 := by
    simpa [prefixWord, tailWord_1599186, baseEnd_1599186] using wordTrace_append hprefix tailTrace_1599186
  have hstable : (prefixWord ++ tailWord_1599186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599186).length < 2 ^ (prefixWord ++ tailWord_1599186).sum := by decide
  have hdescent : baseEnd_1599186 < baseStart_1599186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599199 : List Nat := [1, 1, 2, 3, 2, 2, 5, 6]
def baseStart_1599199 : Nat := 118140960795 + 1599199 * 2 ^ 59
def prefixEnd_1599199 : Nat := 4983230072969 + 3 ^ 40 * 1599199 * 2
def baseEnd_1599199 : Nat := 60826499939969915574661

theorem tailTrace_1599199 : CollatzResearch.WordTrace tailWord_1599199 prefixEnd_1599199 60826499939969915574661 := by
  unfold tailWord_1599199
  simp only [CollatzResearch.WordTrace]
  refine ⟨58327579333382619290000651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38885052888921746193333767 58327579333382619290000651)
  ·
    refine ⟨87491369000073928935000977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58327579333382619290000651 87491369000073928935000977)
    ·
      refine ⟨65618526750055446701250733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87491369000073928935000977 65618526750055446701250733)
      ·
        refine ⟨24606947531270792512969025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65618526750055446701250733 24606947531270792512969025)
        ·
          refine ⟨18455210648453094384726769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24606947531270792512969025 18455210648453094384726769)
          ·
            refine ⟨13841407986339820788545077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18455210648453094384726769 13841407986339820788545077)
            ·
              refine ⟨1297631998719358198926101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13841407986339820788545077 1297631998719358198926101)
              ·
                refine ⟨60826499939969915574661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1297631998719358198926101 60826499939969915574661)
                ·
                  rfl

theorem cell22_1599199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 6].length) (baseStart_1599199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599199 prefixEnd_1599199 := by exact prefixLift 1599199
  have htrace : WordTrace (prefixWord ++ tailWord_1599199) baseStart_1599199 baseEnd_1599199 := by
    simpa [prefixWord, tailWord_1599199, baseEnd_1599199] using wordTrace_append hprefix tailTrace_1599199
  have hstable : (prefixWord ++ tailWord_1599199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599199).length < 2 ^ (prefixWord ++ tailWord_1599199).sum := by decide
  have hdescent : baseEnd_1599199 < baseStart_1599199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599207 : List Nat := [1, 1, 5, 4, 2, 1, 2, 1, 1, 4]
def baseStart_1599207 : Nat := 118140960795 + 1599207 * 2 ^ 59
def prefixEnd_1599207 : Nat := 4983230072969 + 3 ^ 40 * 1599207 * 2
def baseEnd_1599207 : Nat := 547441238023219885971925

theorem tailTrace_1599207 : CollatzResearch.WordTrace tailWord_1599207 prefixEnd_1599207 547441238023219885971925 := by
  unfold tailWord_1599207
  simp only [CollatzResearch.WordTrace]
  refine ⟨58327871117353636656291875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38885247411569091104194583 58327871117353636656291875)
  ·
    refine ⟨87491806676030454984437813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58327871117353636656291875 87491806676030454984437813)
    ·
      refine ⟨8202356875877855154791045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87491806676030454984437813 8202356875877855154791045)
      ·
        refine ⟨1537941914227097841523321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8202356875877855154791045 1537941914227097841523321)
        ·
          refine ⟨1153456435670323381142491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1537941914227097841523321 1153456435670323381142491)
          ·
            refine ⟨1730184653505485071713737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153456435670323381142491 1730184653505485071713737)
            ·
              refine ⟨1297638490129113803785303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1730184653505485071713737 1297638490129113803785303)
              ·
                refine ⟨1946457735193670705677955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1297638490129113803785303 1946457735193670705677955)
                ·
                  refine ⟨2919686602790506058516933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1946457735193670705677955 2919686602790506058516933)
                  ·
                    refine ⟨547441238023219885971925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2919686602790506058516933 547441238023219885971925)
                    ·
                      rfl

theorem cell22_1599207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_1599207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599207 prefixEnd_1599207 := by exact prefixLift 1599207
  have htrace : WordTrace (prefixWord ++ tailWord_1599207) baseStart_1599207 baseEnd_1599207 := by
    simpa [prefixWord, tailWord_1599207, baseEnd_1599207] using wordTrace_append hprefix tailTrace_1599207
  have hstable : (prefixWord ++ tailWord_1599207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599207).length < 2 ^ (prefixWord ++ tailWord_1599207).sum := by decide
  have hdescent : baseEnd_1599207 < baseStart_1599207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599220 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_1599220 : Nat := 118140960795 + 1599220 * 2 ^ 59
def prefixEnd_1599220 : Nat := 4983230072969 + 3 ^ 40 * 1599220 * 2
def baseEnd_1599220 : Nat := 547445688188892185396885

theorem tailTrace_1599220 : CollatzResearch.WordTrace tailWord_1599220 prefixEnd_1599220 547445688188892185396885 := by
  unfold tailWord_1599220
  simp only [CollatzResearch.WordTrace]
  refine ⟨29164172633153269938257557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38885563510871026584343409 29164172633153269938257557)
  ·
    refine ⟨1367070592179059528355823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29164172633153269938257557 1367070592179059528355823)
    ·
      refine ⟨2050605888268589292533735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1367070592179059528355823 2050605888268589292533735)
      ·
        refine ⟨3075908832402883938800603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2050605888268589292533735 3075908832402883938800603)
        ·
          refine ⟨4613863248604325908200905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3075908832402883938800603 4613863248604325908200905)
          ·
            refine ⟨3460397436453244431150679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4613863248604325908200905 3460397436453244431150679)
            ·
              refine ⟨5190596154679866646726019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3460397436453244431150679 5190596154679866646726019)
              ·
                refine ⟨7785894232019799970089029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5190596154679866646726019 7785894232019799970089029)
                ·
                  refine ⟨1459855168503712494391693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7785894232019799970089029 1459855168503712494391693)
                  ·
                    refine ⟨547445688188892185396885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1459855168503712494391693 547445688188892185396885)
                    ·
                      rfl

theorem cell22_1599220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_1599220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599220 prefixEnd_1599220 := by exact prefixLift 1599220
  have htrace : WordTrace (prefixWord ++ tailWord_1599220) baseStart_1599220 baseEnd_1599220 := by
    simpa [prefixWord, tailWord_1599220, baseEnd_1599220] using wordTrace_append hprefix tailTrace_1599220
  have hstable : (prefixWord ++ tailWord_1599220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599220).length < 2 ^ (prefixWord ++ tailWord_1599220).sum := by decide
  have hdescent : baseEnd_1599220 < baseStart_1599220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599244 : List Nat := [2, 2, 1, 2, 2, 1, 2, 5, 5]
def baseStart_1599244 : Nat := 118140960795 + 1599244 * 2 ^ 59
def prefixEnd_1599244 : Nat := 4983230072969 + 3 ^ 40 * 1599244 * 2
def baseEnd_1599244 : Nat := 182484634626454707598937

theorem tailTrace_1599244 : CollatzResearch.WordTrace tailWord_1599244 prefixEnd_1599244 182484634626454707598937 := by
  unfold tailWord_1599244
  simp only [CollatzResearch.WordTrace]
  refine ⟨29164610309109795987694393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38886147078813061316925857 29164610309109795987694393)
  ·
    refine ⟨21873457731832346990770795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29164610309109795987694393 21873457731832346990770795)
    ·
      refine ⟨32810186597748520486156193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21873457731832346990770795 32810186597748520486156193)
      ·
        refine ⟨24607639948311390364617145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32810186597748520486156193 24607639948311390364617145)
        ·
          refine ⟨18455729961233542773462859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24607639948311390364617145 18455729961233542773462859)
          ·
            refine ⟨27683594941850314160194289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18455729961233542773462859 27683594941850314160194289)
            ·
              refine ⟨20762696206387735620145717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27683594941850314160194289 20762696206387735620145717)
              ·
                refine ⟨1946502769348850214388661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20762696206387735620145717 1946502769348850214388661)
                ·
                  refine ⟨182484634626454707598937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1946502769348850214388661 182484634626454707598937)
                  ·
                    rfl

theorem cell22_1599244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 5].length) (baseStart_1599244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599244 prefixEnd_1599244 := by exact prefixLift 1599244
  have htrace : WordTrace (prefixWord ++ tailWord_1599244) baseStart_1599244 baseEnd_1599244 := by
    simpa [prefixWord, tailWord_1599244, baseEnd_1599244] using wordTrace_append hprefix tailTrace_1599244
  have hstable : (prefixWord ++ tailWord_1599244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599244).length < 2 ^ (prefixWord ++ tailWord_1599244).sum := by decide
  have hdescent : baseEnd_1599244 < baseStart_1599244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599265 : List Nat := [1, 2, 3, 2, 1, 5, 1, 3, 1, 3]
def baseStart_1599265 : Nat := 118140960795 + 1599265 * 2 ^ 59
def prefixEnd_1599265 : Nat := 4983230072969 + 3 ^ 40 * 1599265 * 2
def baseEnd_1599265 : Nat := 547461092608527068021747

theorem tailTrace_1599265 : CollatzResearch.WordTrace tailWord_1599265 prefixEnd_1599265 547461092608527068021747 := by
  unfold tailWord_1599265
  simp only [CollatzResearch.WordTrace]
  refine ⟨58329986551143512561903249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38886657700762341707935499 58329986551143512561903249)
  ·
    refine ⟨43747489913357634421427437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58329986551143512561903249 43747489913357634421427437)
    ·
      refine ⟨16405308717509112908035289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43747489913357634421427437 16405308717509112908035289)
      ·
        refine ⟨12303981538131834681026467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16405308717509112908035289 12303981538131834681026467)
        ·
          refine ⟨18455972307197752021539701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12303981538131834681026467 18455972307197752021539701)
          ·
            refine ⟨1730247403799789252019347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18455972307197752021539701 1730247403799789252019347)
            ·
              refine ⟨2595371105699683878029021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1730247403799789252019347 2595371105699683878029021)
              ·
                refine ⟨973264164637381454260883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2595371105699683878029021 973264164637381454260883)
                ·
                  refine ⟨1459896246956072181391325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 973264164637381454260883 1459896246956072181391325)
                  ·
                    refine ⟨547461092608527068021747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1459896246956072181391325 547461092608527068021747)
                    ·
                      rfl

theorem cell22_1599265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 1, 3].length) (baseStart_1599265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599265 prefixEnd_1599265 := by exact prefixLift 1599265
  have htrace : WordTrace (prefixWord ++ tailWord_1599265) baseStart_1599265 baseEnd_1599265 := by
    simpa [prefixWord, tailWord_1599265, baseEnd_1599265] using wordTrace_append hprefix tailTrace_1599265
  have hstable : (prefixWord ++ tailWord_1599265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599265).length < 2 ^ (prefixWord ++ tailWord_1599265).sum := by decide
  have hdescent : baseEnd_1599265 < baseStart_1599265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599295 : List Nat := [1, 1, 2, 2, 7, 1, 2, 1, 5]
def baseStart_1599295 : Nat := 118140960795 + 1599295 * 2 ^ 59
def prefixEnd_1599295 : Nat := 4983230072969 + 3 ^ 40 * 1599295 * 2
def baseEnd_1599295 : Nat := 182490454073872329923885

theorem tailTrace_1599295 : CollatzResearch.WordTrace tailWord_1599295 prefixEnd_1599295 182490454073872329923885 := by
  unfold tailWord_1599295
  simp only [CollatzResearch.WordTrace]
  refine ⟨58331080741034827685495339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38887387160689885123663559 58331080741034827685495339)
  ·
    refine ⟨87496621111552241528243009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58331080741034827685495339 87496621111552241528243009)
    ·
      refine ⟨65622465833664181146182257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87496621111552241528243009 65622465833664181146182257)
      ·
        refine ⟨49216849375248135859636693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65622465833664181146182257 49216849375248135859636693)
        ·
          refine ⟨1153519907232378184210235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 49216849375248135859636693 1153519907232378184210235)
          ·
            refine ⟨1730279860848567276315353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153519907232378184210235 1730279860848567276315353)
            ·
              refine ⟨1297709895636425457236515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1730279860848567276315353 1297709895636425457236515)
              ·
                refine ⟨1946564843454638185854773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1297709895636425457236515 1946564843454638185854773)
                ·
                  refine ⟨182490454073872329923885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1946564843454638185854773 182490454073872329923885)
                  ·
                    rfl

theorem cell22_1599295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 5].length) (baseStart_1599295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599295 prefixEnd_1599295 := by exact prefixLift 1599295
  have htrace : WordTrace (prefixWord ++ tailWord_1599295) baseStart_1599295 baseEnd_1599295 := by
    simpa [prefixWord, tailWord_1599295, baseEnd_1599295] using wordTrace_append hprefix tailTrace_1599295
  have hstable : (prefixWord ++ tailWord_1599295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599295).length < 2 ^ (prefixWord ++ tailWord_1599295).sum := by decide
  have hdescent : baseEnd_1599295 < baseStart_1599295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599336 : List Nat := [2, 1, 4, 2, 1, 1, 1, 4, 2, 4]
def baseStart_1599336 : Nat := 118140960795 + 1599336 * 2 ^ 59
def prefixEnd_1599336 : Nat := 4983230072969 + 3 ^ 40 * 1599336 * 2
def baseEnd_1599336 : Nat := 547485397359506549496529

theorem tailTrace_1599336 : CollatzResearch.WordTrace tailWord_1599336 prefixEnd_1599336 547485397359506549496529 := by
  unfold tailWord_1599336
  simp only [CollatzResearch.WordTrace]
  refine ⟨29166288066943145843868931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38888384089257527791825241 29166288066943145843868931)
  ·
    refine ⟨43749432100414718765803397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29166288066943145843868931 43749432100414718765803397)
    ·
      refine ⟨8203018518827759768588137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43749432100414718765803397 8203018518827759768588137)
      ·
        refine ⟨6152263889120819826441103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8203018518827759768588137 6152263889120819826441103)
        ·
          refine ⟨9228395833681229739661655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6152263889120819826441103 9228395833681229739661655)
          ·
            refine ⟨13842593750521844609492483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9228395833681229739661655 13842593750521844609492483)
            ·
              refine ⟨20763890625782766914238725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13842593750521844609492483 20763890625782766914238725)
              ·
                refine ⟨3893229492334268796419761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20763890625782766914238725 3893229492334268796419761)
                ·
                  refine ⟨2919922119250701597314821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3893229492334268796419761 2919922119250701597314821)
                  ·
                    refine ⟨547485397359506549496529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2919922119250701597314821 547485397359506549496529)
                    ·
                      rfl

theorem cell22_1599336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_1599336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599336 prefixEnd_1599336 := by exact prefixLift 1599336
  have htrace : WordTrace (prefixWord ++ tailWord_1599336) baseStart_1599336 baseEnd_1599336 := by
    simpa [prefixWord, tailWord_1599336, baseEnd_1599336] using wordTrace_append hprefix tailTrace_1599336
  have hstable : (prefixWord ++ tailWord_1599336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599336).length < 2 ^ (prefixWord ++ tailWord_1599336).sum := by decide
  have hdescent : baseEnd_1599336 < baseStart_1599336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599340 : List Nat := [2, 2, 1, 1, 4, 4, 2, 2, 4]
def baseStart_1599340 : Nat := 118140960795 + 1599340 * 2 ^ 59
def prefixEnd_1599340 : Nat := 4983230072969 + 3 ^ 40 * 1599340 * 2
def baseEnd_1599340 : Nat := 182495588880417290798839

theorem tailTrace_1599340 : CollatzResearch.WordTrace tailWord_1599340 prefixEnd_1599340 182495588880417290798839 := by
  unfold tailWord_1599340
  simp only [CollatzResearch.WordTrace]
  refine ⟨29166361012935900185441737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38888481350581200247255649 29166361012935900185441737)
  ·
    refine ⟨21874770759701925139081303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29166361012935900185441737 21874770759701925139081303)
    ·
      refine ⟨32812156139552887708621955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21874770759701925139081303 32812156139552887708621955)
      ·
        refine ⟨49218234209329331562932933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32812156139552887708621955 49218234209329331562932933)
        ·
          refine ⟨9228418914249249668049925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49218234209329331562932933 9228418914249249668049925)
          ·
            refine ⟨1730328546421734312759361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9228418914249249668049925 1730328546421734312759361)
            ·
              refine ⟨1297746409816300734569521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1730328546421734312759361 1297746409816300734569521)
              ·
                refine ⟨973309807362225550927141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1297746409816300734569521 973309807362225550927141)
                ·
                  refine ⟨182495588880417290798839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 973309807362225550927141 182495588880417290798839)
                  ·
                    rfl

theorem cell22_1599340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_1599340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599340 prefixEnd_1599340 := by exact prefixLift 1599340
  have htrace : WordTrace (prefixWord ++ tailWord_1599340) baseStart_1599340 baseEnd_1599340 := by
    simpa [prefixWord, tailWord_1599340, baseEnd_1599340] using wordTrace_append hprefix tailTrace_1599340
  have hstable : (prefixWord ++ tailWord_1599340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599340).length < 2 ^ (prefixWord ++ tailWord_1599340).sum := by decide
  have hdescent : baseEnd_1599340 < baseStart_1599340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599368 : List Nat := [2, 1, 3, 3, 3, 1, 3, 6]
def baseStart_1599368 : Nat := 118140960795 + 1599368 * 2 ^ 59
def prefixEnd_1599368 : Nat := 4983230072969 + 3 ^ 40 * 1599368 * 2
def baseEnd_1599368 : Nat := 60832927957052125855159

theorem tailTrace_1599368 : CollatzResearch.WordTrace tailWord_1599368 prefixEnd_1599368 60832927957052125855159 := by
  unfold tailWord_1599368
  simp only [CollatzResearch.WordTrace]
  refine ⟨29166871634885180576451379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38889162179846907435268505 29166871634885180576451379)
  ·
    refine ⟨43750307452327770864677069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29166871634885180576451379 43750307452327770864677069)
    ·
      refine ⟨16406365294622914074253901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43750307452327770864677069 16406365294622914074253901)
      ·
        refine ⟨6152386985483592777845213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16406365294622914074253901 6152386985483592777845213)
        ·
          refine ⟨2307145119556347291691955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6152386985483592777845213 2307145119556347291691955)
          ·
            refine ⟨3460717679334520937537933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2307145119556347291691955 3460717679334520937537933)
            ·
              refine ⟨1297769129750445351576725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3460717679334520937537933 1297769129750445351576725)
              ·
                refine ⟨60832927957052125855159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1297769129750445351576725 60832927957052125855159)
                ·
                  rfl

theorem cell22_1599368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 6].length) (baseStart_1599368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599368 prefixEnd_1599368 := by exact prefixLift 1599368
  have htrace : WordTrace (prefixWord ++ tailWord_1599368) baseStart_1599368 baseEnd_1599368 := by
    simpa [prefixWord, tailWord_1599368, baseEnd_1599368] using wordTrace_append hprefix tailTrace_1599368
  have hstable : (prefixWord ++ tailWord_1599368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599368).length < 2 ^ (prefixWord ++ tailWord_1599368).sum := by decide
  have hdescent : baseEnd_1599368 < baseStart_1599368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599370 : List Nat := [3, 1, 2, 4, 2, 2, 1, 1, 2, 4]
def baseStart_1599370 : Nat := 118140960795 + 1599370 * 2 ^ 59
def prefixEnd_1599370 : Nat := 4983230072969 + 3 ^ 40 * 1599370 * 2
def baseEnd_1599370 : Nat := 547497036254341794146425

theorem tailTrace_1599370 : CollatzResearch.WordTrace tailWord_1599370 prefixEnd_1599370 547497036254341794146425 := by
  unfold tailWord_1599370
  simp only [CollatzResearch.WordTrace]
  refine ⟨14583454053940778873618891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38889210810508743662983709 14583454053940778873618891)
  ·
    refine ⟨21875181080911168310428337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14583454053940778873618891 21875181080911168310428337)
    ·
      refine ⟨16406385810683376232821253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21875181080911168310428337 16406385810683376232821253)
      ·
        refine ⟨3076197339503133043653985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16406385810683376232821253 3076197339503133043653985)
        ·
          refine ⟨2307148004627349782740489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3076197339503133043653985 2307148004627349782740489)
          ·
            refine ⟨1730361003470512337055367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2307148004627349782740489 1730361003470512337055367)
            ·
              refine ⟨2595541505205768505583051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1730361003470512337055367 2595541505205768505583051)
              ·
                refine ⟨3893312257808652758374577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2595541505205768505583051 3893312257808652758374577)
                ·
                  refine ⟨2919984193356489568780933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3893312257808652758374577 2919984193356489568780933)
                  ·
                    refine ⟨547497036254341794146425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2919984193356489568780933 547497036254341794146425)
                    ·
                      rfl

theorem cell22_1599370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_1599370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599370 prefixEnd_1599370 := by exact prefixLift 1599370
  have htrace : WordTrace (prefixWord ++ tailWord_1599370) baseStart_1599370 baseEnd_1599370 := by
    simpa [prefixWord, tailWord_1599370, baseEnd_1599370] using wordTrace_append hprefix tailTrace_1599370
  have hstable : (prefixWord ++ tailWord_1599370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599370).length < 2 ^ (prefixWord ++ tailWord_1599370).sum := by decide
  have hdescent : baseEnd_1599370 < baseStart_1599370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599396 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 7]
def baseStart_1599396 : Nat := 118140960795 + 1599396 * 2 ^ 59
def prefixEnd_1599396 : Nat := 4983230072969 + 3 ^ 40 * 1599396 * 2
def baseEnd_1599396 : Nat := 182501978861895464332115

theorem tailTrace_1599396 : CollatzResearch.WordTrace tailWord_1599396 prefixEnd_1599396 182501978861895464332115 := by
  unfold tailWord_1599396
  simp only [CollatzResearch.WordTrace]
  refine ⟨29167382256834460967461021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38889843009112614623281361 29167382256834460967461021)
  ·
    refine ⟨10937768346312922862797883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29167382256834460967461021 10937768346312922862797883)
    ·
      refine ⟨16406652519469384294196825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10937768346312922862797883 16406652519469384294196825)
      ·
        refine ⟨12304989389602038220647619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16406652519469384294196825 12304989389602038220647619)
        ·
          refine ⟨18457484084403057330971429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12304989389602038220647619 18457484084403057330971429)
          ·
            refine ⟨3460778265825573249557143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18457484084403057330971429 3460778265825573249557143)
            ·
              refine ⟨5191167398738359874335715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3460778265825573249557143 5191167398738359874335715)
              ·
                refine ⟨7786751098107539811503573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5191167398738359874335715 7786751098107539811503573)
                ·
                  refine ⟨182501978861895464332115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7786751098107539811503573 182501978861895464332115)
                  ·
                    rfl

theorem cell22_1599396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_1599396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599396 prefixEnd_1599396 := by exact prefixLift 1599396
  have htrace : WordTrace (prefixWord ++ tailWord_1599396) baseStart_1599396 baseEnd_1599396 := by
    simpa [prefixWord, tailWord_1599396, baseEnd_1599396] using wordTrace_append hprefix tailTrace_1599396
  have hstable : (prefixWord ++ tailWord_1599396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599396).length < 2 ^ (prefixWord ++ tailWord_1599396).sum := by decide
  have hdescent : baseEnd_1599396 < baseStart_1599396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599406 : List Nat := [4, 1, 5, 1, 1, 1, 3, 1, 2, 3]
def baseStart_1599406 : Nat := 118140960795 + 1599406 * 2 ^ 59
def prefixEnd_1599406 : Nat := 4983230072969 + 3 ^ 40 * 1599406 * 2
def baseEnd_1599406 : Nat := 547509359790049700246315

theorem tailTrace_1599406 : CollatzResearch.WordTrace tailWord_1599406 prefixEnd_1599406 547509359790049700246315 := by
  unfold tailWord_1599406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7291891155454086705348259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38890086162421795761857381 7291891155454086705348259)
  ·
    refine ⟨10937836733181130058022389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7291891155454086705348259 10937836733181130058022389)
    ·
      refine ⟨1025422193735730942939599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10937836733181130058022389 1025422193735730942939599)
      ·
        refine ⟨1538133290603596414409399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1025422193735730942939599 1538133290603596414409399)
        ·
          refine ⟨2307199935905394621614099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538133290603596414409399 2307199935905394621614099)
          ·
            refine ⟨3460799903858091932421149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2307199935905394621614099 3460799903858091932421149)
            ·
              refine ⟨1297799963946784474657931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3460799903858091932421149 1297799963946784474657931)
              ·
                refine ⟨1946699945920176711986897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1297799963946784474657931 1946699945920176711986897)
                ·
                  refine ⟨1460024959440132533990173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1946699945920176711986897 1460024959440132533990173)
                  ·
                    refine ⟨547509359790049700246315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1460024959440132533990173 547509359790049700246315)
                    ·
                      rfl

theorem cell22_1599406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_1599406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599406 prefixEnd_1599406 := by exact prefixLift 1599406
  have htrace : WordTrace (prefixWord ++ tailWord_1599406) baseStart_1599406 baseEnd_1599406 := by
    simpa [prefixWord, tailWord_1599406, baseEnd_1599406] using wordTrace_append hprefix tailTrace_1599406
  have hstable : (prefixWord ++ tailWord_1599406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599406).length < 2 ^ (prefixWord ++ tailWord_1599406).sum := by decide
  have hdescent : baseEnd_1599406 < baseStart_1599406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599471 : List Nat := [1, 1, 2, 1, 4, 2, 1, 2, 4, 4]
def baseStart_1599471 : Nat := 118140960795 + 1599471 * 2 ^ 59
def prefixEnd_1599471 : Nat := 4983230072969 + 3 ^ 40 * 1599471 * 2
def baseEnd_1599471 : Nat := 547531610618411197371115

theorem tailTrace_1599471 : CollatzResearch.WordTrace tailWord_1599471 prefixEnd_1599471 547531610618411197371115 := by
  unfold tailWord_1599471
  simp only [CollatzResearch.WordTrace]
  refine ⟨58337499988397209743902267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38891666658931473162601511 58337499988397209743902267)
  ·
    refine ⟨87506249982595814615853401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58337499988397209743902267 87506249982595814615853401)
    ·
      refine ⟨65629687486946860961890051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87506249982595814615853401 65629687486946860961890051)
      ·
        refine ⟨98444531230420291442835077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65629687486946860961890051 98444531230420291442835077)
        ·
          refine ⟨18458349605703804645531577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98444531230420291442835077 18458349605703804645531577)
          ·
            refine ⟨13843762204277853484148683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18458349605703804645531577 13843762204277853484148683)
            ·
              refine ⟨20765643306416780226223025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13843762204277853484148683 20765643306416780226223025)
              ·
                refine ⟨15574232479812585169667269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20765643306416780226223025 15574232479812585169667269)
                ·
                  refine ⟨2920168589964859719312613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15574232479812585169667269 2920168589964859719312613)
                  ·
                    refine ⟨547531610618411197371115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2920168589964859719312613 547531610618411197371115)
                    ·
                      rfl

theorem cell22_1599471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_1599471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599471 prefixEnd_1599471 := by exact prefixLift 1599471
  have htrace : WordTrace (prefixWord ++ tailWord_1599471) baseStart_1599471 baseEnd_1599471 := by
    simpa [prefixWord, tailWord_1599471, baseEnd_1599471] using wordTrace_append hprefix tailTrace_1599471
  have hstable : (prefixWord ++ tailWord_1599471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599471).length < 2 ^ (prefixWord ++ tailWord_1599471).sum := by decide
  have hdescent : baseEnd_1599471 < baseStart_1599471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599509 : List Nat := [1, 3, 2, 1, 6, 1, 2, 2, 4]
def baseStart_1599509 : Nat := 118140960795 + 1599509 * 2 ^ 59
def prefixEnd_1599509 : Nat := 4983230072969 + 3 ^ 40 * 1599509 * 2
def baseEnd_1599509 : Nat := 182514872931663921640333

theorem tailTrace_1599509 : CollatzResearch.WordTrace tailWord_1599509 prefixEnd_1599509 182514872931663921640333 := by
  unfold tailWord_1599509
  simp only [CollatzResearch.WordTrace]
  refine ⟨58338885962259542233785581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38892590641506361489190387 58338885962259542233785581)
  ·
    refine ⟨21877082235847328337669593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58338885962259542233785581 21877082235847328337669593)
    ·
      refine ⟨16407811676885496253252195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21877082235847328337669593 16407811676885496253252195)
      ·
        refine ⟨24611717515328244379878293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16407811676885496253252195 24611717515328244379878293)
        ·
          refine ⟨1153674258531011455306795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24611717515328244379878293 1153674258531011455306795)
          ·
            refine ⟨1730511387796517182960193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153674258531011455306795 1730511387796517182960193)
            ·
              refine ⟨1297883540847387887220145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1730511387796517182960193 1297883540847387887220145)
              ·
                refine ⟨973412655635540915415109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1297883540847387887220145 973412655635540915415109)
                ·
                  refine ⟨182514872931663921640333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 973412655635540915415109 182514872931663921640333)
                  ·
                    rfl

theorem cell22_1599509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 2, 4].length) (baseStart_1599509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599509 prefixEnd_1599509 := by exact prefixLift 1599509
  have htrace : WordTrace (prefixWord ++ tailWord_1599509) baseStart_1599509 baseEnd_1599509 := by
    simpa [prefixWord, tailWord_1599509, baseEnd_1599509] using wordTrace_append hprefix tailTrace_1599509
  have hstable : (prefixWord ++ tailWord_1599509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599509).length < 2 ^ (prefixWord ++ tailWord_1599509).sum := by decide
  have hdescent : baseEnd_1599509 < baseStart_1599509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599546 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 3, 7]
def baseStart_1599546 : Nat := 118140960795 + 1599546 * 2 ^ 59
def prefixEnd_1599546 : Nat := 4983230072969 + 3 ^ 40 * 1599546 * 2
def baseEnd_1599546 : Nat := 547557284651136001745885

theorem tailTrace_1599546 : CollatzResearch.WordTrace tailWord_1599546 prefixEnd_1599546 547557284651136001745885 := by
  unfold tailWord_1599546
  simp only [CollatzResearch.WordTrace]
  refine ⟨14585058865781374388220623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38893490308750331701921661 14585058865781374388220623)
  ·
    refine ⟨21877588298672061582330935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14585058865781374388220623 21877588298672061582330935)
    ·
      refine ⟨32816382448008092373496403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21877588298672061582330935 32816382448008092373496403)
      ·
        refine ⟨49224573672012138560244605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32816382448008092373496403 49224573672012138560244605)
        ·
          refine ⟨18459215127004551960091727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49224573672012138560244605 18459215127004551960091727)
          ·
            refine ⟨27688822690506827940137591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18459215127004551960091727 27688822690506827940137591)
            ·
              refine ⟨41533234035760241910206387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27688822690506827940137591 41533234035760241910206387)
              ·
                refine ⟨62299851053640362865309581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41533234035760241910206387 62299851053640362865309581)
                ·
                  refine ⟨23362444145115136074491093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62299851053640362865309581 23362444145115136074491093)
                  ·
                    refine ⟨547557284651136001745885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23362444145115136074491093 547557284651136001745885)
                    ·
                      rfl

theorem cell22_1599546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_1599546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599546 prefixEnd_1599546 := by exact prefixLift 1599546
  have htrace : WordTrace (prefixWord ++ tailWord_1599546) baseStart_1599546 baseEnd_1599546 := by
    simpa [prefixWord, tailWord_1599546, baseEnd_1599546] using wordTrace_append hprefix tailTrace_1599546
  have hstable : (prefixWord ++ tailWord_1599546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599546).length < 2 ^ (prefixWord ++ tailWord_1599546).sum := by decide
  have hdescent : baseEnd_1599546 < baseStart_1599546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599552 : List Nat := [2, 1, 1, 2, 2, 5, 2, 3, 1, 3]
def baseStart_1599552 : Nat := 118140960795 + 1599552 * 2 ^ 59
def prefixEnd_1599552 : Nat := 4983230072969 + 3 ^ 40 * 1599552 * 2
def baseEnd_1599552 : Nat := 547559338573753986095867

theorem tailTrace_1599552 : CollatzResearch.WordTrace tailWord_1599552 prefixEnd_1599552 547559338573753986095867 := by
  unfold tailWord_1599552
  simp only [CollatzResearch.WordTrace]
  refine ⟨29170227150551880288800455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38893636200735840385067273 29170227150551880288800455)
  ·
    refine ⟨43755340725827820433200683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29170227150551880288800455 43755340725827820433200683)
    ·
      refine ⟨65633011088741730649801025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43755340725827820433200683 65633011088741730649801025)
      ·
        refine ⟨49224758316556297987350769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65633011088741730649801025 49224758316556297987350769)
        ·
          refine ⟨36918568737417223490513077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49224758316556297987350769 36918568737417223490513077)
          ·
            refine ⟨3461115819132864702235601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36918568737417223490513077 3461115819132864702235601)
            ·
              refine ⟨2595836864349648526676701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3461115819132864702235601 2595836864349648526676701)
              ·
                refine ⟨973438824131118197503763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2595836864349648526676701 973438824131118197503763)
                ·
                  refine ⟨1460158236196677296255645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 973438824131118197503763 1460158236196677296255645)
                  ·
                    refine ⟨547559338573753986095867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1460158236196677296255645 547559338573753986095867)
                    ·
                      rfl

theorem cell22_1599552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 1, 3].length) (baseStart_1599552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599552 prefixEnd_1599552 := by exact prefixLift 1599552
  have htrace : WordTrace (prefixWord ++ tailWord_1599552) baseStart_1599552 baseEnd_1599552 := by
    simpa [prefixWord, tailWord_1599552, baseEnd_1599552] using wordTrace_append hprefix tailTrace_1599552
  have hstable : (prefixWord ++ tailWord_1599552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599552).length < 2 ^ (prefixWord ++ tailWord_1599552).sum := by decide
  have hdescent : baseEnd_1599552 < baseStart_1599552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599623 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 4, 4]
def baseStart_1599623 : Nat := 118140960795 + 1599623 * 2 ^ 59
def prefixEnd_1599623 : Nat := 4983230072969 + 3 ^ 40 * 1599623 * 2
def baseEnd_1599623 : Nat := 547583643324733467570649

theorem tailTrace_1599623 : CollatzResearch.WordTrace tailWord_1599623 prefixEnd_1599623 547583643324733467570649 := by
  unfold tailWord_1599623
  simp only [CollatzResearch.WordTrace]
  refine ⟨58343043883846539703435523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38895362589231026468957015 58343043883846539703435523)
  ·
    refine ⟨87514565825769809555153285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58343043883846539703435523 87514565825769809555153285)
    ·
      refine ⟨16408981092331839291591241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87514565825769809555153285 16408981092331839291591241)
      ·
        refine ⟨12306735819248879468693431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16408981092331839291591241 12306735819248879468693431)
        ·
          refine ⟨18460103728873319203040147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12306735819248879468693431 18460103728873319203040147)
          ·
            refine ⟨27690155593309978804560221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18460103728873319203040147 27690155593309978804560221)
            ·
              refine ⟨10383808347491242051710083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27690155593309978804560221 10383808347491242051710083)
              ·
                refine ⟨15575712521236863077565125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10383808347491242051710083 15575712521236863077565125)
                ·
                  refine ⟨2920446097731911827043461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15575712521236863077565125 2920446097731911827043461)
                  ·
                    refine ⟨547583643324733467570649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2920446097731911827043461 547583643324733467570649)
                    ·
                      rfl

theorem cell22_1599623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_1599623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599623 prefixEnd_1599623 := by exact prefixLift 1599623
  have htrace : WordTrace (prefixWord ++ tailWord_1599623) baseStart_1599623 baseEnd_1599623 := by
    simpa [prefixWord, tailWord_1599623, baseEnd_1599623] using wordTrace_append hprefix tailTrace_1599623
  have hstable : (prefixWord ++ tailWord_1599623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599623).length < 2 ^ (prefixWord ++ tailWord_1599623).sum := by decide
  have hdescent : baseEnd_1599623 < baseStart_1599623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599625 : List Nat := [1, 2, 1, 1, 4, 2, 2, 4, 2, 3]
def baseStart_1599625 : Nat := 118140960795 + 1599625 * 2 ^ 59
def prefixEnd_1599625 : Nat := 4983230072969 + 3 ^ 40 * 1599625 * 2
def baseEnd_1599625 : Nat := 547584327965606129020643

theorem tailTrace_1599625 : CollatzResearch.WordTrace tailWord_1599625 prefixEnd_1599625 547584327965606129020643 := by
  unfold tailWord_1599625
  simp only [CollatzResearch.WordTrace]
  refine ⟨58343116829839294045008329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38895411219892862696672219 58343116829839294045008329)
  ·
    refine ⟨43757337622379470533756247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58343116829839294045008329 43757337622379470533756247)
    ·
      refine ⟨65636006433569205800634371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43757337622379470533756247 65636006433569205800634371)
      ·
        refine ⟨98454009650353808700951557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65636006433569205800634371 98454009650353808700951557)
        ·
          refine ⟨18460126809441339131428417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98454009650353808700951557 18460126809441339131428417)
          ·
            refine ⟨13845095107081004348571313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18460126809441339131428417 13845095107081004348571313)
            ·
              refine ⟨10383821330310753261428485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13845095107081004348571313 10383821330310753261428485)
              ·
                refine ⟨1946966499433266236517841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10383821330310753261428485 1946966499433266236517841)
                ·
                  refine ⟨1460224874574949677388381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1946966499433266236517841 1460224874574949677388381)
                  ·
                    refine ⟨547584327965606129020643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1460224874574949677388381 547584327965606129020643)
                    ·
                      rfl

theorem cell22_1599625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 3].length) (baseStart_1599625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599625 prefixEnd_1599625 := by exact prefixLift 1599625
  have htrace : WordTrace (prefixWord ++ tailWord_1599625) baseStart_1599625 baseEnd_1599625 := by
    simpa [prefixWord, tailWord_1599625, baseEnd_1599625] using wordTrace_append hprefix tailTrace_1599625
  have hstable : (prefixWord ++ tailWord_1599625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599625).length < 2 ^ (prefixWord ++ tailWord_1599625).sum := by decide
  have hdescent : baseEnd_1599625 < baseStart_1599625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599646 : List Nat := [4, 3, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_1599646 : Nat := 118140960795 + 1599646 * 2 ^ 59
def prefixEnd_1599646 : Nat := 4983230072969 + 3 ^ 40 * 1599646 * 2
def baseEnd_1599646 : Nat := 547591516694769074245579

theorem tailTrace_1599646 : CollatzResearch.WordTrace tailWord_1599646 prefixEnd_1599646 547591516694769074245579 := by
  unfold tailWord_1599646
  simp only [CollatzResearch.WordTrace]
  refine ⟨7292985345345401828940349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38895921841842143087681861 7292985345345401828940349)
  ·
    refine ⟨2734869504504525685852631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7292985345345401828940349 2734869504504525685852631)
    ·
      refine ⟨4102304256756788528778947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2734869504504525685852631 4102304256756788528778947)
      ·
        refine ⟨6153456385135182793168421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4102304256756788528778947 6153456385135182793168421)
        ·
          refine ⟨1153773072212846773719079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6153456385135182793168421 1153773072212846773719079)
          ·
            refine ⟨1730659608319270160578619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153773072212846773719079 1730659608319270160578619)
            ·
              refine ⟨2595989412478905240867929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1730659608319270160578619 2595989412478905240867929)
              ·
                refine ⟨1946992059359178930650947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2595989412478905240867929 1946992059359178930650947)
                ·
                  refine ⟨2920488089038768395976421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1946992059359178930650947 2920488089038768395976421)
                  ·
                    refine ⟨547591516694769074245579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2920488089038768395976421 547591516694769074245579)
                    ·
                      rfl

theorem cell22_1599646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_1599646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599646 prefixEnd_1599646 := by exact prefixLift 1599646
  have htrace : WordTrace (prefixWord ++ tailWord_1599646) baseStart_1599646 baseEnd_1599646 := by
    simpa [prefixWord, tailWord_1599646, baseEnd_1599646] using wordTrace_append hprefix tailTrace_1599646
  have hstable : (prefixWord ++ tailWord_1599646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599646).length < 2 ^ (prefixWord ++ tailWord_1599646).sum := by decide
  have hdescent : baseEnd_1599646 < baseStart_1599646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599745 : List Nat := [1, 2, 4, 1, 1, 2, 4, 1, 6]
def baseStart_1599745 : Nat := 118140960795 + 1599745 * 2 ^ 59
def prefixEnd_1599745 : Nat := 4983230072969 + 3 ^ 40 * 1599745 * 2
def baseEnd_1599745 : Nat := 182541802139321938673425

theorem tailTrace_1599745 : CollatzResearch.WordTrace tailWord_1599745 prefixEnd_1599745 182541802139321938673425 := by
  unfold tailWord_1599745
  simp only [CollatzResearch.WordTrace]
  refine ⟨58347493589404554539376689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38898329059603036359584459 58347493589404554539376689)
  ·
    refine ⟨43760620192053415904532517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58347493589404554539376689 43760620192053415904532517)
    ·
      refine ⟨8205116286010015482099847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43760620192053415904532517 8205116286010015482099847)
      ·
        refine ⟨12307674429015023223149771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8205116286010015482099847 12307674429015023223149771)
        ·
          refine ⟨18461511643522534834724657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12307674429015023223149771 18461511643522534834724657)
          ·
            refine ⟨13846133732641901126043493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18461511643522534834724657 13846133732641901126043493)
            ·
              refine ⟨2596150074870356461133155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13846133732641901126043493 2596150074870356461133155)
              ·
                refine ⟨3894225112305534691699733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2596150074870356461133155 3894225112305534691699733)
                ·
                  refine ⟨182541802139321938673425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3894225112305534691699733 182541802139321938673425)
                  ·
                    rfl

theorem cell22_1599745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 6].length) (baseStart_1599745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599745 prefixEnd_1599745 := by exact prefixLift 1599745
  have htrace : WordTrace (prefixWord ++ tailWord_1599745) baseStart_1599745 baseEnd_1599745 := by
    simpa [prefixWord, tailWord_1599745, baseEnd_1599745] using wordTrace_append hprefix tailTrace_1599745
  have hstable : (prefixWord ++ tailWord_1599745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599745).length < 2 ^ (prefixWord ++ tailWord_1599745).sum := by decide
  have hdescent : baseEnd_1599745 < baseStart_1599745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599775 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 1, 6]
def baseStart_1599775 : Nat := 118140960795 + 1599775 * 2 ^ 59
def prefixEnd_1599775 : Nat := 4983230072969 + 3 ^ 40 * 1599775 * 2
def baseEnd_1599775 : Nat := 547635676031055737770183

theorem tailTrace_1599775 : CollatzResearch.WordTrace tailWord_1599775 prefixEnd_1599775 547635676031055737770183 := by
  unfold tailWord_1599775
  simp only [CollatzResearch.WordTrace]
  refine ⟨58348587779295869662968779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38899058519530579775312519 58348587779295869662968779)
  ·
    refine ⟨87522881668943804494453169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58348587779295869662968779 87522881668943804494453169)
    ·
      refine ⟨65642161251707853370839877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87522881668943804494453169 65642161251707853370839877)
      ·
        refine ⟨12307905234695222507032477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65642161251707853370839877 12307905234695222507032477)
        ·
          refine ⟨4615464463010708440137179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12307905234695222507032477 4615464463010708440137179)
          ·
            refine ⟨6923196694516062660205769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4615464463010708440137179 6923196694516062660205769)
            ·
              refine ⟨5192397520887046995154327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6923196694516062660205769 5192397520887046995154327)
              ·
                refine ⟨7788596281330570492731491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5192397520887046995154327 7788596281330570492731491)
                ·
                  refine ⟨11682894421995855739097237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7788596281330570492731491 11682894421995855739097237)
                  ·
                    refine ⟨547635676031055737770183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11682894421995855739097237 547635676031055737770183)
                    ·
                      rfl

theorem cell22_1599775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_1599775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599775 prefixEnd_1599775 := by exact prefixLift 1599775
  have htrace : WordTrace (prefixWord ++ tailWord_1599775) baseStart_1599775 baseEnd_1599775 := by
    simpa [prefixWord, tailWord_1599775, baseEnd_1599775] using wordTrace_append hprefix tailTrace_1599775
  have hstable : (prefixWord ++ tailWord_1599775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599775).length < 2 ^ (prefixWord ++ tailWord_1599775).sum := by decide
  have hdescent : baseEnd_1599775 < baseStart_1599775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599796 : List Nat := [2, 5, 1, 1, 1, 3, 3, 2, 4]
def baseStart_1599796 : Nat := 118140960795 + 1599796 * 2 ^ 59
def prefixEnd_1599796 : Nat := 4983230072969 + 3 ^ 40 * 1599796 * 2
def baseEnd_1599796 : Nat := 182547621586739560998373

theorem tailTrace_1599796 : CollatzResearch.WordTrace tailWord_1599796 prefixEnd_1599796 182547621586739560998373 := by
  unfold tailWord_1599796
  simp only [CollatzResearch.WordTrace]
  refine ⟨29174676856109895124741621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38899569141479860166322161 29174676856109895124741621)
  ·
    refine ⟨2735125955260302667944527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29174676856109895124741621 2735125955260302667944527)
    ·
      refine ⟨4102688932890454001916791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2735125955260302667944527 4102688932890454001916791)
      ·
        refine ⟨6154033399335681002875187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4102688932890454001916791 6154033399335681002875187)
        ·
          refine ⟨9231050099003521504312781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6154033399335681002875187 9231050099003521504312781)
          ·
            refine ⟨3461643787126320564117293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9231050099003521504312781 3461643787126320564117293)
            ·
              refine ⟨1298116420172370211543985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3461643787126320564117293 1298116420172370211543985)
              ·
                refine ⟨973587315129277658657989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1298116420172370211543985 973587315129277658657989)
                ·
                  refine ⟨182547621586739560998373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 973587315129277658657989 182547621586739560998373)
                  ·
                    rfl

theorem cell22_1599796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_1599796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599796 prefixEnd_1599796 := by exact prefixLift 1599796
  have htrace : WordTrace (prefixWord ++ tailWord_1599796) baseStart_1599796 baseEnd_1599796 := by
    simpa [prefixWord, tailWord_1599796, baseEnd_1599796] using wordTrace_append hprefix tailTrace_1599796
  have hstable : (prefixWord ++ tailWord_1599796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599796).length < 2 ^ (prefixWord ++ tailWord_1599796).sum := by decide
  have hdescent : baseEnd_1599796 < baseStart_1599796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599856 : List Nat := [2, 1, 1, 1, 4, 3, 4, 2, 1, 3]
def baseStart_1599856 : Nat := 118140960795 + 1599856 * 2 ^ 59
def prefixEnd_1599856 : Nat := 4983230072969 + 3 ^ 40 * 1599856 * 2
def baseEnd_1599856 : Nat := 547663403986398526494935

theorem tailTrace_1599856 : CollatzResearch.WordTrace tailWord_1599856 prefixEnd_1599856 547663403986398526494935 := by
  unfold tailWord_1599856
  simp only [CollatzResearch.WordTrace]
  refine ⟨29175771046001210248333711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38901028061334946997778281 29175771046001210248333711)
  ·
    refine ⟨43763656569001815372500567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29175771046001210248333711 43763656569001815372500567)
    ·
      refine ⟨65645484853502723058750851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43763656569001815372500567 65645484853502723058750851)
      ·
        refine ⟨98468227280254084588126277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65645484853502723058750851 98468227280254084588126277)
        ·
          refine ⟨18462792615047640860273677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98468227280254084588126277 18462792615047640860273677)
          ·
            refine ⟨6923547230642865322602629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18462792615047640860273677 6923547230642865322602629)
            ·
              refine ⟨1298165105745537247987993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6923547230642865322602629 1298165105745537247987993)
              ·
                refine ⟨973623829309152935990995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1298165105745537247987993 973623829309152935990995)
                ·
                  refine ⟨1460435743963729403986493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 973623829309152935990995 1460435743963729403986493)
                  ·
                    refine ⟨547663403986398526494935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1460435743963729403986493 547663403986398526494935)
                    ·
                      rfl

theorem cell22_1599856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 1, 3].length) (baseStart_1599856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599856 prefixEnd_1599856 := by exact prefixLift 1599856
  have htrace : WordTrace (prefixWord ++ tailWord_1599856) baseStart_1599856 baseEnd_1599856 := by
    simpa [prefixWord, tailWord_1599856, baseEnd_1599856] using wordTrace_append hprefix tailTrace_1599856
  have hstable : (prefixWord ++ tailWord_1599856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599856).length < 2 ^ (prefixWord ++ tailWord_1599856).sum := by decide
  have hdescent : baseEnd_1599856 < baseStart_1599856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599929 : List Nat := [1, 2, 1, 4, 3, 3, 1, 1, 1, 5]
def baseStart_1599929 : Nat := 118140960795 + 1599929 * 2 ^ 59
def prefixEnd_1599929 : Nat := 4983230072969 + 3 ^ 40 * 1599929 * 2
def baseEnd_1599929 : Nat := 547688393378250669419711

theorem tailTrace_1599929 : CollatzResearch.WordTrace tailWord_1599929 prefixEnd_1599929 547688393378250669419711 := by
  unfold tailWord_1599929
  simp only [CollatzResearch.WordTrace]
  refine ⟨58354204620737953964074841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38902803080491969309383227 58354204620737953964074841)
  ·
    refine ⟨43765653465553465473056131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58354204620737953964074841 43765653465553465473056131)
    ·
      refine ⟨65648480198330198209584197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43765653465553465473056131 65648480198330198209584197)
      ·
        refine ⟨12309090037186912164297037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65648480198330198209584197 12309090037186912164297037)
        ·
          refine ⟨4615908763945092061611389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12309090037186912164297037 4615908763945092061611389)
          ·
            refine ⟨1730965786479409523104271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4615908763945092061611389 1730965786479409523104271)
            ·
              refine ⟨2596448679719114284656407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1730965786479409523104271 2596448679719114284656407)
              ·
                refine ⟨3894673019578671426984611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2596448679719114284656407 3894673019578671426984611)
                ·
                  refine ⟨5842009529368007140476917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3894673019578671426984611 5842009529368007140476917)
                  ·
                    refine ⟨547688393378250669419711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5842009529368007140476917 547688393378250669419711)
                    ·
                      rfl

theorem cell22_1599929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 5].length) (baseStart_1599929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599929 prefixEnd_1599929 := by exact prefixLift 1599929
  have htrace : WordTrace (prefixWord ++ tailWord_1599929) baseStart_1599929 baseEnd_1599929 := by
    simpa [prefixWord, tailWord_1599929, baseEnd_1599929] using wordTrace_append hprefix tailTrace_1599929
  have hstable : (prefixWord ++ tailWord_1599929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599929).length < 2 ^ (prefixWord ++ tailWord_1599929).sum := by decide
  have hdescent : baseEnd_1599929 < baseStart_1599929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599948 : List Nat := [2, 2, 1, 4, 4, 1, 1, 3, 4]
def baseStart_1599948 : Nat := 118140960795 + 1599948 * 2 ^ 59
def prefixEnd_1599948 : Nat := 4983230072969 + 3 ^ 40 * 1599948 * 2
def baseEnd_1599948 : Nat := 182564965822180317731551

theorem tailTrace_1599948 : CollatzResearch.WordTrace tailWord_1599948 prefixEnd_1599948 182564965822180317731551 := by
  unfold tailWord_1599948
  simp only [CollatzResearch.WordTrace]
  refine ⟨29177448803834560104508249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38903265071779413472677665 29177448803834560104508249)
  ·
    refine ⟨21883086602875920078381187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29177448803834560104508249 21883086602875920078381187)
    ·
      refine ⟨32824629904313880117571781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21883086602875920078381187 32824629904313880117571781)
      ·
        refine ⟨6154618107058852522044709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32824629904313880117571781 6154618107058852522044709)
        ·
          refine ⟨1153990895073534847883383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6154618107058852522044709 1153990895073534847883383)
          ·
            refine ⟨1730986342610302271825075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1153990895073534847883383 1730986342610302271825075)
            ·
              refine ⟨2596479513915453407737613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1730986342610302271825075 2596479513915453407737613)
              ·
                refine ⟨973679817718295027901605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2596479513915453407737613 973679817718295027901605)
                ·
                  refine ⟨182564965822180317731551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 973679817718295027901605 182564965822180317731551)
                  ·
                    rfl

theorem cell22_1599948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 1, 1, 3, 4].length) (baseStart_1599948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599948 prefixEnd_1599948 := by exact prefixLift 1599948
  have htrace : WordTrace (prefixWord ++ tailWord_1599948) baseStart_1599948 baseEnd_1599948 := by
    simpa [prefixWord, tailWord_1599948, baseEnd_1599948] using wordTrace_append hprefix tailTrace_1599948
  have hstable : (prefixWord ++ tailWord_1599948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599948).length < 2 ^ (prefixWord ++ tailWord_1599948).sum := by decide
  have hdescent : baseEnd_1599948 < baseStart_1599948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1599987 : List Nat := [1, 1, 1, 2, 2, 2, 5, 3, 5]
def baseStart_1599987 : Nat := 118140960795 + 1599987 * 2 ^ 59
def prefixEnd_1599987 : Nat := 4983230072969 + 3 ^ 40 * 1599987 * 2
def baseEnd_1599987 : Nat := 182569415987852617156511

theorem tailTrace_1599987 : CollatzResearch.WordTrace tailWord_1599987 prefixEnd_1599987 182569415987852617156511 := by
  unfold tailWord_1599987
  simp only [CollatzResearch.WordTrace]
  refine ⟨58356320054527829869686215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38904213369685219913124143 58356320054527829869686215)
  ·
    refine ⟨87534480081791744804529323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58356320054527829869686215 87534480081791744804529323)
    ·
      refine ⟨131301720122687617206793985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87534480081791744804529323 131301720122687617206793985)
      ·
        refine ⟨98476290092015712905095489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131301720122687617206793985 98476290092015712905095489)
        ·
          refine ⟨73857217569011784678821617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98476290092015712905095489 73857217569011784678821617)
          ·
            refine ⟨55392913176758838509116213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73857217569011784678821617 55392913176758838509116213)
            ·
              refine ⟨5193085610321141110229645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55392913176758838509116213 5193085610321141110229645)
              ·
                refine ⟨1947407103870427916336117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5193085610321141110229645 1947407103870427916336117)
                ·
                  refine ⟨182569415987852617156511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1947407103870427916336117 182569415987852617156511)
                  ·
                    rfl

theorem cell22_1599987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 5].length) (baseStart_1599987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1599987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1599987 prefixEnd_1599987 := by exact prefixLift 1599987
  have htrace : WordTrace (prefixWord ++ tailWord_1599987) baseStart_1599987 baseEnd_1599987 := by
    simpa [prefixWord, tailWord_1599987, baseEnd_1599987] using wordTrace_append hprefix tailTrace_1599987
  have hstable : (prefixWord ++ tailWord_1599987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1599987).length < 2 ^ (prefixWord ++ tailWord_1599987).sum := by decide
  have hdescent : baseEnd_1599987 < baseStart_1599987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1599987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600036 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 2, 5]
def baseStart_1600036 : Nat := 118140960795 + 1600036 * 2 ^ 59
def prefixEnd_1600036 : Nat := 4983230072969 + 3 ^ 40 * 1600036 * 2
def baseEnd_1600036 : Nat := 547725021664938056994383

theorem tailTrace_1600036 : CollatzResearch.WordTrace tailWord_1600036 prefixEnd_1600036 547725021664938056994383 := by
  unfold tailWord_1600036
  simp only [CollatzResearch.WordTrace]
  refine ⟨29179053615675155619109981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38905404820900207492146641 29179053615675155619109981)
  ·
    refine ⟨10942145105878183357166243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29179053615675155619109981 10942145105878183357166243)
    ·
      refine ⟨16413217658817275035749365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10942145105878183357166243 16413217658817275035749365)
      ·
        refine ⟨1538739155514119534601503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16413217658817275035749365 1538739155514119534601503)
        ·
          refine ⟨2308108733271179301902255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1538739155514119534601503 2308108733271179301902255)
          ·
            refine ⟨3462163099906768952853383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2308108733271179301902255 3462163099906768952853383)
            ·
              refine ⟨5193244649860153429280075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3462163099906768952853383 5193244649860153429280075)
              ·
                refine ⟨7789866974790230143920113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5193244649860153429280075 7789866974790230143920113)
                ·
                  refine ⟨5842400231092672607940085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7789866974790230143920113 5842400231092672607940085)
                  ·
                    refine ⟨547725021664938056994383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5842400231092672607940085 547725021664938056994383)
                    ·
                      rfl

theorem cell22_1600036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_1600036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600036 prefixEnd_1600036 := by exact prefixLift 1600036
  have htrace : WordTrace (prefixWord ++ tailWord_1600036) baseStart_1600036 baseEnd_1600036 := by
    simpa [prefixWord, tailWord_1600036, baseEnd_1600036] using wordTrace_append hprefix tailTrace_1600036
  have hstable : (prefixWord ++ tailWord_1600036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600036).length < 2 ^ (prefixWord ++ tailWord_1600036).sum := by decide
  have hdescent : baseEnd_1600036 < baseStart_1600036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600081 : List Nat := [1, 2, 2, 1, 3, 3, 3, 2, 2, 3]
def baseStart_1600081 : Nat := 118140960795 + 1600081 * 2 ^ 59
def prefixEnd_1600081 : Nat := 4983230072969 + 3 ^ 40 * 1600081 * 2
def baseEnd_1600081 : Nat := 547740426084572939619245

theorem tailTrace_1600081 : CollatzResearch.WordTrace tailWord_1600081 prefixEnd_1600081 547740426084572939619245 := by
  unfold tailWord_1600081
  simp only [CollatzResearch.WordTrace]
  refine ⟨58359748516187283923608097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38906499010791522615738731 58359748516187283923608097)
  ·
    refine ⟨43769811387140462942706073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58359748516187283923608097 43769811387140462942706073)
    ·
      refine ⟨32827358540355347207029555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43769811387140462942706073 32827358540355347207029555)
      ·
        refine ⟨49241037810533020810544333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32827358540355347207029555 49241037810533020810544333)
        ·
          refine ⟨18465389178949882803954125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49241037810533020810544333 18465389178949882803954125)
          ·
            refine ⟨6924520942106206051482797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18465389178949882803954125 6924520942106206051482797)
            ·
              refine ⟨2596695353289827269306049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6924520942106206051482797 2596695353289827269306049)
              ·
                refine ⟨1947521514967370451979537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2596695353289827269306049 1947521514967370451979537)
                ·
                  refine ⟨1460641136225527838984653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1947521514967370451979537 1460641136225527838984653)
                  ·
                    refine ⟨547740426084572939619245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1460641136225527838984653 547740426084572939619245)
                    ·
                      rfl

theorem cell22_1600081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_1600081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600081 prefixEnd_1600081 := by exact prefixLift 1600081
  have htrace : WordTrace (prefixWord ++ tailWord_1600081) baseStart_1600081 baseEnd_1600081 := by
    simpa [prefixWord, tailWord_1600081, baseEnd_1600081] using wordTrace_append hprefix tailTrace_1600081
  have hstable : (prefixWord ++ tailWord_1600081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600081).length < 2 ^ (prefixWord ++ tailWord_1600081).sum := by decide
  have hdescent : baseEnd_1600081 < baseStart_1600081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600156 : List Nat := [2, 2, 3, 2, 2, 2, 1, 3, 5]
def baseStart_1600156 : Nat := 118140960795 + 1600156 * 2 ^ 59
def prefixEnd_1600156 : Nat := 4983230072969 + 3 ^ 40 * 1600156 * 2
def baseEnd_1600156 : Nat := 182588700039099247998005

theorem tailTrace_1600156 : CollatzResearch.WordTrace tailWord_1600156 prefixEnd_1600156 182588700039099247998005 := by
  unfold tailWord_1600156
  simp only [CollatzResearch.WordTrace]
  refine ⟨29181241995457785866294161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38908322660610381155058881 29181241995457785866294161)
  ·
    refine ⟨21885931496593339399720621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29181241995457785866294161 21885931496593339399720621)
    ·
      refine ⟨8207224311222502274895233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21885931496593339399720621 8207224311222502274895233)
      ·
        refine ⟨6155418233416876706171425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8207224311222502274895233 6155418233416876706171425)
        ·
          refine ⟨4616563675062657529628569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6155418233416876706171425 4616563675062657529628569)
          ·
            refine ⟨3462422756296993147221427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4616563675062657529628569 3462422756296993147221427)
            ·
              refine ⟨5193634134445489720832141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3462422756296993147221427 5193634134445489720832141)
              ·
                refine ⟨1947612800417058645312053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5193634134445489720832141 1947612800417058645312053)
                ·
                  refine ⟨182588700039099247998005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1947612800417058645312053 182588700039099247998005)
                  ·
                    rfl

theorem cell22_1600156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 5].length) (baseStart_1600156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600156 prefixEnd_1600156 := by exact prefixLift 1600156
  have htrace : WordTrace (prefixWord ++ tailWord_1600156) baseStart_1600156 baseEnd_1600156 := by
    simpa [prefixWord, tailWord_1600156, baseEnd_1600156] using wordTrace_append hprefix tailTrace_1600156
  have hstable : (prefixWord ++ tailWord_1600156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600156).length < 2 ^ (prefixWord ++ tailWord_1600156).sum := by decide
  have hdescent : baseEnd_1600156 < baseStart_1600156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600216 : List Nat := [2, 1, 2, 2, 3, 3, 2, 1, 1, 5]
def baseStart_1600216 : Nat := 118140960795 + 1600216 * 2 ^ 59
def prefixEnd_1600216 : Nat := 4983230072969 + 3 ^ 40 * 1600216 * 2
def baseEnd_1600216 : Nat := 547786639343477587493831

theorem tailTrace_1600216 : CollatzResearch.WordTrace tailWord_1600216 prefixEnd_1600216 547786639343477587493831 := by
  unfold tailWord_1600216
  simp only [CollatzResearch.WordTrace]
  refine ⟨29182336185349100989886251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38909781580465467986515001 29182336185349100989886251)
  ·
    refine ⟨43773504278023651484829377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29182336185349100989886251 43773504278023651484829377)
    ·
      refine ⟨32830128208517738613622033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43773504278023651484829377 32830128208517738613622033)
      ·
        refine ⟨24622596156388303960216525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32830128208517738613622033 24622596156388303960216525)
        ·
          refine ⟨9233473558645613985081197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24622596156388303960216525 9233473558645613985081197)
          ·
            refine ⟨3462552584492105244405449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9233473558645613985081197 3462552584492105244405449)
            ·
              refine ⟨2596914438369078933304087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3462552584492105244405449 2596914438369078933304087)
              ·
                refine ⟨3895371657553618399956131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2596914438369078933304087 3895371657553618399956131)
                ·
                  refine ⟨5843057486330427599934197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3895371657553618399956131 5843057486330427599934197)
                  ·
                    refine ⟨547786639343477587493831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5843057486330427599934197 547786639343477587493831)
                    ·
                      rfl

theorem cell22_1600216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_1600216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600216 prefixEnd_1600216 := by exact prefixLift 1600216
  have htrace : WordTrace (prefixWord ++ tailWord_1600216) baseStart_1600216 baseEnd_1600216 := by
    simpa [prefixWord, tailWord_1600216, baseEnd_1600216] using wordTrace_append hprefix tailTrace_1600216
  have hstable : (prefixWord ++ tailWord_1600216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600216).length < 2 ^ (prefixWord ++ tailWord_1600216).sum := by decide
  have hdescent : baseEnd_1600216 < baseStart_1600216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600351 : List Nat := [1, 1, 2, 3, 1, 3, 3, 2, 1, 5]
def baseStart_1600351 : Nat := 118140960795 + 1600351 * 2 ^ 59
def prefixEnd_1600351 : Nat := 4983230072969 + 3 ^ 40 * 1600351 * 2
def baseEnd_1600351 : Nat := 547832852602382235368417

theorem tailTrace_1600351 : CollatzResearch.WordTrace tailWord_1600351 prefixEnd_1600351 547832852602382235368417 := by
  unfold tailWord_1600351
  simp only [CollatzResearch.WordTrace]
  refine ⟨58369596225209120035936907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38913064150139413357291271 58369596225209120035936907)
  ·
    refine ⟨87554394337813680053905361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58369596225209120035936907 87554394337813680053905361)
    ·
      refine ⟨65665795753360260040429021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87554394337813680053905361 65665795753360260040429021)
      ·
        refine ⟨24624673407510097515160883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65665795753360260040429021 24624673407510097515160883)
        ·
          refine ⟨36937010111265146272741325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24624673407510097515160883 36937010111265146272741325)
          ·
            refine ⟨13851378791724429852277997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36937010111265146272741325 13851378791724429852277997)
            ·
              refine ⟨5194267046896661194604249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13851378791724429852277997 5194267046896661194604249)
              ·
                refine ⟨3895700285172495895953187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5194267046896661194604249 3895700285172495895953187)
                ·
                  refine ⟨5843550427758743843929781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3895700285172495895953187 5843550427758743843929781)
                  ·
                    refine ⟨547832852602382235368417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5843550427758743843929781 547832852602382235368417)
                    ·
                      rfl

theorem cell22_1600351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 5].length) (baseStart_1600351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600351 prefixEnd_1600351 := by exact prefixLift 1600351
  have htrace : WordTrace (prefixWord ++ tailWord_1600351) baseStart_1600351 baseEnd_1600351 := by
    simpa [prefixWord, tailWord_1600351, baseEnd_1600351] using wordTrace_append hprefix tailTrace_1600351
  have hstable : (prefixWord ++ tailWord_1600351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600351).length < 2 ^ (prefixWord ++ tailWord_1600351).sum := by decide
  have hdescent : baseEnd_1600351 < baseStart_1600351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600355 : List Nat := [1, 1, 1, 5, 3, 2, 3, 1, 1, 4]
def baseStart_1600355 : Nat := 118140960795 + 1600355 * 2 ^ 59
def prefixEnd_1600355 : Nat := 4983230072969 + 3 ^ 40 * 1600355 * 2
def baseEnd_1600355 : Nat := 547834221884127558268405

theorem tailTrace_1600355 : CollatzResearch.WordTrace tailWord_1600355 prefixEnd_1600355 547834221884127558268405 := by
  unfold tailWord_1600355
  simp only [CollatzResearch.WordTrace]
  refine ⟨58369742117194628719082519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38913161411463085812721679 58369742117194628719082519)
  ·
    refine ⟨87554613175791943078623779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58369742117194628719082519 87554613175791943078623779)
    ·
      refine ⟨131331919763687914617935669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87554613175791943078623779 131331919763687914617935669)
      ·
        refine ⟨12312367477845741995431469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131331919763687914617935669 12312367477845741995431469)
        ·
          refine ⟨4617137804192153248286801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12312367477845741995431469 4617137804192153248286801)
          ·
            refine ⟨3462853353144114936215101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4617137804192153248286801 3462853353144114936215101)
            ·
              refine ⟨1298570007429043101080663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3462853353144114936215101 1298570007429043101080663)
              ·
                refine ⟨1947855011143564651620995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298570007429043101080663 1947855011143564651620995)
                ·
                  refine ⟨2921782516715346977431493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1947855011143564651620995 2921782516715346977431493)
                  ·
                    refine ⟨547834221884127558268405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2921782516715346977431493 547834221884127558268405)
                    ·
                      rfl

theorem cell22_1600355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 1, 4].length) (baseStart_1600355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600355 prefixEnd_1600355 := by exact prefixLift 1600355
  have htrace : WordTrace (prefixWord ++ tailWord_1600355) baseStart_1600355 baseEnd_1600355 := by
    simpa [prefixWord, tailWord_1600355, baseEnd_1600355] using wordTrace_append hprefix tailTrace_1600355
  have hstable : (prefixWord ++ tailWord_1600355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600355).length < 2 ^ (prefixWord ++ tailWord_1600355).sum := by decide
  have hdescent : baseEnd_1600355 < baseStart_1600355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600368 : List Nat := [2, 1, 1, 1, 4, 1, 3, 4, 2, 3]
def baseStart_1600368 : Nat := 118140960795 + 1600368 * 2 ^ 59
def prefixEnd_1600368 : Nat := 4983230072969 + 3 ^ 40 * 1600368 * 2
def baseEnd_1600368 : Nat := 547838672049799857693365

theorem tailTrace_1600368 : CollatzResearch.WordTrace tailWord_1600368 prefixEnd_1600368 547838672049799857693365 := by
  unfold tailWord_1600368
  simp only [CollatzResearch.WordTrace]
  refine ⟨29185108133073765969652879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38913477510765021292870505 29185108133073765969652879)
  ·
    refine ⟨43777662199610648954479319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29185108133073765969652879 43777662199610648954479319)
    ·
      refine ⟨65666493299415973431718979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43777662199610648954479319 65666493299415973431718979)
      ·
        refine ⟨98499739949123960147578469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65666493299415973431718979 98499739949123960147578469)
        ·
          refine ⟨18468701240460742527670963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98499739949123960147578469 18468701240460742527670963)
          ·
            refine ⟨27703051860691113791506445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18468701240460742527670963 27703051860691113791506445)
            ·
              refine ⟨10388644447759167671814917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27703051860691113791506445 10388644447759167671814917)
              ·
                refine ⟨1947870833954843938465297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10388644447759167671814917 1947870833954843938465297)
                ·
                  refine ⟨1460903125466132953848973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1947870833954843938465297 1460903125466132953848973)
                  ·
                    refine ⟨547838672049799857693365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1460903125466132953848973 547838672049799857693365)
                    ·
                      rfl

theorem cell22_1600368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 2, 3].length) (baseStart_1600368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600368 prefixEnd_1600368 := by exact prefixLift 1600368
  have htrace : WordTrace (prefixWord ++ tailWord_1600368) baseStart_1600368 baseEnd_1600368 := by
    simpa [prefixWord, tailWord_1600368, baseEnd_1600368] using wordTrace_append hprefix tailTrace_1600368
  have hstable : (prefixWord ++ tailWord_1600368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600368).length < 2 ^ (prefixWord ++ tailWord_1600368).sum := by decide
  have hdescent : baseEnd_1600368 < baseStart_1600368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600370 : List Nat := [3, 2, 1, 2, 1, 1, 6, 2, 4]
def baseStart_1600370 : Nat := 118140960795 + 1600370 * 2 ^ 59
def prefixEnd_1600370 : Nat := 4983230072969 + 3 ^ 40 * 1600370 * 2
def baseEnd_1600370 : Nat := 182613118896890839714453

theorem tailTrace_1600370 : CollatzResearch.WordTrace tailWord_1600370 prefixEnd_1600370 182613118896890839714453 := by
  unfold tailWord_1600370
  simp only [CollatzResearch.WordTrace]
  refine ⟨14592572303035071570219641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38913526141426857520585709 14592572303035071570219641)
  ·
    refine ⟨10944429227276303677664731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14592572303035071570219641 10944429227276303677664731)
    ·
      refine ⟨16416643840914455516497097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10944429227276303677664731 16416643840914455516497097)
      ·
        refine ⟨12312482880685841637372823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16416643840914455516497097 12312482880685841637372823)
        ·
          refine ⟨18468724321028762456059235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12312482880685841637372823 18468724321028762456059235)
          ·
            refine ⟨27703086481543143684088853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18468724321028762456059235 27703086481543143684088853)
            ·
              refine ⟨1298582178822334860191665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27703086481543143684088853 1298582178822334860191665)
              ·
                refine ⟨973936634116751145143749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1298582178822334860191665 973936634116751145143749)
                ·
                  refine ⟨182613118896890839714453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 973936634116751145143749 182613118896890839714453)
                  ·
                    rfl

theorem cell22_1600370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_1600370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600370 prefixEnd_1600370 := by exact prefixLift 1600370
  have htrace : WordTrace (prefixWord ++ tailWord_1600370) baseStart_1600370 baseEnd_1600370 := by
    simpa [prefixWord, tailWord_1600370, baseEnd_1600370] using wordTrace_append hprefix tailTrace_1600370
  have hstable : (prefixWord ++ tailWord_1600370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600370).length < 2 ^ (prefixWord ++ tailWord_1600370).sum := by decide
  have hdescent : baseEnd_1600370 < baseStart_1600370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600381 : List Nat := [1, 4, 1, 1, 2, 1, 5, 7]
def baseStart_1600381 : Nat := 118140960795 + 1600381 * 2 ^ 59
def prefixEnd_1600381 : Nat := 4983230072969 + 3 ^ 40 * 1600381 * 2
def baseEnd_1600381 : Nat := 60871458023941350790925

theorem tailTrace_1600381 : CollatzResearch.WordTrace tailWord_1600381 prefixEnd_1600381 60871458023941350790925 := by
  unfold tailWord_1600381
  simp only [CollatzResearch.WordTrace]
  refine ⟨58370690415100435159528997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38913793610066956773019331 58370690415100435159528997)
  ·
    refine ⟨10944504452831331592411687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58370690415100435159528997 10944504452831331592411687)
    ·
      refine ⟨16416756679246997388617531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10944504452831331592411687 16416756679246997388617531)
      ·
        refine ⟨24625135018870496082926297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16416756679246997388617531 24625135018870496082926297)
        ·
          refine ⟨18468851264152872062194723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24625135018870496082926297 18468851264152872062194723)
          ·
            refine ⟨27703276896229308093292085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18468851264152872062194723 27703276896229308093292085)
            ·
              refine ⟨2597182209021497633746133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27703276896229308093292085 2597182209021497633746133)
              ·
                refine ⟨60871458023941350790925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2597182209021497633746133 60871458023941350790925)
                ·
                  rfl

theorem cell22_1600381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 7].length) (baseStart_1600381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600381 prefixEnd_1600381 := by exact prefixLift 1600381
  have htrace : WordTrace (prefixWord ++ tailWord_1600381) baseStart_1600381 baseEnd_1600381 := by
    simpa [prefixWord, tailWord_1600381, baseEnd_1600381] using wordTrace_append hprefix tailTrace_1600381
  have hstable : (prefixWord ++ tailWord_1600381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600381).length < 2 ^ (prefixWord ++ tailWord_1600381).sum := by decide
  have hdescent : baseEnd_1600381 < baseStart_1600381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600406 : List Nat := [5, 3, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_1600406 : Nat := 118140960795 + 1600406 * 2 ^ 59
def prefixEnd_1600406 : Nat := 4983230072969 + 3 ^ 40 * 1600406 * 2
def baseEnd_1600406 : Nat := 547851680226380425243249

theorem tailTrace_1600406 : CollatzResearch.WordTrace tailWord_1600406 prefixEnd_1600406 547851680226380425243249 := by
  unfold tailWord_1600406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3648225140000616526824317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38914401493339909619459381 3648225140000616526824317)
  ·
    refine ⟨1368084427500231197559119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3648225140000616526824317 1368084427500231197559119)
    ·
      refine ⟨2052126641250346796338679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1368084427500231197559119 2052126641250346796338679)
      ·
        refine ⟨3078189961875520194508019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2052126641250346796338679 3078189961875520194508019)
        ·
          refine ⟨4617284942813280291762029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3078189961875520194508019 4617284942813280291762029)
          ·
            refine ⟨1731481853554980109410761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4617284942813280291762029 1731481853554980109410761)
            ·
              refine ⟨1298611390166235082058071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1731481853554980109410761 1298611390166235082058071)
              ·
                refine ⟨1947917085249352623087107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298611390166235082058071 1947917085249352623087107)
                ·
                  refine ⟨2921875627874028934630661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1947917085249352623087107 2921875627874028934630661)
                  ·
                    refine ⟨547851680226380425243249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2921875627874028934630661 547851680226380425243249)
                    ·
                      rfl

theorem cell22_1600406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_1600406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600406 prefixEnd_1600406 := by exact prefixLift 1600406
  have htrace : WordTrace (prefixWord ++ tailWord_1600406) baseStart_1600406 baseEnd_1600406 := by
    simpa [prefixWord, tailWord_1600406, baseEnd_1600406] using wordTrace_append hprefix tailTrace_1600406
  have hstable : (prefixWord ++ tailWord_1600406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600406).length < 2 ^ (prefixWord ++ tailWord_1600406).sum := by decide
  have hdescent : baseEnd_1600406 < baseStart_1600406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600413 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 5, 3]
def baseStart_1600413 : Nat := 118140960795 + 1600413 * 2 ^ 59
def prefixEnd_1600413 : Nat := 4983230072969 + 3 ^ 40 * 1600413 * 2
def baseEnd_1600413 : Nat := 547854076469434740318227

theorem tailTrace_1600413 : CollatzResearch.WordTrace tailWord_1600413 prefixEnd_1600413 547854076469434740318227 := by
  unfold tailWord_1600413
  simp only [CollatzResearch.WordTrace]
  refine ⟨58371857550984504624693893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38914571700656336416462595 58371857550984504624693893)
  ·
    refine ⟨10944723290809594617130105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58371857550984504624693893 10944723290809594617130105)
    ·
      refine ⟨8208542468107195962847579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10944723290809594617130105 8208542468107195962847579)
      ·
        refine ⟨12312813702160793944271369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8208542468107195962847579 12312813702160793944271369)
        ·
          refine ⟨9234610276620595458203527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12312813702160793944271369 9234610276620595458203527)
          ·
            refine ⟨13851915414930893187305291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9234610276620595458203527 13851915414930893187305291)
            ·
              refine ⟨20777873122396339780957937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13851915414930893187305291 20777873122396339780957937)
              ·
                refine ⟨15583404841797254835718453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20777873122396339780957937 15583404841797254835718453)
                ·
                  refine ⟨1460944203918492640848605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15583404841797254835718453 1460944203918492640848605)
                  ·
                    refine ⟨547854076469434740318227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1460944203918492640848605 547854076469434740318227)
                    ·
                      rfl

theorem cell22_1600413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_1600413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600413 prefixEnd_1600413 := by exact prefixLift 1600413
  have htrace : WordTrace (prefixWord ++ tailWord_1600413) baseStart_1600413 baseEnd_1600413 := by
    simpa [prefixWord, tailWord_1600413, baseEnd_1600413] using wordTrace_append hprefix tailTrace_1600413
  have hstable : (prefixWord ++ tailWord_1600413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600413).length < 2 ^ (prefixWord ++ tailWord_1600413).sum := by decide
  have hdescent : baseEnd_1600413 < baseStart_1600413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600488 : List Nat := [2, 1, 4, 1, 1, 1, 5, 1, 6]
def baseStart_1600488 : Nat := 118140960795 + 1600488 * 2 ^ 59
def prefixEnd_1600488 : Nat := 4983230072969 + 3 ^ 40 * 1600488 * 2
def baseEnd_1600488 : Nat := 182626583500719848230999

theorem tailTrace_1600488 : CollatzResearch.WordTrace tailWord_1600488 prefixEnd_1600488 182626583500719848230999 := by
  unfold tailWord_1600488
  simp only [CollatzResearch.WordTrace]
  refine ⟨29187296512856396216837059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38916395350475194955782745 29187296512856396216837059)
  ·
    refine ⟨43780944769284594325255589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29187296512856396216837059 43780944769284594325255589)
    ·
      refine ⟨8208927144240861435985423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43780944769284594325255589 8208927144240861435985423)
      ·
        refine ⟨12313390716361292153978135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8208927144240861435985423 12313390716361292153978135)
        ·
          refine ⟨18470086074541938230967203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12313390716361292153978135 18470086074541938230967203)
          ·
            refine ⟨27705129111812907346450805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18470086074541938230967203 27705129111812907346450805)
            ·
              refine ⟨2597355854232460063729763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27705129111812907346450805 2597355854232460063729763)
              ·
                refine ⟨3896033781348690095594645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2597355854232460063729763 3896033781348690095594645)
                ·
                  refine ⟨182626583500719848230999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3896033781348690095594645 182626583500719848230999)
                  ·
                    rfl

theorem cell22_1600488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 6].length) (baseStart_1600488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600488 prefixEnd_1600488 := by exact prefixLift 1600488
  have htrace : WordTrace (prefixWord ++ tailWord_1600488) baseStart_1600488 baseEnd_1600488 := by
    simpa [prefixWord, tailWord_1600488, baseEnd_1600488] using wordTrace_append hprefix tailTrace_1600488
  have hstable : (prefixWord ++ tailWord_1600488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600488).length < 2 ^ (prefixWord ++ tailWord_1600488).sum := by decide
  have hdescent : baseEnd_1600488 < baseStart_1600488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600494 : List Nat := [4, 1, 2, 1, 5, 1, 2, 1, 5]
def baseStart_1600494 : Nat := 118140960795 + 1600494 * 2 ^ 59
def prefixEnd_1600494 : Nat := 4983230072969 + 3 ^ 40 * 1600494 * 2
def baseEnd_1600494 : Nat := 182627268141592509680993

theorem tailTrace_1600494 : CollatzResearch.WordTrace tailWord_1600494 prefixEnd_1600494 182627268141592509680993 := by
  unfold tailWord_1600494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7296851482961381932299067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38916541242460703638928357 7296851482961381932299067)
  ·
    refine ⟨10945277224442072898448601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7296851482961381932299067 10945277224442072898448601)
    ·
      refine ⟨8208957918331554673836451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10945277224442072898448601 8208957918331554673836451)
      ·
        refine ⟨12313436877497332010754677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8208957918331554673836451 12313436877497332010754677)
        ·
          refine ⟨1154384707265374876008251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12313436877497332010754677 1154384707265374876008251)
          ·
            refine ⟨1731577060898062314012377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154384707265374876008251 1731577060898062314012377)
            ·
              refine ⟨1298682795673546735509283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1731577060898062314012377 1298682795673546735509283)
              ·
                refine ⟨1948024193510320103263925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298682795673546735509283 1948024193510320103263925)
                ·
                  refine ⟨182627268141592509680993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1948024193510320103263925 182627268141592509680993)
                  ·
                    rfl

theorem cell22_1600494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_1600494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600494 prefixEnd_1600494 := by exact prefixLift 1600494
  have htrace : WordTrace (prefixWord ++ tailWord_1600494) baseStart_1600494 baseEnd_1600494 := by
    simpa [prefixWord, tailWord_1600494, baseEnd_1600494] using wordTrace_append hprefix tailTrace_1600494
  have hstable : (prefixWord ++ tailWord_1600494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600494).length < 2 ^ (prefixWord ++ tailWord_1600494).sum := by decide
  have hdescent : baseEnd_1600494 < baseStart_1600494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600535 : List Nat := [1, 1, 3, 5, 1, 1, 2, 2, 2, 4]
def baseStart_1600535 : Nat := 118140960795 + 1600535 * 2 ^ 59
def prefixEnd_1600535 : Nat := 4983230072969 + 3 ^ 40 * 1600535 * 2
def baseEnd_1600535 : Nat := 547895839562667088767853

theorem tailTrace_1600535 : CollatzResearch.WordTrace tailWord_1600535 prefixEnd_1600535 547895839562667088767853 := by
  unfold tailWord_1600535
  simp only [CollatzResearch.WordTrace]
  refine ⟨58376307256542519460635059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38917538171028346307090039 58376307256542519460635059)
  ·
    refine ⟨87564460884813779190952589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58376307256542519460635059 87564460884813779190952589)
    ·
      refine ⟨32836672831805167196607221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87564460884813779190952589 32836672831805167196607221)
      ·
        refine ⟨3078438077981734424681927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32836672831805167196607221 3078438077981734424681927)
        ·
          refine ⟨4617657116972601637022891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3078438077981734424681927 4617657116972601637022891)
          ·
            refine ⟨6926485675458902455534337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4617657116972601637022891 6926485675458902455534337)
            ·
              refine ⟨5194864256594176841650753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6926485675458902455534337 5194864256594176841650753)
              ·
                refine ⟨3896148192445632631238065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5194864256594176841650753 3896148192445632631238065)
                ·
                  refine ⟨2922111144334224473428549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3896148192445632631238065 2922111144334224473428549)
                  ·
                    refine ⟨547895839562667088767853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2922111144334224473428549 547895839562667088767853)
                    ·
                      rfl

theorem cell22_1600535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 4].length) (baseStart_1600535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600535 prefixEnd_1600535 := by exact prefixLift 1600535
  have htrace : WordTrace (prefixWord ++ tailWord_1600535) baseStart_1600535 baseEnd_1600535 := by
    simpa [prefixWord, tailWord_1600535, baseEnd_1600535] using wordTrace_append hprefix tailTrace_1600535
  have hstable : (prefixWord ++ tailWord_1600535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600535).length < 2 ^ (prefixWord ++ tailWord_1600535).sum := by decide
  have hdescent : baseEnd_1600535 < baseStart_1600535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600593 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 2, 5]
def baseStart_1600593 : Nat := 118140960795 + 1600593 * 2 ^ 59
def prefixEnd_1600593 : Nat := 4983230072969 + 3 ^ 40 * 1600593 * 2
def baseEnd_1600593 : Nat := 547915694147974270817675

theorem tailTrace_1600593 : CollatzResearch.WordTrace tailWord_1600593 prefixEnd_1600593 547915694147974270817675 := by
  unfold tailWord_1600593
  simp only [CollatzResearch.WordTrace]
  refine ⟨58378422690332395366246433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38918948460221596910830955 58378422690332395366246433)
  ·
    refine ⟨43783817017749296524684825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58378422690332395366246433 43783817017749296524684825)
    ·
      refine ⟨32837862763311972393513619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43783817017749296524684825 32837862763311972393513619)
      ·
        refine ⟨49256794144967958590270429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32837862763311972393513619 49256794144967958590270429)
        ·
          refine ⟨18471297804362984471351411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49256794144967958590270429 18471297804362984471351411)
          ·
            refine ⟨27706946706544476707027117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18471297804362984471351411 27706946706544476707027117)
            ·
              refine ⟨10390105014954178765135169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27706946706544476707027117 10390105014954178765135169)
              ·
                refine ⟨7792578761215634073851377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10390105014954178765135169 7792578761215634073851377)
                ·
                  refine ⟨5844434070911725555388533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7792578761215634073851377 5844434070911725555388533)
                  ·
                    refine ⟨547915694147974270817675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5844434070911725555388533 547915694147974270817675)
                    ·
                      rfl

theorem cell22_1600593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_1600593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600593 prefixEnd_1600593 := by exact prefixLift 1600593
  have htrace : WordTrace (prefixWord ++ tailWord_1600593) baseStart_1600593 baseEnd_1600593 := by
    simpa [prefixWord, tailWord_1600593, baseEnd_1600593] using wordTrace_append hprefix tailTrace_1600593
  have hstable : (prefixWord ++ tailWord_1600593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600593).length < 2 ^ (prefixWord ++ tailWord_1600593).sum := by decide
  have hdescent : baseEnd_1600593 < baseStart_1600593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600623 : List Nat := [1, 1, 2, 1, 3, 3, 1, 4, 6]
def baseStart_1600623 : Nat := 118140960795 + 1600623 * 2 ^ 59
def prefixEnd_1600623 : Nat := 4983230072969 + 3 ^ 40 * 1600623 * 2
def baseEnd_1600623 : Nat := 182641987920354730855861

theorem tailTrace_1600623 : CollatzResearch.WordTrace tailWord_1600623 prefixEnd_1600623 182641987920354730855861 := by
  unfold tailWord_1600623
  simp only [CollatzResearch.WordTrace]
  refine ⟨58379516880223710489838523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38919677920149140326559015 58379516880223710489838523)
  ·
    refine ⟨87569275320335565734757785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58379516880223710489838523 87569275320335565734757785)
    ·
      refine ⟨65676956490251674301068339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87569275320335565734757785 65676956490251674301068339)
      ·
        refine ⟨98515434735377511451602509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65676956490251674301068339 98515434735377511451602509)
        ·
          refine ⟨36943288025766566794350941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98515434735377511451602509 36943288025766566794350941)
          ·
            refine ⟨13853733009662462547881603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36943288025766566794350941 13853733009662462547881603)
            ·
              refine ⟨20780599514493693821822405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13853733009662462547881603 20780599514493693821822405)
              ·
                refine ⟨3896362408967567591591701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20780599514493693821822405 3896362408967567591591701)
                ·
                  refine ⟨182641987920354730855861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3896362408967567591591701 182641987920354730855861)
                  ·
                    rfl

theorem cell22_1600623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 6].length) (baseStart_1600623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600623 prefixEnd_1600623 := by exact prefixLift 1600623
  have htrace : WordTrace (prefixWord ++ tailWord_1600623) baseStart_1600623 baseEnd_1600623 := by
    simpa [prefixWord, tailWord_1600623, baseEnd_1600623] using wordTrace_append hprefix tailTrace_1600623
  have hstable : (prefixWord ++ tailWord_1600623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600623).length < 2 ^ (prefixWord ++ tailWord_1600623).sum := by decide
  have hdescent : baseEnd_1600623 < baseStart_1600623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600672 : List Nat := [2, 1, 1, 4, 2, 1, 3, 3, 2, 3]
def baseStart_1600672 : Nat := 118140960795 + 1600672 * 2 ^ 59
def prefixEnd_1600672 : Nat := 4983230072969 + 3 ^ 40 * 1600672 * 2
def baseEnd_1600672 : Nat := 547942737462444398092433

theorem tailTrace_1600672 : CollatzResearch.WordTrace tailWord_1600672 prefixEnd_1600672 547942737462444398092433 := by
  unfold tailWord_1600672
  simp only [CollatzResearch.WordTrace]
  refine ⟨29190652028523095929186135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38920869371364127905581513 29190652028523095929186135)
  ·
    refine ⟨43785978042784643893779203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29190652028523095929186135 43785978042784643893779203)
    ·
      refine ⟨65678967064176965840668805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43785978042784643893779203 65678967064176965840668805)
      ·
        refine ⟨12314806324533181095125401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65678967064176965840668805 12314806324533181095125401)
        ·
          refine ⟨9236104743399885821344051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12314806324533181095125401 9236104743399885821344051)
          ·
            refine ⟨13854157115099828732016077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9236104743399885821344051 13854157115099828732016077)
            ·
              refine ⟨5195308918162435774506029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13854157115099828732016077 5195308918162435774506029)
              ·
                refine ⟨1948240844310913415439761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5195308918162435774506029 1948240844310913415439761)
                ·
                  refine ⟨1461180633233185061579821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1948240844310913415439761 1461180633233185061579821)
                  ·
                    refine ⟨547942737462444398092433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1461180633233185061579821 547942737462444398092433)
                    ·
                      rfl

theorem cell22_1600672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 2, 3].length) (baseStart_1600672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600672 prefixEnd_1600672 := by exact prefixLift 1600672
  have htrace : WordTrace (prefixWord ++ tailWord_1600672) baseStart_1600672 baseEnd_1600672 := by
    simpa [prefixWord, tailWord_1600672, baseEnd_1600672] using wordTrace_append hprefix tailTrace_1600672
  have hstable : (prefixWord ++ tailWord_1600672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600672).length < 2 ^ (prefixWord ++ tailWord_1600672).sum := by decide
  have hdescent : baseEnd_1600672 < baseStart_1600672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600708 : List Nat := [2, 3, 3, 1, 4, 1, 2, 2, 4]
def baseStart_1600708 : Nat := 118140960795 + 1600708 * 2 ^ 59
def prefixEnd_1600708 : Nat := 4983230072969 + 3 ^ 40 * 1600708 * 2
def baseEnd_1600708 : Nat := 182651686999384101397441

theorem tailTrace_1600708 : CollatzResearch.WordTrace tailWord_1600708 prefixEnd_1600708 182651686999384101397441 := by
  unfold tailWord_1600708
  simp only [CollatzResearch.WordTrace]
  refine ⟨29191308542457885003341389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38921744723277180004455185 29191308542457885003341389)
  ·
    refine ⟨10946740703421706876253021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29191308542457885003341389 10946740703421706876253021)
    ·
      refine ⟨4105027763783140078594883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10946740703421706876253021 4105027763783140078594883)
      ·
        refine ⟨6157541645674710117892325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4105027763783140078594883 6157541645674710117892325)
        ·
          refine ⟨1154539058564008147104811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6157541645674710117892325 1154539058564008147104811)
          ·
            refine ⟨1731808587846012220657217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154539058564008147104811 1731808587846012220657217)
            ·
              refine ⟨1298856440884509165492913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1731808587846012220657217 1298856440884509165492913)
              ·
                refine ⟨974142330663381874119685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1298856440884509165492913 974142330663381874119685)
                ·
                  refine ⟨182651686999384101397441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 974142330663381874119685 182651686999384101397441)
                  ·
                    rfl

theorem cell22_1600708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_1600708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600708 prefixEnd_1600708 := by exact prefixLift 1600708
  have htrace : WordTrace (prefixWord ++ tailWord_1600708) baseStart_1600708 baseEnd_1600708 := by
    simpa [prefixWord, tailWord_1600708, baseEnd_1600708] using wordTrace_append hprefix tailTrace_1600708
  have hstable : (prefixWord ++ tailWord_1600708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600708).length < 2 ^ (prefixWord ++ tailWord_1600708).sum := by decide
  have hdescent : baseEnd_1600708 < baseStart_1600708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600713 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 11]
def baseStart_1600713 : Nat := 118140960795 + 1600713 * 2 ^ 59
def prefixEnd_1600713 : Nat := 4983230072969 + 3 ^ 40 * 1600713 * 2
def baseEnd_1600713 : Nat := 182652257533444652605769

theorem tailTrace_1600713 : CollatzResearch.WordTrace tailWord_1600713 prefixEnd_1600713 182652257533444652605769 := by
  unfold tailWord_1600713
  simp only [CollatzResearch.WordTrace]
  refine ⟨58382799449897655860614793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38921866299931770573743195 58382799449897655860614793)
  ·
    refine ⟨43787099587423241895461095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58382799449897655860614793 43787099587423241895461095)
    ·
      refine ⟨65680649381134862843191643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43787099587423241895461095 65680649381134862843191643)
      ·
        refine ⟨98520974071702294264787465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65680649381134862843191643 98520974071702294264787465)
        ·
          refine ⟨73890730553776720698590599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98520974071702294264787465 73890730553776720698590599)
          ·
            refine ⟨110836095830665081047885899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73890730553776720698590599 110836095830665081047885899)
            ·
              refine ⟨166254143745997621571828849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110836095830665081047885899 166254143745997621571828849)
              ·
                refine ⟨124690607809498216178871637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166254143745997621571828849 124690607809498216178871637)
                ·
                  refine ⟨182652257533444652605769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 124690607809498216178871637 182652257533444652605769)
                  ·
                    rfl

theorem cell22_1600713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 11].length) (baseStart_1600713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600713 prefixEnd_1600713 := by exact prefixLift 1600713
  have htrace : WordTrace (prefixWord ++ tailWord_1600713) baseStart_1600713 baseEnd_1600713 := by
    simpa [prefixWord, tailWord_1600713, baseEnd_1600713] using wordTrace_append hprefix tailTrace_1600713
  have hstable : (prefixWord ++ tailWord_1600713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600713).length < 2 ^ (prefixWord ++ tailWord_1600713).sum := by decide
  have hdescent : baseEnd_1600713 < baseStart_1600713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600751 : List Nat := [1, 1, 2, 1, 7, 1, 2, 3, 1, 3]
def baseStart_1600751 : Nat := 118140960795 + 1600751 * 2 ^ 59
def prefixEnd_1600751 : Nat := 4983230072969 + 3 ^ 40 * 1600751 * 2
def baseEnd_1600751 : Nat := 547969780776914525367191

theorem tailTrace_1600751 : CollatzResearch.WordTrace tailWord_1600751 prefixEnd_1600751 547969780776914525367191 := by
  unfold tailWord_1600751
  simp only [CollatzResearch.WordTrace]
  refine ⟨58384185423759988350498107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38922790282506658900332071 58384185423759988350498107)
  ·
    refine ⟨87576278135639982525747161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58384185423759988350498107 87576278135639982525747161)
    ·
      refine ⟨65682208601729986894310371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87576278135639982525747161 65682208601729986894310371)
      ·
        refine ⟨98523312902594980341465557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65682208601729986894310371 98523312902594980341465557)
        ·
          refine ⟨2309140146154569851753099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 98523312902594980341465557 2309140146154569851753099)
          ·
            refine ⟨3463710219231854777629649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2309140146154569851753099 3463710219231854777629649)
            ·
              refine ⟨2597782664423891083222237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3463710219231854777629649 2597782664423891083222237)
              ·
                refine ⟨974168499158959156208339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2597782664423891083222237 974168499158959156208339)
                ·
                  refine ⟨1461252748738438734312509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974168499158959156208339 1461252748738438734312509)
                  ·
                    refine ⟨547969780776914525367191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1461252748738438734312509 547969780776914525367191)
                    ·
                      rfl

theorem cell22_1600751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 1, 3].length) (baseStart_1600751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600751 prefixEnd_1600751 := by exact prefixLift 1600751
  have htrace : WordTrace (prefixWord ++ tailWord_1600751) baseStart_1600751 baseEnd_1600751 := by
    simpa [prefixWord, tailWord_1600751, baseEnd_1600751] using wordTrace_append hprefix tailTrace_1600751
  have hstable : (prefixWord ++ tailWord_1600751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600751).length < 2 ^ (prefixWord ++ tailWord_1600751).sum := by decide
  have hdescent : baseEnd_1600751 < baseStart_1600751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600764 : List Nat := [2, 2, 2, 1, 5, 2, 1, 2, 5]
def baseStart_1600764 : Nat := 118140960795 + 1600764 * 2 ^ 59
def prefixEnd_1600764 : Nat := 4983230072969 + 3 ^ 40 * 1600764 * 2
def baseEnd_1600764 : Nat := 182658076980862274930717

theorem tailTrace_1600764 : CollatzResearch.WordTrace tailWord_1600764 prefixEnd_1600764 182658076980862274930717 := by
  unfold tailWord_1600764
  simp only [CollatzResearch.WordTrace]
  refine ⟨29192329786356445785360673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38923106381808594380480897 29192329786356445785360673)
  ·
    refine ⟨21894247339767334339020505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29192329786356445785360673 21894247339767334339020505)
    ·
      refine ⟨16420685504825500754265379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21894247339767334339020505 16420685504825500754265379)
      ·
        refine ⟨24631028257238251131398069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16420685504825500754265379 24631028257238251131398069)
        ·
          refine ⟨2309158899116086043568569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24631028257238251131398069 2309158899116086043568569)
          ·
            refine ⟨1731869174337064532676427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2309158899116086043568569 1731869174337064532676427)
            ·
              refine ⟨2597803761505596799014641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1731869174337064532676427 2597803761505596799014641)
              ·
                refine ⟨1948352821129197599260981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2597803761505596799014641 1948352821129197599260981)
                ·
                  refine ⟨182658076980862274930717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1948352821129197599260981 182658076980862274930717)
                  ·
                    rfl

theorem cell22_1600764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_1600764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600764 prefixEnd_1600764 := by exact prefixLift 1600764
  have htrace : WordTrace (prefixWord ++ tailWord_1600764) baseStart_1600764 baseEnd_1600764 := by
    simpa [prefixWord, tailWord_1600764, baseEnd_1600764] using wordTrace_append hprefix tailTrace_1600764
  have hstable : (prefixWord ++ tailWord_1600764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600764).length < 2 ^ (prefixWord ++ tailWord_1600764).sum := by decide
  have hdescent : baseEnd_1600764 < baseStart_1600764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600794 : List Nat := [3, 1, 1, 3, 3, 2, 2, 2, 1, 4]
def baseStart_1600794 : Nat := 118140960795 + 1600794 * 2 ^ 59
def prefixEnd_1600794 : Nat := 4983230072969 + 3 ^ 40 * 1600794 * 2
def baseEnd_1600794 : Nat := 547984500555676746542059

theorem tailTrace_1600794 : CollatzResearch.WordTrace tailWord_1600794 prefixEnd_1600794 547984500555676746542059 := by
  unfold tailWord_1600794
  simp only [CollatzResearch.WordTrace]
  refine ⟨14596438440651051673578359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38923835841736137796208957 14596438440651051673578359)
  ·
    refine ⟨21894657660976577510367539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14596438440651051673578359 21894657660976577510367539)
    ·
      refine ⟨32841986491464866265551309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21894657660976577510367539 32841986491464866265551309)
      ·
        refine ⟨12315744934299324849581741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32841986491464866265551309 12315744934299324849581741)
        ·
          refine ⟨4618404350362246818593153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12315744934299324849581741 4618404350362246818593153)
          ·
            refine ⟨3463803262771685113944865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4618404350362246818593153 3463803262771685113944865)
            ·
              refine ⟨2597852447078763835458649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3463803262771685113944865 2597852447078763835458649)
              ·
                refine ⟨1948389335309072876593987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2597852447078763835458649 1948389335309072876593987)
                ·
                  refine ⟨2922584002963609314890981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1948389335309072876593987 2922584002963609314890981)
                  ·
                    refine ⟨547984500555676746542059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2922584002963609314890981 547984500555676746542059)
                    ·
                      rfl

theorem cell22_1600794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_1600794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600794 prefixEnd_1600794 := by exact prefixLift 1600794
  have htrace : WordTrace (prefixWord ++ tailWord_1600794) baseStart_1600794 baseEnd_1600794 := by
    simpa [prefixWord, tailWord_1600794, baseEnd_1600794] using wordTrace_append hprefix tailTrace_1600794
  have hstable : (prefixWord ++ tailWord_1600794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600794).length < 2 ^ (prefixWord ++ tailWord_1600794).sum := by decide
  have hdescent : baseEnd_1600794 < baseStart_1600794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600845 : List Nat := [1, 6, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_1600845 : Nat := 118140960795 + 1600845 * 2 ^ 59
def prefixEnd_1600845 : Nat := 4983230072969 + 3 ^ 40 * 1600845 * 2
def baseEnd_1600845 : Nat := 548001958897929613516903

theorem tailTrace_1600845 : CollatzResearch.WordTrace tailWord_1600845 prefixEnd_1600845 548001958897929613516903 := by
  unfold tailWord_1600845
  simp only [CollatzResearch.WordTrace]
  refine ⟨58387613885419442404419989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38925075923612961602946659 58387613885419442404419989)
  ·
    refine ⟨2736919400879036362707187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58387613885419442404419989 2736919400879036362707187)
    ·
      refine ⟨4105379101318554544060781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2736919400879036362707187 4105379101318554544060781)
      ·
        refine ⟨1539517162994457954022793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4105379101318554544060781 1539517162994457954022793)
        ·
          refine ⟨1154637872245843465517095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1539517162994457954022793 1154637872245843465517095)
          ·
            refine ⟨1731956808368765198275643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1154637872245843465517095 1731956808368765198275643)
            ·
              refine ⟨2597935212553147797413465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1731956808368765198275643 2597935212553147797413465)
              ·
                refine ⟨1948451409414860848060099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2597935212553147797413465 1948451409414860848060099)
                ·
                  refine ⟨2922677114122291272090149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1948451409414860848060099 2922677114122291272090149)
                  ·
                    refine ⟨548001958897929613516903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2922677114122291272090149 548001958897929613516903)
                    ·
                      rfl

theorem cell22_1600845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_1600845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600845 prefixEnd_1600845 := by exact prefixLift 1600845
  have htrace : WordTrace (prefixWord ++ tailWord_1600845) baseStart_1600845 baseEnd_1600845 := by
    simpa [prefixWord, tailWord_1600845, baseEnd_1600845] using wordTrace_append hprefix tailTrace_1600845
  have hstable : (prefixWord ++ tailWord_1600845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600845).length < 2 ^ (prefixWord ++ tailWord_1600845).sum := by decide
  have hdescent : baseEnd_1600845 < baseStart_1600845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600865 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 9]
def baseStart_1600865 : Nat := 118140960795 + 1600865 * 2 ^ 59
def prefixEnd_1600865 : Nat := 4983230072969 + 3 ^ 40 * 1600865 * 2
def baseEnd_1600865 : Nat := 182669601768885409338947

theorem tailTrace_1600865 : CollatzResearch.WordTrace tailWord_1600865 prefixEnd_1600865 182669601768885409338947 := by
  unfold tailWord_1600865
  simp only [CollatzResearch.WordTrace]
  refine ⟨58388343345346985820148049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38925562230231323880098699 58388343345346985820148049)
  ·
    refine ⟨43791257509010239365111037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58388343345346985820148049 43791257509010239365111037)
    ·
      refine ⟨16421721565878839761916639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43791257509010239365111037 16421721565878839761916639)
      ·
        refine ⟨24632582348818259642874959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16421721565878839761916639 24632582348818259642874959)
        ·
          refine ⟨36948873523227389464312439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24632582348818259642874959 36948873523227389464312439)
          ·
            refine ⟨55423310284841084196468659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36948873523227389464312439 55423310284841084196468659)
            ·
              refine ⟨83134965427261626294702989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55423310284841084196468659 83134965427261626294702989)
              ·
                refine ⟨31175612035223109860513621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83134965427261626294702989 31175612035223109860513621)
                ·
                  refine ⟨182669601768885409338947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31175612035223109860513621 182669601768885409338947)
                  ·
                    rfl

theorem cell22_1600865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 9].length) (baseStart_1600865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600865 prefixEnd_1600865 := by exact prefixLift 1600865
  have htrace : WordTrace (prefixWord ++ tailWord_1600865) baseStart_1600865 baseEnd_1600865 := by
    simpa [prefixWord, tailWord_1600865, baseEnd_1600865] using wordTrace_append hprefix tailTrace_1600865
  have hstable : (prefixWord ++ tailWord_1600865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600865).length < 2 ^ (prefixWord ++ tailWord_1600865).sum := by decide
  have hdescent : baseEnd_1600865 < baseStart_1600865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600895 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 1, 10]
def baseStart_1600895 : Nat := 118140960795 + 1600895 * 2 ^ 59
def prefixEnd_1600895 : Nat := 4983230072969 + 3 ^ 40 * 1600895 * 2
def baseEnd_1600895 : Nat := 548019074919746149766749

theorem tailTrace_1600895 : CollatzResearch.WordTrace tailWord_1600895 prefixEnd_1600895 548019074919746149766749 := by
  unfold tailWord_1600895
  simp only [CollatzResearch.WordTrace]
  refine ⟨58389437535238300943740139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38926291690158867295826759 58389437535238300943740139)
  ·
    refine ⟨87584156302857451415610209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58389437535238300943740139 87584156302857451415610209)
    ·
      refine ⟨65688117227143088561707657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87584156302857451415610209 65688117227143088561707657)
      ·
        refine ⟨49266087920357316421280743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65688117227143088561707657 49266087920357316421280743)
        ·
          refine ⟨73899131880535974631921115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49266087920357316421280743 73899131880535974631921115)
          ·
            refine ⟨110848697820803961947881673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73899131880535974631921115 110848697820803961947881673)
            ·
              refine ⟨83136523365602971460911255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110848697820803961947881673 83136523365602971460911255)
              ·
                refine ⟨124704785048404457191366883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83136523365602971460911255 124704785048404457191366883)
                ·
                  refine ⟨187057177572606685787050325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124704785048404457191366883 187057177572606685787050325)
                  ·
                    refine ⟨548019074919746149766749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 187057177572606685787050325 548019074919746149766749)
                    ·
                      rfl

theorem cell22_1600895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_1600895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600895 prefixEnd_1600895 := by exact prefixLift 1600895
  have htrace : WordTrace (prefixWord ++ tailWord_1600895) baseStart_1600895 baseEnd_1600895 := by
    simpa [prefixWord, tailWord_1600895, baseEnd_1600895] using wordTrace_append hprefix tailTrace_1600895
  have hstable : (prefixWord ++ tailWord_1600895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600895).length < 2 ^ (prefixWord ++ tailWord_1600895).sum := by decide
  have hdescent : baseEnd_1600895 < baseStart_1600895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600957 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_1600957 : Nat := 118140960795 + 1600957 * 2 ^ 59
def prefixEnd_1600957 : Nat := 4983230072969 + 3 ^ 40 * 1600957 * 2
def baseEnd_1600957 : Nat := 548040298786798654716559

theorem tailTrace_1600957 : CollatzResearch.WordTrace tailWord_1600957 prefixEnd_1600957 548040298786798654716559 := by
  unfold tailWord_1600957
  simp only [CollatzResearch.WordTrace]
  refine ⟨58391698861013685532497125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38927799240675790354998083 58391698861013685532497125)
  ·
    refine ⟨10948443536440066037343211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58391698861013685532497125 10948443536440066037343211)
    ·
      refine ⟨16422665304660099056014817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10948443536440066037343211 16422665304660099056014817)
      ·
        refine ⟨12316998978495074292011113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16422665304660099056014817 12316998978495074292011113)
        ·
          refine ⟨9237749233871305719008335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12316998978495074292011113 9237749233871305719008335)
          ·
            refine ⟨13856623850806958578512503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9237749233871305719008335 13856623850806958578512503)
            ·
              refine ⟨20784935776210437867768755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13856623850806958578512503 20784935776210437867768755)
              ·
                refine ⟨31177403664315656801653133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20784935776210437867768755 31177403664315656801653133)
                ·
                  refine ⟨11691526374118371300619925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31177403664315656801653133 11691526374118371300619925)
                  ·
                    refine ⟨548040298786798654716559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11691526374118371300619925 548040298786798654716559)
                    ·
                      rfl

theorem cell22_1600957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_1600957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600957 prefixEnd_1600957 := by exact prefixLift 1600957
  have htrace : WordTrace (prefixWord ++ tailWord_1600957) baseStart_1600957 baseEnd_1600957 := by
    simpa [prefixWord, tailWord_1600957, baseEnd_1600957] using wordTrace_append hprefix tailTrace_1600957
  have hstable : (prefixWord ++ tailWord_1600957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600957).length < 2 ^ (prefixWord ++ tailWord_1600957).sum := by decide
  have hdescent : baseEnd_1600957 < baseStart_1600957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600959 : List Nat := [1, 1, 2, 2, 2, 1, 1, 7, 2, 3]
def baseStart_1600959 : Nat := 118140960795 + 1600959 * 2 ^ 59
def prefixEnd_1600959 : Nat := 4983230072969 + 3 ^ 40 * 1600959 * 2
def baseEnd_1600959 : Nat := 548040983427671316166553

theorem tailTrace_1600959 : CollatzResearch.WordTrace tailWord_1600959 prefixEnd_1600959 548040983427671316166553 := by
  unfold tailWord_1600959
  simp only [CollatzResearch.WordTrace]
  refine ⟨58391771807006439874069931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38927847871337626582713287 58391771807006439874069931)
  ·
    refine ⟨87587657710509659811104897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58391771807006439874069931 87587657710509659811104897)
    ·
      refine ⟨65690743282882244858328673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87587657710509659811104897 65690743282882244858328673)
      ·
        refine ⟨49268057462161683643746505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65690743282882244858328673 49268057462161683643746505)
        ·
          refine ⟨36951043096621262732809879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49268057462161683643746505 36951043096621262732809879)
          ·
            refine ⟨55426564644931894099214819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36951043096621262732809879 55426564644931894099214819)
            ·
              refine ⟨83139846967397841148822229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55426564644931894099214819 83139846967397841148822229)
              ·
                refine ⟨1948590163298386901925521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 83139846967397841148822229 1948590163298386901925521)
                ·
                  refine ⟨1461442622473790176444141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1948590163298386901925521 1461442622473790176444141)
                  ·
                    refine ⟨548040983427671316166553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1461442622473790176444141 548040983427671316166553)
                    ·
                      rfl

theorem cell22_1600959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 3].length) (baseStart_1600959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600959 prefixEnd_1600959 := by exact prefixLift 1600959
  have htrace : WordTrace (prefixWord ++ tailWord_1600959) baseStart_1600959 baseEnd_1600959 := by
    simpa [prefixWord, tailWord_1600959, baseEnd_1600959] using wordTrace_append hprefix tailTrace_1600959
  have hstable : (prefixWord ++ tailWord_1600959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600959).length < 2 ^ (prefixWord ++ tailWord_1600959).sum := by decide
  have hdescent : baseEnd_1600959 < baseStart_1600959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1600989 : List Nat := [1, 4, 3, 1, 1, 4, 8]
def baseStart_1600989 : Nat := 118140960795 + 1600989 * 2 ^ 59
def prefixEnd_1600989 : Nat := 4983230072969 + 3 ^ 40 * 1600989 * 2
def baseEnd_1600989 : Nat := 20298194557065231033943

theorem tailTrace_1600989 : CollatzResearch.WordTrace tailWord_1600989 prefixEnd_1600989 20298194557065231033943 := by
  unfold tailWord_1600989
  simp only [CollatzResearch.WordTrace]
  refine ⟨58392865996897754997662021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38928577331265169998441347 58392865996897754997662021)
  ·
    refine ⟨10948662374418329062061629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58392865996897754997662021 10948662374418329062061629)
    ·
      refine ⟨4105748390406873398273111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10948662374418329062061629 4105748390406873398273111)
      ·
        refine ⟨6158622585610310097409667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4105748390406873398273111 6158622585610310097409667)
        ·
          refine ⟨9237933878415465146114501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6158622585610310097409667 9237933878415465146114501)
          ·
            refine ⟨1732112602202899714896469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9237933878415465146114501 1732112602202899714896469)
            ·
              refine ⟨20298194557065231033943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1732112602202899714896469 20298194557065231033943)
              ·
                rfl

theorem cell22_1600989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 8].length) (baseStart_1600989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1600989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1600989 prefixEnd_1600989 := by exact prefixLift 1600989
  have htrace : WordTrace (prefixWord ++ tailWord_1600989) baseStart_1600989 baseEnd_1600989 := by
    simpa [prefixWord, tailWord_1600989, baseEnd_1600989] using wordTrace_append hprefix tailTrace_1600989
  have hstable : (prefixWord ++ tailWord_1600989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1600989).length < 2 ^ (prefixWord ++ tailWord_1600989).sum := by decide
  have hdescent : baseEnd_1600989 < baseStart_1600989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1600989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601004 : List Nat := [2, 2, 1, 1, 2, 1, 2, 5, 3, 3]
def baseStart_1601004 : Nat := 118140960795 + 1601004 * 2 ^ 59
def prefixEnd_1601004 : Nat := 4983230072969 + 3 ^ 40 * 1601004 * 2
def baseEnd_1601004 : Nat := 548056387847306198791415

theorem tailTrace_1601004 : CollatzResearch.WordTrace tailWord_1601004 prefixEnd_1601004 548056387847306198791415 := by
  unfold tailWord_1601004
  simp only [CollatzResearch.WordTrace]
  refine ⟨29196706545921706279729033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38928942061228941706305377 29196706545921706279729033)
  ·
    refine ⟨21897529909441279709796775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29196706545921706279729033 21897529909441279709796775)
    ·
      refine ⟨32846294864161919564695163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21897529909441279709796775 32846294864161919564695163)
      ·
        refine ⟨49269442296242879347042745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32846294864161919564695163 49269442296242879347042745)
        ·
          refine ⟨36952081722182159510282059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49269442296242879347042745 36952081722182159510282059)
          ·
            refine ⟨55428122583273239265423089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36952081722182159510282059 55428122583273239265423089)
            ·
              refine ⟨41571091937454929449067317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55428122583273239265423089 41571091937454929449067317)
              ·
                refine ⟨3897289869136399635850061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41571091937454929449067317 3897289869136399635850061)
                ·
                  refine ⟨1461483700926149863443773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3897289869136399635850061 1461483700926149863443773)
                  ·
                    refine ⟨548056387847306198791415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1461483700926149863443773 548056387847306198791415)
                    ·
                      rfl

theorem cell22_1601004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 3].length) (baseStart_1601004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601004 prefixEnd_1601004 := by exact prefixLift 1601004
  have htrace : WordTrace (prefixWord ++ tailWord_1601004) baseStart_1601004 baseEnd_1601004 := by
    simpa [prefixWord, tailWord_1601004, baseEnd_1601004] using wordTrace_append hprefix tailTrace_1601004
  have hstable : (prefixWord ++ tailWord_1601004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601004).length < 2 ^ (prefixWord ++ tailWord_1601004).sum := by decide
  have hdescent : baseEnd_1601004 < baseStart_1601004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601010 : List Nat := [3, 2, 1, 4, 1, 3, 2, 1, 2, 3]
def baseStart_1601010 : Nat := 118140960795 + 1601010 * 2 ^ 59
def prefixEnd_1601010 : Nat := 4983230072969 + 3 ^ 40 * 1601010 * 2
def baseEnd_1601010 : Nat := 548058441769924183141397

theorem tailTrace_1601010 : CollatzResearch.WordTrace tailWord_1601010 prefixEnd_1601010 548058441769924183141397 := by
  unfold tailWord_1601010
  simp only [CollatzResearch.WordTrace]
  refine ⟨14598407982455418896044121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38929087953214450389450989 14598407982455418896044121)
  ·
    refine ⟨10948805986841564172033091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14598407982455418896044121 10948805986841564172033091)
    ·
      refine ⟨16423208980262346258049637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10948805986841564172033091 16423208980262346258049637)
      ·
        refine ⟨3079351683799189923384307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16423208980262346258049637 3079351683799189923384307)
        ·
          refine ⟨4619027525698784885076461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3079351683799189923384307 4619027525698784885076461)
          ·
            refine ⟨1732135322137044331903673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4619027525698784885076461 1732135322137044331903673)
            ·
              refine ⟨1299101491602783248927755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1732135322137044331903673 1299101491602783248927755)
              ·
                refine ⟨1948652237404174873391633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1299101491602783248927755 1948652237404174873391633)
                ·
                  refine ⟨1461489178053131155043725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1948652237404174873391633 1461489178053131155043725)
                  ·
                    refine ⟨548058441769924183141397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1461489178053131155043725 548058441769924183141397)
                    ·
                      rfl

theorem cell22_1601010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_1601010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601010 prefixEnd_1601010 := by exact prefixLift 1601010
  have htrace : WordTrace (prefixWord ++ tailWord_1601010) baseStart_1601010 baseEnd_1601010 := by
    simpa [prefixWord, tailWord_1601010, baseEnd_1601010] using wordTrace_append hprefix tailTrace_1601010
  have hstable : (prefixWord ++ tailWord_1601010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601010).length < 2 ^ (prefixWord ++ tailWord_1601010).sum := by decide
  have hdescent : baseEnd_1601010 < baseStart_1601010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601079 : List Nat := [1, 1, 3, 1, 2, 5, 1, 2, 6]
def baseStart_1601079 : Nat := 118140960795 + 1601079 * 2 ^ 59
def prefixEnd_1601079 : Nat := 4983230072969 + 3 ^ 40 * 1601079 * 2
def baseEnd_1601079 : Nat := 182694020626677001055395

theorem tailTrace_1601079 : CollatzResearch.WordTrace tailWord_1601079 prefixEnd_1601079 182694020626677001055395 := by
  unfold tailWord_1601079
  simp only [CollatzResearch.WordTrace]
  refine ⟨58396148566571700368438291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38930765711047800245625527 58396148566571700368438291)
  ·
    refine ⟨87594222849857550552657437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58396148566571700368438291 87594222849857550552657437)
    ·
      refine ⟨32847833568696581457246539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87594222849857550552657437 32847833568696581457246539)
      ·
        refine ⟨49271750353044872185869809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32847833568696581457246539 49271750353044872185869809)
        ·
          refine ⟨36953812764783654139402357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49271750353044872185869809 36953812764783654139402357)
          ·
            refine ⟨3464419946698467575568971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36953812764783654139402357 3464419946698467575568971)
            ·
              refine ⟨5196629920047701363353457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3464419946698467575568971 5196629920047701363353457)
              ·
                refine ⟨3897472440035776022515093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5196629920047701363353457 3897472440035776022515093)
                ·
                  refine ⟨182694020626677001055395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3897472440035776022515093 182694020626677001055395)
                  ·
                    rfl

theorem cell22_1601079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 6].length) (baseStart_1601079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601079 prefixEnd_1601079 := by exact prefixLift 1601079
  have htrace : WordTrace (prefixWord ++ tailWord_1601079) baseStart_1601079 baseEnd_1601079 := by
    simpa [prefixWord, tailWord_1601079, baseEnd_1601079] using wordTrace_append hprefix tailTrace_1601079
  have hstable : (prefixWord ++ tailWord_1601079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601079).length < 2 ^ (prefixWord ++ tailWord_1601079).sum := by decide
  have hdescent : baseEnd_1601079 < baseStart_1601079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601109 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 4, 4]
def baseStart_1601109 : Nat := 118140960795 + 1601109 * 2 ^ 59
def prefixEnd_1601109 : Nat := 4983230072969 + 3 ^ 40 * 1601109 * 2
def baseEnd_1601109 : Nat := 548092331493120924916093

theorem tailTrace_1601109 : CollatzResearch.WordTrace tailWord_1601109 prefixEnd_1601109 548092331493120924916093 := by
  unfold tailWord_1601109
  simp only [CollatzResearch.WordTrace]
  refine ⟨58397242756463015492030381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38931495170975343661353587 58397242756463015492030381)
  ·
    refine ⟨21898966033673630809511393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58397242756463015492030381 21898966033673630809511393)
    ·
      refine ⟨16424224525255223107133545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21898966033673630809511393 16424224525255223107133545)
      ·
        refine ⟨12318168393941417330350159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16424224525255223107133545 12318168393941417330350159)
        ·
          refine ⟨18477252590912125995525239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12318168393941417330350159 18477252590912125995525239)
          ·
            refine ⟨27715878886368188993287859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18477252590912125995525239 27715878886368188993287859)
            ·
              refine ⟨41573818329552283489931789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27715878886368188993287859 41573818329552283489931789)
              ·
                refine ⟨15590181873582106308724421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41573818329552283489931789 15590181873582106308724421)
                ·
                  refine ⟨2923159101296644932885829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15590181873582106308724421 2923159101296644932885829)
                  ·
                    refine ⟨548092331493120924916093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2923159101296644932885829 548092331493120924916093)
                    ·
                      rfl

theorem cell22_1601109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 4].length) (baseStart_1601109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601109 prefixEnd_1601109 := by exact prefixLift 1601109
  have htrace : WordTrace (prefixWord ++ tailWord_1601109) baseStart_1601109 baseEnd_1601109 := by
    simpa [prefixWord, tailWord_1601109, baseEnd_1601109] using wordTrace_append hprefix tailTrace_1601109
  have hstable : (prefixWord ++ tailWord_1601109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601109).length < 2 ^ (prefixWord ++ tailWord_1601109).sum := by decide
  have hdescent : baseEnd_1601109 < baseStart_1601109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601111 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 4, 3]
def baseStart_1601111 : Nat := 118140960795 + 1601111 * 2 ^ 59
def prefixEnd_1601111 : Nat := 4983230072969 + 3 ^ 40 * 1601111 * 2
def baseEnd_1601111 : Nat := 548093016133993586366087

theorem tailTrace_1601111 : CollatzResearch.WordTrace tailWord_1601111 prefixEnd_1601111 548093016133993586366087 := by
  unfold tailWord_1601111
  simp only [CollatzResearch.WordTrace]
  refine ⟨58397315702455769833603187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38931543801637179889068791 58397315702455769833603187)
  ·
    refine ⟨87595973553683654750404781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58397315702455769833603187 87595973553683654750404781)
    ·
      refine ⟨32848490082631370531401793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87595973553683654750404781 32848490082631370531401793)
      ·
        refine ⟨24636367561973527898551345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32848490082631370531401793 24636367561973527898551345)
        ·
          refine ⟨18477275671480145923913509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24636367561973527898551345 18477275671480145923913509)
          ·
            refine ⟨3464489188402527360733783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18477275671480145923913509 3464489188402527360733783)
            ·
              refine ⟨5196733782603791041100675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3464489188402527360733783 5196733782603791041100675)
              ·
                refine ⟨7795100673905686561651013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5196733782603791041100675 7795100673905686561651013)
                ·
                  refine ⟨1461581376357316230309565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7795100673905686561651013 1461581376357316230309565)
                  ·
                    refine ⟨548093016133993586366087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1461581376357316230309565 548093016133993586366087)
                    ·
                      rfl

theorem cell22_1601111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_1601111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601111 prefixEnd_1601111 := by exact prefixLift 1601111
  have htrace : WordTrace (prefixWord ++ tailWord_1601111) baseStart_1601111 baseEnd_1601111 := by
    simpa [prefixWord, tailWord_1601111, baseEnd_1601111] using wordTrace_append hprefix tailTrace_1601111
  have hstable : (prefixWord ++ tailWord_1601111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601111).length < 2 ^ (prefixWord ++ tailWord_1601111).sum := by decide
  have hdescent : baseEnd_1601111 < baseStart_1601111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601128 : List Nat := [2, 1, 4, 3, 1, 3, 1, 1, 1, 5]
def baseStart_1601128 : Nat := 118140960795 + 1601128 * 2 ^ 59
def prefixEnd_1601128 : Nat := 4983230072969 + 3 ^ 40 * 1601128 * 2
def baseEnd_1601128 : Nat := 548098835581411208691035

theorem tailTrace_1601128 : CollatzResearch.WordTrace tailWord_1601128 prefixEnd_1601128 548098835581411208691035 := by
  unfold tailWord_1601128
  simp only [CollatzResearch.WordTrace]
  refine ⟨29198967871697090868486019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38931957162262787824648025 29198967871697090868486019)
  ·
    refine ⟨43798451807545636302729029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29198967871697090868486019 43798451807545636302729029)
    ·
      refine ⟨8212209713914806806761693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43798451807545636302729029 8212209713914806806761693)
      ·
        refine ⟨3079578642718052552535635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8212209713914806806761693 3079578642718052552535635)
        ·
          refine ⟨4619367964077078828803453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3079578642718052552535635 4619367964077078828803453)
          ·
            refine ⟨1732262986528904560801295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4619367964077078828803453 1732262986528904560801295)
            ·
              refine ⟨2598394479793356841201943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1732262986528904560801295 2598394479793356841201943)
              ·
                refine ⟨3897591719690035261802915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2598394479793356841201943 3897591719690035261802915)
                ·
                  refine ⟨5846387579535052892704373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3897591719690035261802915 5846387579535052892704373)
                  ·
                    refine ⟨548098835581411208691035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5846387579535052892704373 548098835581411208691035)
                    ·
                      rfl

theorem cell22_1601128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_1601128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601128 prefixEnd_1601128 := by exact prefixLift 1601128
  have htrace : WordTrace (prefixWord ++ tailWord_1601128) baseStart_1601128 baseEnd_1601128 := by
    simpa [prefixWord, tailWord_1601128, baseEnd_1601128] using wordTrace_append hprefix tailTrace_1601128
  have hstable : (prefixWord ++ tailWord_1601128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601128).length < 2 ^ (prefixWord ++ tailWord_1601128).sum := by decide
  have hdescent : baseEnd_1601128 < baseStart_1601128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601141 : List Nat := [1, 3, 4, 2, 1, 2, 1, 8]
def baseStart_1601141 : Nat := 118140960795 + 1601141 * 2 ^ 59
def prefixEnd_1601141 : Nat := 4983230072969 + 3 ^ 40 * 1601141 * 2
def baseEnd_1601141 : Nat := 60900365083009278679555

theorem tailTrace_1601141 : CollatzResearch.WordTrace tailWord_1601141 prefixEnd_1601141 60900365083009278679555 := by
  unfold tailWord_1601141
  simp only [CollatzResearch.WordTrace]
  refine ⟨58398409892347084957195277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38932273261564723304796851 58398409892347084957195277)
  ·
    refine ⟨21899403709630156858948229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58398409892347084957195277 21899403709630156858948229)
    ·
      refine ⟨4106138195555654411052793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21899403709630156858948229 4106138195555654411052793)
      ·
        refine ⟨3079603646666740808289595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4106138195555654411052793 3079603646666740808289595)
        ·
          refine ⟨4619405470000111212434393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3079603646666740808289595 4619405470000111212434393)
          ·
            refine ⟨3464554102500083409325795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4619405470000111212434393 3464554102500083409325795)
            ·
              refine ⟨5196831153750125113988693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3464554102500083409325795 5196831153750125113988693)
              ·
                refine ⟨60900365083009278679555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5196831153750125113988693 60900365083009278679555)
                ·
                  rfl

theorem cell22_1601141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 8].length) (baseStart_1601141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601141 prefixEnd_1601141 := by exact prefixLift 1601141
  have htrace : WordTrace (prefixWord ++ tailWord_1601141) baseStart_1601141 baseEnd_1601141 := by
    simpa [prefixWord, tailWord_1601141, baseEnd_1601141] using wordTrace_append hprefix tailTrace_1601141
  have hstable : (prefixWord ++ tailWord_1601141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601141).length < 2 ^ (prefixWord ++ tailWord_1601141).sum := by decide
  have hdescent : baseEnd_1601141 < baseStart_1601141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601173 : List Nat := [1, 3, 2, 1, 1, 1, 1, 8, 1, 3]
def baseStart_1601173 : Nat := 118140960795 + 1601173 * 2 ^ 59
def prefixEnd_1601173 : Nat := 4983230072969 + 3 ^ 40 * 1601173 * 2
def baseEnd_1601173 : Nat := 548114240001046091315897

theorem tailTrace_1601173 : CollatzResearch.WordTrace tailWord_1601173 prefixEnd_1601173 548114240001046091315897 := by
  unfold tailWord_1601173
  simp only [CollatzResearch.WordTrace]
  refine ⟨58399577028231154422360173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38933051352154102948240115 58399577028231154422360173)
  ·
    refine ⟨21899841385586682908385065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58399577028231154422360173 21899841385586682908385065)
    ·
      refine ⟨16424881039190012181288799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21899841385586682908385065 16424881039190012181288799)
      ·
        refine ⟨24637321558785018271933199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16424881039190012181288799 24637321558785018271933199)
        ·
          refine ⟨36955982338177527407899799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24637321558785018271933199 36955982338177527407899799)
          ·
            refine ⟨55433973507266291111849699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36955982338177527407899799 55433973507266291111849699)
            ·
              refine ⟨83150960260899436667774549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55433973507266291111849699 83150960260899436667774549)
              ·
                refine ⟨974425315557415273450483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 83150960260899436667774549 974425315557415273450483)
                ·
                  refine ⟨1461637973336122910175725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974425315557415273450483 1461637973336122910175725)
                  ·
                    refine ⟨548114240001046091315897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1461637973336122910175725 548114240001046091315897)
                    ·
                      rfl

theorem cell22_1601173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_1601173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601173 prefixEnd_1601173 := by exact prefixLift 1601173
  have htrace : WordTrace (prefixWord ++ tailWord_1601173) baseStart_1601173 baseEnd_1601173 := by
    simpa [prefixWord, tailWord_1601173, baseEnd_1601173] using wordTrace_append hprefix tailTrace_1601173
  have hstable : (prefixWord ++ tailWord_1601173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601173).length < 2 ^ (prefixWord ++ tailWord_1601173).sum := by decide
  have hdescent : baseEnd_1601173 < baseStart_1601173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601259 : List Nat := [1, 1, 1, 1, 2, 4, 2, 10]
def baseStart_1601259 : Nat := 118140960795 + 1601259 * 2 ^ 59
def prefixEnd_1601259 : Nat := 4983230072969 + 3 ^ 40 * 1601259 * 2
def baseEnd_1601259 : Nat := 60904853284285614851737

theorem tailTrace_1601259 : CollatzResearch.WordTrace tailWord_1601259 prefixEnd_1601259 60904853284285614851737 := by
  unfold tailWord_1601259
  simp only [CollatzResearch.WordTrace]
  refine ⟨58402713705919591109990831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38935142470613060739993887 58402713705919591109990831)
  ·
    refine ⟨87604070558879386664986247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58402713705919591109990831 87604070558879386664986247)
    ·
      refine ⟨131406105838319079997479371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87604070558879386664986247 131406105838319079997479371)
      ·
        refine ⟨197109158757478619996219057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131406105838319079997479371 197109158757478619996219057)
        ·
          refine ⟨147831869068108964997164293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197109158757478619996219057 147831869068108964997164293)
          ·
            refine ⟨27718475450270430936968305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147831869068108964997164293 27718475450270430936968305)
            ·
              refine ⟨20788856587702823202726229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27718475450270430936968305 20788856587702823202726229)
              ·
                refine ⟨60904853284285614851737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20788856587702823202726229 60904853284285614851737)
                ·
                  rfl

theorem cell22_1601259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 10].length) (baseStart_1601259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601259 prefixEnd_1601259 := by exact prefixLift 1601259
  have htrace : WordTrace (prefixWord ++ tailWord_1601259) baseStart_1601259 baseEnd_1601259 := by
    simpa [prefixWord, tailWord_1601259, baseEnd_1601259] using wordTrace_append hprefix tailTrace_1601259
  have hstable : (prefixWord ++ tailWord_1601259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601259).length < 2 ^ (prefixWord ++ tailWord_1601259).sum := by decide
  have hdescent : baseEnd_1601259 < baseStart_1601259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601308 : List Nat := [2, 2, 3, 1, 1, 2, 1, 4, 3, 3]
def baseStart_1601308 : Nat := 118140960795 + 1601308 * 2 ^ 59
def prefixEnd_1601308 : Nat := 4983230072969 + 3 ^ 40 * 1601308 * 2
def baseEnd_1601308 : Nat := 548160453259950739190483

theorem tailTrace_1601308 : CollatzResearch.WordTrace tailWord_1601308 prefixEnd_1601308 548160453259950739190483 := by
  unfold tailWord_1601308
  simp only [CollatzResearch.WordTrace]
  refine ⟨29202250441371036239262289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38936333921828048319016385 29202250441371036239262289)
  ·
    refine ⟨21901687831028277179446717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29202250441371036239262289 21901687831028277179446717)
    ·
      refine ⟨8213132936635603942292519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21901687831028277179446717 8213132936635603942292519)
      ·
        refine ⟨12319699404953405913438779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8213132936635603942292519 12319699404953405913438779)
        ·
          refine ⟨18479549107430108870158169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12319699404953405913438779 18479549107430108870158169)
          ·
            refine ⟨13859661830572581652618627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18479549107430108870158169 13859661830572581652618627)
            ·
              refine ⟨20789492745858872478927941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13859661830572581652618627 20789492745858872478927941)
              ·
                refine ⟨3898029889848538589798989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20789492745858872478927941 3898029889848538589798989)
                ·
                  refine ⟨1461761208693201971174621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3898029889848538589798989 1461761208693201971174621)
                  ·
                    refine ⟨548160453259950739190483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1461761208693201971174621 548160453259950739190483)
                    ·
                      rfl

theorem cell22_1601308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_1601308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601308 prefixEnd_1601308 := by exact prefixLift 1601308
  have htrace : WordTrace (prefixWord ++ tailWord_1601308) baseStart_1601308 baseEnd_1601308 := by
    simpa [prefixWord, tailWord_1601308, baseEnd_1601308] using wordTrace_append hprefix tailTrace_1601308
  have hstable : (prefixWord ++ tailWord_1601308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601308).length < 2 ^ (prefixWord ++ tailWord_1601308).sum := by decide
  have hdescent : baseEnd_1601308 < baseStart_1601308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601342 : List Nat := [4, 2, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_1601342 : Nat := 118140960795 + 1601342 * 2 ^ 59
def prefixEnd_1601342 : Nat := 4983230072969 + 3 ^ 40 * 1601342 * 2
def baseEnd_1601342 : Nat := 548172092154785983840379

theorem tailTrace_1601342 : CollatzResearch.WordTrace tailWord_1601342 prefixEnd_1601342 548172092154785983840379 := by
  unfold tailWord_1601342
  simp only [CollatzResearch.WordTrace]
  refine ⟨7300717620577362035657785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38937160643079264190174853 7300717620577362035657785)
  ·
    refine ⟨5475538215433021526743339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7300717620577362035657785 5475538215433021526743339)
    ·
      refine ⟨8213307323149532290115009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5475538215433021526743339 8213307323149532290115009)
      ·
        refine ⟨6159980492362149217586257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8213307323149532290115009 6159980492362149217586257)
        ·
          refine ⟨4619985369271611913189693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6159980492362149217586257 4619985369271611913189693)
          ·
            refine ⟨1732494513476854467446135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4619985369271611913189693 1732494513476854467446135)
            ·
              refine ⟨2598741770215281701169203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1732494513476854467446135 2598741770215281701169203)
              ·
                refine ⟨3898112655322922551753805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2598741770215281701169203 3898112655322922551753805)
                ·
                  refine ⟨1461792245746095956907677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3898112655322922551753805 1461792245746095956907677)
                  ·
                    refine ⟨548172092154785983840379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1461792245746095956907677 548172092154785983840379)
                    ·
                      rfl

theorem cell22_1601342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_1601342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601342 prefixEnd_1601342 := by exact prefixLift 1601342
  have htrace : WordTrace (prefixWord ++ tailWord_1601342) baseStart_1601342 baseEnd_1601342 := by
    simpa [prefixWord, tailWord_1601342, baseEnd_1601342] using wordTrace_append hprefix tailTrace_1601342
  have hstable : (prefixWord ++ tailWord_1601342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601342).length < 2 ^ (prefixWord ++ tailWord_1601342).sum := by decide
  have hdescent : baseEnd_1601342 < baseStart_1601342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601415 : List Nat := [1, 1, 4, 2, 4, 1, 2, 1, 1, 5]
def baseStart_1601415 : Nat := 118140960795 + 1601415 * 2 ^ 59
def prefixEnd_1601415 : Nat := 4983230072969 + 3 ^ 40 * 1601415 * 2
def baseEnd_1601415 : Nat := 548197081546638126765155

theorem tailTrace_1601415 : CollatzResearch.WordTrace tailWord_1601415 prefixEnd_1601415 548197081546638126765155 := by
  unfold tailWord_1601415
  simp only [CollatzResearch.WordTrace]
  refine ⟨58408403493354429752669699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38938935662236286501779799 58408403493354429752669699)
  ·
    refine ⟨87612605240031644629004549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58408403493354429752669699 87612605240031644629004549)
    ·
      refine ⟨16427363482505933367938353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87612605240031644629004549 16427363482505933367938353)
      ·
        refine ⟨12320522611879450025953765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16427363482505933367938353 12320522611879450025953765)
        ·
          refine ⟨2310097989727396879866331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12320522611879450025953765 2310097989727396879866331)
          ·
            refine ⟨3465146984591095319799497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2310097989727396879866331 3465146984591095319799497)
            ·
              refine ⟨2598860238443321489849623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3465146984591095319799497 2598860238443321489849623)
              ·
                refine ⟨3898290357664982234774435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2598860238443321489849623 3898290357664982234774435)
                ·
                  refine ⟨5847435536497473352161653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3898290357664982234774435 5847435536497473352161653)
                  ·
                    refine ⟨548197081546638126765155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5847435536497473352161653 548197081546638126765155)
                    ·
                      rfl

theorem cell22_1601415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_1601415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601415 prefixEnd_1601415 := by exact prefixLift 1601415
  have htrace : WordTrace (prefixWord ++ tailWord_1601415) baseStart_1601415 baseEnd_1601415 := by
    simpa [prefixWord, tailWord_1601415, baseEnd_1601415] using wordTrace_append hprefix tailTrace_1601415
  have hstable : (prefixWord ++ tailWord_1601415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601415).length < 2 ^ (prefixWord ++ tailWord_1601415).sum := by decide
  have hdescent : baseEnd_1601415 < baseStart_1601415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601443 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 7, 3]
def baseStart_1601443 : Nat := 118140960795 + 1601443 * 2 ^ 59
def prefixEnd_1601443 : Nat := 4983230072969 + 3 ^ 40 * 1601443 * 2
def baseEnd_1601443 : Nat := 548206666518855387065069

theorem tailTrace_1601443 : CollatzResearch.WordTrace tailWord_1601443 prefixEnd_1601443 548206666518855387065069 := by
  unfold tailWord_1601443
  simp only [CollatzResearch.WordTrace]
  refine ⟨58409424737252990534688983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38939616491501993689792655 58409424737252990534688983)
  ·
    refine ⟨87614137105879485802033475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58409424737252990534688983 87614137105879485802033475)
    ·
      refine ⟨131421205658819228703050213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87614137105879485802033475 131421205658819228703050213)
      ·
        refine ⟨24641476061028605381821915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131421205658819228703050213 24641476061028605381821915)
        ·
          refine ⟨36962214091542908072732873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24641476061028605381821915 36962214091542908072732873)
          ·
            refine ⟨27721660568657181054549655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36962214091542908072732873 27721660568657181054549655)
            ·
              refine ⟨41582490852985771581824483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27721660568657181054549655 41582490852985771581824483)
              ·
                refine ⟨62373736279478657372736725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41582490852985771581824483 62373736279478657372736725)
                ·
                  refine ⟨1461884444050281032173517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 62373736279478657372736725 1461884444050281032173517)
                  ·
                    refine ⟨548206666518855387065069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1461884444050281032173517 548206666518855387065069)
                    ·
                      rfl

theorem cell22_1601443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 3].length) (baseStart_1601443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601443 prefixEnd_1601443 := by exact prefixLift 1601443
  have htrace : WordTrace (prefixWord ++ tailWord_1601443) baseStart_1601443 baseEnd_1601443 := by
    simpa [prefixWord, tailWord_1601443, baseEnd_1601443] using wordTrace_append hprefix tailTrace_1601443
  have hstable : (prefixWord ++ tailWord_1601443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601443).length < 2 ^ (prefixWord ++ tailWord_1601443).sum := by decide
  have hdescent : baseEnd_1601443 < baseStart_1601443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601511 : List Nat := [1, 1, 5, 2, 3, 1, 3, 2, 1, 3]
def baseStart_1601511 : Nat := 118140960795 + 1601511 * 2 ^ 59
def prefixEnd_1601511 : Nat := 4983230072969 + 3 ^ 40 * 1601511 * 2
def baseEnd_1601511 : Nat := 548229944308525876364861

theorem tailTrace_1601511 : CollatzResearch.WordTrace tailWord_1601511 prefixEnd_1601511 548229944308525876364861 := by
  unfold tailWord_1601511
  simp only [CollatzResearch.WordTrace]
  refine ⟨58411904901006638148164387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38941269934004425432109591 58411904901006638148164387)
  ·
    refine ⟨87617857351509957222246581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58411904901006638148164387 87617857351509957222246581)
    ·
      refine ⟨8214174126704058489585617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87617857351509957222246581 8214174126704058489585617)
      ·
        refine ⟨6160630595028043867189213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8214174126704058489585617 6160630595028043867189213)
        ·
          refine ⟨2310236473135516450195955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6160630595028043867189213 2310236473135516450195955)
          ·
            refine ⟨3465354709703274675293933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2310236473135516450195955 3465354709703274675293933)
            ·
              refine ⟨1299508016138728003235225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3465354709703274675293933 1299508016138728003235225)
              ·
                refine ⟨974631012104046002426419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1299508016138728003235225 974631012104046002426419)
                ·
                  refine ⟨1461946518156069003639629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974631012104046002426419 1461946518156069003639629)
                  ·
                    refine ⟨548229944308525876364861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1461946518156069003639629 548229944308525876364861)
                    ·
                      rfl

theorem cell22_1601511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_1601511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601511 prefixEnd_1601511 := by exact prefixLift 1601511
  have htrace : WordTrace (prefixWord ++ tailWord_1601511) baseStart_1601511 baseEnd_1601511 := by
    simpa [prefixWord, tailWord_1601511, baseEnd_1601511] using wordTrace_append hprefix tailTrace_1601511
  have hstable : (prefixWord ++ tailWord_1601511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601511).length < 2 ^ (prefixWord ++ tailWord_1601511).sum := by decide
  have hdescent : baseEnd_1601511 < baseStart_1601511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601550 : List Nat := [4, 1, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_1601550 : Nat := 118140960795 + 1601550 * 2 ^ 59
def prefixEnd_1601550 : Nat := 4983230072969 + 3 ^ 40 * 1601550 * 2
def baseEnd_1601550 : Nat := 548243294805542774639741

theorem tailTrace_1601550 : CollatzResearch.WordTrace tailWord_1601550 prefixEnd_1601550 548243294805542774639741 := by
  unfold tailWord_1601550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7301665918483168476104263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38942218231910231872556069 7301665918483168476104263)
  ·
    refine ⟨10952498877724752714156395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7301665918483168476104263 10952498877724752714156395)
    ·
      refine ⟨16428748316587129071234593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10952498877724752714156395 16428748316587129071234593)
      ·
        refine ⟨12321561237440346803425945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16428748316587129071234593 12321561237440346803425945)
        ·
          refine ⟨9241170928080260102569459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12321561237440346803425945 9241170928080260102569459)
          ·
            refine ⟨13861756392120390153854189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9241170928080260102569459 13861756392120390153854189)
            ·
              refine ⟨5198158647045146307695321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13861756392120390153854189 5198158647045146307695321)
              ·
                refine ⟨3898618985283859730771491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5198158647045146307695321 3898618985283859730771491)
                ·
                  refine ⟨5847928477925789596157237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3898618985283859730771491 5847928477925789596157237)
                  ·
                    refine ⟨548243294805542774639741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5847928477925789596157237 548243294805542774639741)
                    ·
                      rfl

theorem cell22_1601550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_1601550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601550 prefixEnd_1601550 := by exact prefixLift 1601550
  have htrace : WordTrace (prefixWord ++ tailWord_1601550) baseStart_1601550 baseEnd_1601550 := by
    simpa [prefixWord, tailWord_1601550, baseEnd_1601550] using wordTrace_append hprefix tailTrace_1601550
  have hstable : (prefixWord ++ tailWord_1601550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601550).length < 2 ^ (prefixWord ++ tailWord_1601550).sum := by decide
  have hdescent : baseEnd_1601550 < baseStart_1601550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601567 : List Nat := [1, 1, 2, 4, 1, 2, 4, 2, 2, 3]
def baseStart_1601567 : Nat := 118140960795 + 1601567 * 2 ^ 59
def prefixEnd_1601567 : Nat := 4983230072969 + 3 ^ 40 * 1601567 * 2
def baseEnd_1601567 : Nat := 548249114252960396964689

theorem tailTrace_1601567 : CollatzResearch.WordTrace tailWord_1601567 prefixEnd_1601567 548249114252960396964689 := by
  unfold tailWord_1601567
  simp only [CollatzResearch.WordTrace]
  refine ⟨58413947388803759712202955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38942631592535839808135303 58413947388803759712202955)
  ·
    refine ⟨87620921083205639568304433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58413947388803759712202955 87620921083205639568304433)
    ·
      refine ⟨65715690812404229676228325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87620921083205639568304433 65715690812404229676228325)
      ·
        refine ⟨12321692027325793064292811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65715690812404229676228325 12321692027325793064292811)
        ·
          refine ⟨18482538040988689596439217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12321692027325793064292811 18482538040988689596439217)
          ·
            refine ⟨13861903530741517197329413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18482538040988689596439217 13861903530741517197329413)
            ·
              refine ⟨2599106912014034474499265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13861903530741517197329413 2599106912014034474499265)
              ·
                refine ⟨1949330184010525855874449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2599106912014034474499265 1949330184010525855874449)
                ·
                  refine ⟨1461997638007894391905837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1949330184010525855874449 1461997638007894391905837)
                  ·
                    refine ⟨548249114252960396964689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1461997638007894391905837 548249114252960396964689)
                    ·
                      rfl

theorem cell22_1601567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 3].length) (baseStart_1601567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601567 prefixEnd_1601567 := by exact prefixLift 1601567
  have htrace : WordTrace (prefixWord ++ tailWord_1601567) baseStart_1601567 baseEnd_1601567 := by
    simpa [prefixWord, tailWord_1601567, baseEnd_1601567] using wordTrace_append hprefix tailTrace_1601567
  have hstable : (prefixWord ++ tailWord_1601567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601567).length < 2 ^ (prefixWord ++ tailWord_1601567).sum := by decide
  have hdescent : baseEnd_1601567 < baseStart_1601567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601595 : List Nat := [1, 1, 1, 1, 1, 2, 1, 8, 3, 3]
def baseStart_1601595 : Nat := 118140960795 + 1601595 * 2 ^ 59
def prefixEnd_1601595 : Nat := 4983230072969 + 3 ^ 40 * 1601595 * 2
def baseEnd_1601595 : Nat := 548258699225177657264603

theorem tailTrace_1601595 : CollatzResearch.WordTrace tailWord_1601595 prefixEnd_1601595 548258699225177657264603 := by
  unfold tailWord_1601595
  simp only [CollatzResearch.WordTrace]
  refine ⟨58414968632702320494222239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38943312421801546996148159 58414968632702320494222239)
  ·
    refine ⟨87622452949053480741333359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58414968632702320494222239 87622452949053480741333359)
    ·
      refine ⟨131433679423580221112000039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87622452949053480741333359 131433679423580221112000039)
      ·
        refine ⟨197150519135370331668000059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131433679423580221112000039 197150519135370331668000059)
        ·
          refine ⟨295725778703055497502000089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197150519135370331668000059 295725778703055497502000089)
          ·
            refine ⟨221794334027291623126500067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295725778703055497502000089 221794334027291623126500067)
            ·
              refine ⟨332691501040937434689750101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221794334027291623126500067 332691501040937434689750101)
              ·
                refine ⟨3898728527823485562770509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 332691501040937434689750101 3898728527823485562770509)
                ·
                  refine ⟨1462023197933807086038941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3898728527823485562770509 1462023197933807086038941)
                  ·
                    refine ⟨548258699225177657264603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1462023197933807086038941 548258699225177657264603)
                    ·
                      rfl

theorem cell22_1601595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 3].length) (baseStart_1601595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601595 prefixEnd_1601595 := by exact prefixLift 1601595
  have htrace : WordTrace (prefixWord ++ tailWord_1601595) baseStart_1601595 baseEnd_1601595 := by
    simpa [prefixWord, tailWord_1601595, baseEnd_1601595] using wordTrace_append hprefix tailTrace_1601595
  have hstable : (prefixWord ++ tailWord_1601595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601595).length < 2 ^ (prefixWord ++ tailWord_1601595).sum := by decide
  have hdescent : baseEnd_1601595 < baseStart_1601595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601629 : List Nat := [1, 4, 4, 1, 1, 1, 1, 3, 3, 3]
def baseStart_1601629 : Nat := 118140960795 + 1601629 * 2 ^ 59
def prefixEnd_1601629 : Nat := 4983230072969 + 3 ^ 40 * 1601629 * 2
def baseEnd_1601629 : Nat := 548270338120012901914499

theorem tailTrace_1601629 : CollatzResearch.WordTrace tailWord_1601629 prefixEnd_1601629 548270338120012901914499 := by
  unfold tailWord_1601629
  simp only [CollatzResearch.WordTrace]
  refine ⟨58416208714579144300959941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38944139143052762867306627 58416208714579144300959941)
  ·
    refine ⟨10953039133983589556429989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58416208714579144300959941 10953039133983589556429989)
    ·
      refine ⟨2053694837621923041830623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10953039133983589556429989 2053694837621923041830623)
      ·
        refine ⟨3080542256432884562745935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2053694837621923041830623 3080542256432884562745935)
        ·
          refine ⟨4620813384649326844118903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3080542256432884562745935 4620813384649326844118903)
          ·
            refine ⟨6931220076973990266178355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4620813384649326844118903 6931220076973990266178355)
            ·
              refine ⟨10396830115460985399267533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6931220076973990266178355 10396830115460985399267533)
              ·
                refine ⟨3898811293297869524725325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10396830115460985399267533 3898811293297869524725325)
                ·
                  refine ⟨1462054234986701071771997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3898811293297869524725325 1462054234986701071771997)
                  ·
                    refine ⟨548270338120012901914499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1462054234986701071771997 548270338120012901914499)
                    ·
                      rfl

theorem cell22_1601629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_1601629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601629 prefixEnd_1601629 := by exact prefixLift 1601629
  have htrace : WordTrace (prefixWord ++ tailWord_1601629) baseStart_1601629 baseEnd_1601629 := by
    simpa [prefixWord, tailWord_1601629, baseEnd_1601629] using wordTrace_append hprefix tailTrace_1601629
  have hstable : (prefixWord ++ tailWord_1601629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601629).length < 2 ^ (prefixWord ++ tailWord_1601629).sum := by decide
  have hdescent : baseEnd_1601629 < baseStart_1601629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601745 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 2, 6]
def baseStart_1601745 : Nat := 118140960795 + 1601745 * 2 ^ 59
def prefixEnd_1601745 : Nat := 4983230072969 + 3 ^ 40 * 1601745 * 2
def baseEnd_1601745 : Nat := 548310047290627266014143

theorem tailTrace_1601745 : CollatzResearch.WordTrace tailWord_1601745 prefixEnd_1601745 548310047290627266014143 := by
  unfold tailWord_1601745
  simp only [CollatzResearch.WordTrace]
  refine ⟨58420439582158896112182689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38946959721439264074788459 58420439582158896112182689)
  ·
    refine ⟨43815329686619172084137017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58420439582158896112182689 43815329686619172084137017)
    ·
      refine ⟨32861497264964379063102763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43815329686619172084137017 32861497264964379063102763)
      ·
        refine ⟨49292245897446568594654145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32861497264964379063102763 49292245897446568594654145)
        ·
          refine ⟨36969184423084926445990609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49292245897446568594654145 36969184423084926445990609)
          ·
            refine ⟨27726888317313694834492957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36969184423084926445990609 27726888317313694834492957)
            ·
              refine ⟨10397583118992635562934859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27726888317313694834492957 10397583118992635562934859)
              ·
                refine ⟨15596374678488953344402289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10397583118992635562934859 15596374678488953344402289)
                ·
                  refine ⟨11697281008866715008301717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15596374678488953344402289 11697281008866715008301717)
                  ·
                    refine ⟨548310047290627266014143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11697281008866715008301717 548310047290627266014143)
                    ·
                      rfl

theorem cell22_1601745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_1601745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601745 prefixEnd_1601745 := by exact prefixLift 1601745
  have htrace : WordTrace (prefixWord ++ tailWord_1601745) baseStart_1601745 baseEnd_1601745 := by
    simpa [prefixWord, tailWord_1601745, baseEnd_1601745] using wordTrace_append hprefix tailTrace_1601745
  have hstable : (prefixWord ++ tailWord_1601745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601745).length < 2 ^ (prefixWord ++ tailWord_1601745).sum := by decide
  have hdescent : baseEnd_1601745 < baseStart_1601745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601749 : List Nat := [1, 3, 2, 4, 2, 2, 1, 7]
def baseStart_1601749 : Nat := 118140960795 + 1601749 * 2 ^ 59
def prefixEnd_1601749 : Nat := 4983230072969 + 3 ^ 40 * 1601749 * 2
def baseEnd_1601749 : Nat := 60923490730263620990459

theorem tailTrace_1601749 : CollatzResearch.WordTrace tailWord_1601749 prefixEnd_1601749 60923490730263620990459 := by
  unfold tailWord_1601749
  simp only [CollatzResearch.WordTrace]
  refine ⟨58420585474144404795328301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38947056982762936530218867 58420585474144404795328301)
  ·
    refine ⟨21907719552804151798248113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58420585474144404795328301 21907719552804151798248113)
    ·
      refine ⟨16430789664603113848686085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21907719552804151798248113 16430789664603113848686085)
      ·
        refine ⟨3080773062113083846628641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16430789664603113848686085 3080773062113083846628641)
        ·
          refine ⟨2310579796584812884971481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3080773062113083846628641 2310579796584812884971481)
          ·
            refine ⟨1732934847438609663728611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2310579796584812884971481 1732934847438609663728611)
            ·
              refine ⟨2599402271157914495592917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1732934847438609663728611 2599402271157914495592917)
              ·
                refine ⟨60923490730263620990459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2599402271157914495592917 60923490730263620990459)
                ·
                  rfl

theorem cell22_1601749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 7].length) (baseStart_1601749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601749 prefixEnd_1601749 := by exact prefixLift 1601749
  have htrace : WordTrace (prefixWord ++ tailWord_1601749) baseStart_1601749 baseEnd_1601749 := by
    simpa [prefixWord, tailWord_1601749, baseEnd_1601749] using wordTrace_append hprefix tailTrace_1601749
  have hstable : (prefixWord ++ tailWord_1601749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601749).length < 2 ^ (prefixWord ++ tailWord_1601749).sum := by decide
  have hdescent : baseEnd_1601749 < baseStart_1601749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601794 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 7]
def baseStart_1601794 : Nat := 118140960795 + 1601794 * 2 ^ 59
def prefixEnd_1601794 : Nat := 4983230072969 + 3 ^ 40 * 1601794 * 2
def baseEnd_1601794 : Nat := 182775606997335823846331

theorem tailTrace_1601794 : CollatzResearch.WordTrace tailWord_1601794 prefixEnd_1601794 182775606997335823846331 := by
  unfold tailWord_1601794
  simp only [CollatzResearch.WordTrace]
  refine ⟨14605556689745344370179109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38948151172654251653810957 14605556689745344370179109)
  ·
    refine ⟨2738541879327252069408583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14605556689745344370179109 2738541879327252069408583)
    ·
      refine ⟨4107812818990878104112875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2738541879327252069408583 4107812818990878104112875)
      ·
        refine ⟨6161719228486317156169313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4107812818990878104112875 6161719228486317156169313)
        ·
          refine ⟨4621289421364737867126985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6161719228486317156169313 4621289421364737867126985)
          ·
            refine ⟨3465967066023553400345239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4621289421364737867126985 3465967066023553400345239)
            ·
              refine ⟨5198950599035330100517859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3465967066023553400345239 5198950599035330100517859)
              ·
                refine ⟨7798425898552995150776789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5198950599035330100517859 7798425898552995150776789)
                ·
                  refine ⟨182775606997335823846331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7798425898552995150776789 182775606997335823846331)
                  ·
                    rfl

theorem cell22_1601794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_1601794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601794 prefixEnd_1601794 := by exact prefixLift 1601794
  have htrace : WordTrace (prefixWord ++ tailWord_1601794) baseStart_1601794 baseEnd_1601794 := by
    simpa [prefixWord, tailWord_1601794, baseEnd_1601794] using wordTrace_append hprefix tailTrace_1601794
  have hstable : (prefixWord ++ tailWord_1601794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601794).length < 2 ^ (prefixWord ++ tailWord_1601794).sum := by decide
  have hdescent : baseEnd_1601794 < baseStart_1601794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601824 : List Nat := [2, 1, 1, 5, 2, 1, 1, 4, 1, 4]
def baseStart_1601824 : Nat := 118140960795 + 1601824 * 2 ^ 59
def prefixEnd_1601824 : Nat := 4983230072969 + 3 ^ 40 * 1601824 * 2
def baseEnd_1601824 : Nat := 548337090605097393288901

theorem tailTrace_1601824 : CollatzResearch.WordTrace tailWord_1601824 prefixEnd_1601824 548337090605097393288901 := by
  unfold tailWord_1601824
  simp only [CollatzResearch.WordTrace]
  refine ⟨29211660474436346302154263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38948880632581795069539017 29211660474436346302154263)
  ·
    refine ⟨43817490711654519453231395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29211660474436346302154263 43817490711654519453231395)
    ·
      refine ⟨65726236067481779179847093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43817490711654519453231395 65726236067481779179847093)
      ·
        refine ⟨6161834631326416798110665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65726236067481779179847093 6161834631326416798110665)
        ·
          refine ⟨4621375973494812598582999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6161834631326416798110665 4621375973494812598582999)
          ·
            refine ⟨6932063960242218897874499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4621375973494812598582999 6932063960242218897874499)
            ·
              refine ⟨10398095940363328346811749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6932063960242218897874499 10398095940363328346811749)
              ·
                refine ⟨1949642988818124065027203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10398095940363328346811749 1949642988818124065027203)
                ·
                  refine ⟨2924464483227186097540805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1949642988818124065027203 2924464483227186097540805)
                  ·
                    refine ⟨548337090605097393288901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2924464483227186097540805 548337090605097393288901)
                    ·
                      rfl

theorem cell22_1601824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 1, 4].length) (baseStart_1601824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601824 prefixEnd_1601824 := by exact prefixLift 1601824
  have htrace : WordTrace (prefixWord ++ tailWord_1601824) baseStart_1601824 baseEnd_1601824 := by
    simpa [prefixWord, tailWord_1601824, baseEnd_1601824] using wordTrace_append hprefix tailTrace_1601824
  have hstable : (prefixWord ++ tailWord_1601824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601824).length < 2 ^ (prefixWord ++ tailWord_1601824).sum := by decide
  have hdescent : baseEnd_1601824 < baseStart_1601824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601839 : List Nat := [1, 1, 2, 1, 2, 1, 7, 3, 4]
def baseStart_1601839 : Nat := 118140960795 + 1601839 * 2 ^ 59
def prefixEnd_1601839 : Nat := 4983230072969 + 3 ^ 40 * 1601839 * 2
def baseEnd_1601839 : Nat := 182780741803880784721285

theorem tailTrace_1601839 : CollatzResearch.WordTrace tailWord_1601839 prefixEnd_1601839 182780741803880784721285 := by
  unfold tailWord_1601839
  simp only [CollatzResearch.WordTrace]
  refine ⟨58423868043818350166104571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38949245362545566777403047 58423868043818350166104571)
  ·
    refine ⟨87635802065727525249156857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58423868043818350166104571 87635802065727525249156857)
    ·
      refine ⟨65726851549295643936867643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87635802065727525249156857 65726851549295643936867643)
      ·
        refine ⟨98590277323943465905301465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65726851549295643936867643 98590277323943465905301465)
        ·
          refine ⟨73942707992957599428976099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98590277323943465905301465 73942707992957599428976099)
          ·
            refine ⟨110914061989436399143464149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73942707992957599428976099 110914061989436399143464149)
            ·
              refine ⟨2599548327877415604924941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 110914061989436399143464149 2599548327877415604924941)
              ·
                refine ⟨974830622954030851846853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2599548327877415604924941 974830622954030851846853)
                ·
                  refine ⟨182780741803880784721285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 974830622954030851846853 182780741803880784721285)
                  ·
                    rfl

theorem cell22_1601839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 3, 4].length) (baseStart_1601839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601839 prefixEnd_1601839 := by exact prefixLift 1601839
  have htrace : WordTrace (prefixWord ++ tailWord_1601839) baseStart_1601839 baseEnd_1601839 := by
    simpa [prefixWord, tailWord_1601839, baseEnd_1601839] using wordTrace_append hprefix tailTrace_1601839
  have hstable : (prefixWord ++ tailWord_1601839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601839).length < 2 ^ (prefixWord ++ tailWord_1601839).sum := by decide
  have hdescent : baseEnd_1601839 < baseStart_1601839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601929 : List Nat := [1, 2, 1, 1, 6, 1, 2, 3, 5]
def baseStart_1601929 : Nat := 118140960795 + 1601929 * 2 ^ 59
def prefixEnd_1601929 : Nat := 4983230072969 + 3 ^ 40 * 1601929 * 2
def baseEnd_1601929 : Nat := 182791011416970706471193

theorem tailTrace_1601929 : CollatzResearch.WordTrace tailWord_1601929 prefixEnd_1601929 182791011416970706471193 := by
  unfold tailWord_1601929
  simp only [CollatzResearch.WordTrace]
  refine ⟨58427150613492295536880841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38951433742328197024587227 58427150613492295536880841)
  ·
    refine ⟨43820362960119221652660631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58427150613492295536880841 43820362960119221652660631)
    ·
      refine ⟨65730544440178832478990947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43820362960119221652660631 65730544440178832478990947)
      ·
        refine ⟨98595816660268248718486421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65730544440178832478990947 98595816660268248718486421)
        ·
          refine ⟨4621678905950074158679051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98595816660268248718486421 4621678905950074158679051)
          ·
            refine ⟨6932518358925111238018577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4621678905950074158679051 6932518358925111238018577)
            ·
              refine ⟨5199388769193833428513933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6932518358925111238018577 5199388769193833428513933)
              ·
                refine ⟨1949770788447687535692725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5199388769193833428513933 1949770788447687535692725)
                ·
                  refine ⟨182791011416970706471193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1949770788447687535692725 182791011416970706471193)
                  ·
                    rfl

theorem cell22_1601929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 3, 5].length) (baseStart_1601929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601929 prefixEnd_1601929 := by exact prefixLift 1601929
  have htrace : WordTrace (prefixWord ++ tailWord_1601929) baseStart_1601929 baseEnd_1601929 := by
    simpa [prefixWord, tailWord_1601929, baseEnd_1601929] using wordTrace_append hprefix tailTrace_1601929
  have hstable : (prefixWord ++ tailWord_1601929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601929).length < 2 ^ (prefixWord ++ tailWord_1601929).sum := by decide
  have hdescent : baseEnd_1601929 < baseStart_1601929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601950 : List Nat := [4, 3, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_1601950 : Nat := 118140960795 + 1601950 * 2 ^ 59
def prefixEnd_1601950 : Nat := 4983230072969 + 3 ^ 40 * 1601950 * 2
def baseEnd_1601950 : Nat := 548380222980075064638515

theorem tailTrace_1601950 : CollatzResearch.WordTrace tailWord_1601950 prefixEnd_1601950 548380222980075064638515 := by
  unfold tailWord_1601950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7303489568302027015424413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38951944364277477415596869 7303489568302027015424413)
  ·
    refine ⟨2738808588113260130784155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7303489568302027015424413 2738808588113260130784155)
    ·
      refine ⟨4108212882169890196176233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2738808588113260130784155 4108212882169890196176233)
      ·
        refine ⟨3081159661627417647132175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4108212882169890196176233 3081159661627417647132175)
        ·
          refine ⟨4621739492441126470698263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3081159661627417647132175 4621739492441126470698263)
          ·
            refine ⟨6932609238661689706047395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4621739492441126470698263 6932609238661689706047395)
            ·
              refine ⟨10398913857992534559071093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6932609238661689706047395 10398913857992534559071093)
              ·
                refine ⟨974898174186800114912915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10398913857992534559071093 974898174186800114912915)
                ·
                  refine ⟨1462347261280200172369373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974898174186800114912915 1462347261280200172369373)
                  ·
                    refine ⟨548380222980075064638515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1462347261280200172369373 548380222980075064638515)
                    ·
                      rfl

theorem cell22_1601950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_1601950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601950 prefixEnd_1601950 := by exact prefixLift 1601950
  have htrace : WordTrace (prefixWord ++ tailWord_1601950) baseStart_1601950 baseEnd_1601950 := by
    simpa [prefixWord, tailWord_1601950, baseEnd_1601950] using wordTrace_append hprefix tailTrace_1601950
  have hstable : (prefixWord ++ tailWord_1601950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601950).length < 2 ^ (prefixWord ++ tailWord_1601950).sum := by decide
  have hdescent : baseEnd_1601950 < baseStart_1601950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1601957 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 8]
def baseStart_1601957 : Nat := 118140960795 + 1601957 * 2 ^ 59
def prefixEnd_1601957 : Nat := 4983230072969 + 3 ^ 40 * 1601957 * 2
def baseEnd_1601957 : Nat := 182794206407709793237831

theorem tailTrace_1601957 : CollatzResearch.WordTrace tailWord_1601957 prefixEnd_1601957 182794206407709793237831 := by
  unfold tailWord_1601957
  simp only [CollatzResearch.WordTrace]
  refine ⟨58428171857390856318900125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38952114571593904212600083 58428171857390856318900125)
  ·
    refine ⟨21910564446521571119587547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58428171857390856318900125 21910564446521571119587547)
    ·
      refine ⟨32865846669782356679381321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21910564446521571119587547 32865846669782356679381321)
      ·
        refine ⟨24649385002336767509535991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32865846669782356679381321 24649385002336767509535991)
        ·
          refine ⟨36974077503505151264303987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24649385002336767509535991 36974077503505151264303987)
          ·
            refine ⟨55461116255257726896455981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36974077503505151264303987 55461116255257726896455981)
            ·
              refine ⟨20797918595721647586170993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55461116255257726896455981 20797918595721647586170993)
              ·
                refine ⟨15598438946791235689628245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20797918595721647586170993 15598438946791235689628245)
                ·
                  refine ⟨182794206407709793237831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15598438946791235689628245 182794206407709793237831)
                  ·
                    rfl

theorem cell22_1601957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_1601957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1601957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1601957 prefixEnd_1601957 := by exact prefixLift 1601957
  have htrace : WordTrace (prefixWord ++ tailWord_1601957) baseStart_1601957 baseEnd_1601957 := by
    simpa [prefixWord, tailWord_1601957, baseEnd_1601957] using wordTrace_append hprefix tailTrace_1601957
  have hstable : (prefixWord ++ tailWord_1601957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1601957).length < 2 ^ (prefixWord ++ tailWord_1601957).sum := by decide
  have hdescent : baseEnd_1601957 < baseStart_1601957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1601957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602006 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_1602006 : Nat := 118140960795 + 1602006 * 2 ^ 59
def prefixEnd_1602006 : Nat := 4983230072969 + 3 ^ 40 * 1602006 * 2
def baseEnd_1602006 : Nat := 548399392924509585238343

theorem tailTrace_1602006 : CollatzResearch.WordTrace tailWord_1602006 prefixEnd_1602006 548399392924509585238343 := by
  unfold tailWord_1602006
  simp only [CollatzResearch.WordTrace]
  refine ⟨3651872439638333605464617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38953306022808891791622581 3651872439638333605464617)
  ·
    refine ⟨2738904329728750204098463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3651872439638333605464617 2738904329728750204098463)
    ·
      refine ⟨4108356494593125306147695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2738904329728750204098463 4108356494593125306147695)
      ·
        refine ⟨6162534741889687959221543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4108356494593125306147695 6162534741889687959221543)
        ·
          refine ⟨9243802112834531938832315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6162534741889687959221543 9243802112834531938832315)
          ·
            refine ⟨13865703169251797908248473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9243802112834531938832315 13865703169251797908248473)
            ·
              refine ⟨10399277376938848431186355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13865703169251797908248473 10399277376938848431186355)
              ·
                refine ⟨15598916065408272646779533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10399277376938848431186355 15598916065408272646779533)
                ·
                  refine ⟨5849593524528102242542325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15598916065408272646779533 5849593524528102242542325)
                  ·
                    refine ⟨548399392924509585238343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5849593524528102242542325 548399392924509585238343)
                    ·
                      rfl

theorem cell22_1602006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_1602006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602006 prefixEnd_1602006 := by exact prefixLift 1602006
  have htrace : WordTrace (prefixWord ++ tailWord_1602006) baseStart_1602006 baseEnd_1602006 := by
    simpa [prefixWord, tailWord_1602006, baseEnd_1602006] using wordTrace_append hprefix tailTrace_1602006
  have hstable : (prefixWord ++ tailWord_1602006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602006).length < 2 ^ (prefixWord ++ tailWord_1602006).sum := by decide
  have hdescent : baseEnd_1602006 < baseStart_1602006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602079 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 2, 5]
def baseStart_1602079 : Nat := 118140960795 + 1602079 * 2 ^ 59
def prefixEnd_1602079 : Nat := 4983230072969 + 3 ^ 40 * 1602079 * 2
def baseEnd_1602079 : Nat := 548424382316361728163119

theorem tailTrace_1602079 : CollatzResearch.WordTrace tailWord_1602079 prefixEnd_1602079 548424382316361728163119 := by
  unfold tailWord_1602079
  simp only [CollatzResearch.WordTrace]
  refine ⟨58432621562948871154841291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38955081041965914103227527 58432621562948871154841291)
  ·
    refine ⟨87648932344423306732261937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58432621562948871154841291 87648932344423306732261937)
    ·
      refine ⟨65736699258317480049196453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87648932344423306732261937 65736699258317480049196453)
      ·
        refine ⟨12325631110934527509224335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65736699258317480049196453 12325631110934527509224335)
        ·
          refine ⟨18488446666401791263836503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12325631110934527509224335 18488446666401791263836503)
          ·
            refine ⟨27732669999602686895754755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18488446666401791263836503 27732669999602686895754755)
            ·
              refine ⟨41599004999404030343632133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27732669999602686895754755 41599004999404030343632133)
              ·
                refine ⟨7799813437388255689431025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41599004999404030343632133 7799813437388255689431025)
                ·
                  refine ⟨5849860078041191767073269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7799813437388255689431025 5849860078041191767073269)
                  ·
                    refine ⟨548424382316361728163119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5849860078041191767073269 548424382316361728163119)
                    ·
                      rfl

theorem cell22_1602079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_1602079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602079 prefixEnd_1602079 := by exact prefixLift 1602079
  have htrace : WordTrace (prefixWord ++ tailWord_1602079) baseStart_1602079 baseEnd_1602079 := by
    simpa [prefixWord, tailWord_1602079, baseEnd_1602079] using wordTrace_append hprefix tailTrace_1602079
  have hstable : (prefixWord ++ tailWord_1602079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602079).length < 2 ^ (prefixWord ++ tailWord_1602079).sum := by decide
  have hdescent : baseEnd_1602079 < baseStart_1602079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602081 : List Nat := [1, 2, 3, 2, 2, 1, 4, 2, 5]
def baseStart_1602081 : Nat := 118140960795 + 1602081 * 2 ^ 59
def prefixEnd_1602081 : Nat := 4983230072969 + 3 ^ 40 * 1602081 * 2
def baseEnd_1602081 : Nat := 182808355652411463204371

theorem tailTrace_1602081 : CollatzResearch.WordTrace tailWord_1602081 prefixEnd_1602081 182808355652411463204371 := by
  unfold tailWord_1602081
  simp only [CollatzResearch.WordTrace]
  refine ⟨58432694508941625496414097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38955129672627750330942731 58432694508941625496414097)
  ·
    refine ⟨43824520881706219122310573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58432694508941625496414097 43824520881706219122310573)
    ·
      refine ⟨16434195330639832170866465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43824520881706219122310573 16434195330639832170866465)
      ·
        refine ⟨12325646497979874128149849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16434195330639832170866465 12325646497979874128149849)
        ·
          refine ⟨9244234873484905596112387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12325646497979874128149849 9244234873484905596112387)
          ·
            refine ⟨13866352310227358394168581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9244234873484905596112387 13866352310227358394168581)
            ·
              refine ⟨2599941058167629698906609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13866352310227358394168581 2599941058167629698906609)
              ·
                refine ⟨1949955793625722274179957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2599941058167629698906609 1949955793625722274179957)
                ·
                  refine ⟨182808355652411463204371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1949955793625722274179957 182808355652411463204371)
                  ·
                    rfl

theorem cell22_1602081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 5].length) (baseStart_1602081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602081 prefixEnd_1602081 := by exact prefixLift 1602081
  have htrace : WordTrace (prefixWord ++ tailWord_1602081) baseStart_1602081 baseEnd_1602081 := by
    simpa [prefixWord, tailWord_1602081, baseEnd_1602081] using wordTrace_append hprefix tailTrace_1602081
  have hstable : (prefixWord ++ tailWord_1602081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602081).length < 2 ^ (prefixWord ++ tailWord_1602081).sum := by decide
  have hdescent : baseEnd_1602081 < baseStart_1602081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602085 : List Nat := [1, 3, 1, 2, 2, 1, 6, 2, 1, 3]
def baseStart_1602085 : Nat := 118140960795 + 1602085 * 2 ^ 59
def prefixEnd_1602085 : Nat := 4983230072969 + 3 ^ 40 * 1602085 * 2
def baseEnd_1602085 : Nat := 548426436238979712513101

theorem tailTrace_1602085 : CollatzResearch.WordTrace tailWord_1602085 prefixEnd_1602085 548426436238979712513101 := by
  unfold tailWord_1602085
  simp only [CollatzResearch.WordTrace]
  refine ⟨58432840400927134179559709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38955226933951422786373139 58432840400927134179559709)
  ·
    refine ⟨21912315150347675317334891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58432840400927134179559709 21912315150347675317334891)
    ·
      refine ⟨32868472725521512976002337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21912315150347675317334891 32868472725521512976002337)
      ·
        refine ⟨24651354544141134732001753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32868472725521512976002337 24651354544141134732001753)
        ·
          refine ⟨18488515908105851049001315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24651354544141134732001753 18488515908105851049001315)
          ·
            refine ⟨27732773862158776573501973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18488515908105851049001315 27732773862158776573501973)
            ·
              refine ⟨1299973774788692651882905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27732773862158776573501973 1299973774788692651882905)
              ·
                refine ⟨974980331091519488912179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1299973774788692651882905 974980331091519488912179)
                ·
                  refine ⟨1462470496637279233368269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974980331091519488912179 1462470496637279233368269)
                  ·
                    refine ⟨548426436238979712513101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1462470496637279233368269 548426436238979712513101)
                    ·
                      rfl

theorem cell22_1602085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 2, 1, 3].length) (baseStart_1602085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602085 prefixEnd_1602085 := by exact prefixLift 1602085
  have htrace : WordTrace (prefixWord ++ tailWord_1602085) baseStart_1602085 baseEnd_1602085 := by
    simpa [prefixWord, tailWord_1602085, baseEnd_1602085] using wordTrace_append hprefix tailTrace_1602085
  have hstable : (prefixWord ++ tailWord_1602085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602085).length < 2 ^ (prefixWord ++ tailWord_1602085).sum := by decide
  have hdescent : baseEnd_1602085 < baseStart_1602085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602111 : List Nat := [1, 1, 2, 2, 3, 2, 2, 4, 1, 4]
def baseStart_1602111 : Nat := 118140960795 + 1602111 * 2 ^ 59
def prefixEnd_1602111 : Nat := 4983230072969 + 3 ^ 40 * 1602111 * 2
def baseEnd_1602111 : Nat := 548435336570324311363021

theorem tailTrace_1602111 : CollatzResearch.WordTrace tailWord_1602111 prefixEnd_1602111 548435336570324311363021 := by
  unfold tailWord_1602111
  simp only [CollatzResearch.WordTrace]
  refine ⟨58433788698832940620006187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38955859132555293746670791 58433788698832940620006187)
  ·
    refine ⟨87650683048249410930009281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58433788698832940620006187 87650683048249410930009281)
    ·
      refine ⟨65738012286187058197506961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87650683048249410930009281 65738012286187058197506961)
      ·
        refine ⟨49303509214640293648130221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65738012286187058197506961 49303509214640293648130221)
        ·
          refine ⟨18488815955490110118048833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49303509214640293648130221 18488815955490110118048833)
          ·
            refine ⟨13866611966617582588536625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18488815955490110118048833 13866611966617582588536625)
            ·
              refine ⟨10399958974963186941402469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13866611966617582588536625 10399958974963186941402469)
              ·
                refine ⟨1949992307805597551512963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10399958974963186941402469 1949992307805597551512963)
                ·
                  refine ⟨2924988461708396327269445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1949992307805597551512963 2924988461708396327269445)
                  ·
                    refine ⟨548435336570324311363021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2924988461708396327269445 548435336570324311363021)
                    ·
                      rfl

theorem cell22_1602111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 4].length) (baseStart_1602111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602111 prefixEnd_1602111 := by exact prefixLift 1602111
  have htrace : WordTrace (prefixWord ++ tailWord_1602111) baseStart_1602111 baseEnd_1602111 := by
    simpa [prefixWord, tailWord_1602111, baseEnd_1602111] using wordTrace_append hprefix tailTrace_1602111
  have hstable : (prefixWord ++ tailWord_1602111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602111).length < 2 ^ (prefixWord ++ tailWord_1602111).sum := by decide
  have hdescent : baseEnd_1602111 < baseStart_1602111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602158 : List Nat := [4, 1, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_1602158 : Nat := 118140960795 + 1602158 * 2 ^ 59
def prefixEnd_1602158 : Nat := 4983230072969 + 3 ^ 40 * 1602158 * 2
def baseEnd_1602158 : Nat := 548451425630831855437877

theorem tailTrace_1602158 : CollatzResearch.WordTrace tailWord_1602158 prefixEnd_1602158 548451425630831855437877 := by
  unfold tailWord_1602158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7304437866207833455870891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38957001953108445097978085 7304437866207833455870891)
  ·
    refine ⟨10956656799311750183806337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7304437866207833455870891 10956656799311750183806337)
    ·
      refine ⟨8217492599483812637854753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10956656799311750183806337 8217492599483812637854753)
      ·
        refine ⟨6163119449612859478391065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8217492599483812637854753 6163119449612859478391065)
        ·
          refine ⟨4622339587209644608793299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6163119449612859478391065 4622339587209644608793299)
          ·
            refine ⟨6933509380814466913189949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4622339587209644608793299 6933509380814466913189949)
            ·
              refine ⟨2600066017805425092446231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6933509380814466913189949 2600066017805425092446231)
              ·
                refine ⟨3900099026708137638669347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2600066017805425092446231 3900099026708137638669347)
                ·
                  refine ⟨5850148540062206458004021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900099026708137638669347 5850148540062206458004021)
                  ·
                    refine ⟨548451425630831855437877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5850148540062206458004021 548451425630831855437877)
                    ·
                      rfl

theorem cell22_1602158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_1602158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602158 prefixEnd_1602158 := by exact prefixLift 1602158
  have htrace : WordTrace (prefixWord ++ tailWord_1602158) baseStart_1602158 baseEnd_1602158 := by
    simpa [prefixWord, tailWord_1602158, baseEnd_1602158] using wordTrace_append hprefix tailTrace_1602158
  have hstable : (prefixWord ++ tailWord_1602158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602158).length < 2 ^ (prefixWord ++ tailWord_1602158).sum := by decide
  have hdescent : baseEnd_1602158 < baseStart_1602158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602209 : List Nat := [1, 2, 3, 3, 4, 1, 2, 1, 2, 3]
def baseStart_1602209 : Nat := 118140960795 + 1602209 * 2 ^ 59
def prefixEnd_1602209 : Nat := 4983230072969 + 3 ^ 40 * 1602209 * 2
def baseEnd_1602209 : Nat := 548468883973084722412721

theorem tailTrace_1602209 : CollatzResearch.WordTrace tailWord_1602209 prefixEnd_1602209 548468883973084722412721 := by
  unfold tailWord_1602209
  simp only [CollatzResearch.WordTrace]
  refine ⟨58437363052477903357073681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38958242034985268904715787 58437363052477903357073681)
  ·
    refine ⟨43828022289358427517805261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58437363052477903357073681 43828022289358427517805261)
    ·
      refine ⟨16435508358509410319176973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43828022289358427517805261 16435508358509410319176973)
      ·
        refine ⟨6163315634441028869691365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16435508358509410319176973 6163315634441028869691365)
        ·
          refine ⟨1155621681457692913067131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6163315634441028869691365 1155621681457692913067131)
          ·
            refine ⟨1733432522186539369600697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155621681457692913067131 1733432522186539369600697)
            ·
              refine ⟨1300074391639904527200523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1733432522186539369600697 1300074391639904527200523)
              ·
                refine ⟨1950111587459856790800785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1300074391639904527200523 1950111587459856790800785)
                ·
                  refine ⟨1462583690594892593100589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1950111587459856790800785 1462583690594892593100589)
                  ·
                    refine ⟨548468883973084722412721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1462583690594892593100589 548468883973084722412721)
                    ·
                      rfl

theorem cell22_1602209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_1602209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602209 prefixEnd_1602209 := by exact prefixLift 1602209
  have htrace : WordTrace (prefixWord ++ tailWord_1602209) baseStart_1602209 baseEnd_1602209 := by
    simpa [prefixWord, tailWord_1602209, baseEnd_1602209] using wordTrace_append hprefix tailTrace_1602209
  have hstable : (prefixWord ++ tailWord_1602209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602209).length < 2 ^ (prefixWord ++ tailWord_1602209).sum := by decide
  have hdescent : baseEnd_1602209 < baseStart_1602209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602254 : List Nat := [4, 1, 1, 1, 3, 4, 2, 2, 1, 3]
def baseStart_1602254 : Nat := 118140960795 + 1602254 * 2 ^ 59
def prefixEnd_1602254 : Nat := 4983230072969 + 3 ^ 40 * 1602254 * 2
def baseEnd_1602254 : Nat := 548484288392719605037583

theorem tailTrace_1602254 : CollatzResearch.WordTrace tailWord_1602254 prefixEnd_1602254 548484288392719605037583 := by
  unfold tailWord_1602254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7304875542164359505307727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38959336224876584028307877 7304875542164359505307727)
  ·
    refine ⟨10957313313246539257961591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7304875542164359505307727 10957313313246539257961591)
    ·
      refine ⟨16435969969869808886942387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10957313313246539257961591 16435969969869808886942387)
      ·
        refine ⟨24653954954804713330413581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16435969969869808886942387 24653954954804713330413581)
        ·
          refine ⟨9245233108051767498905093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24653954954804713330413581 9245233108051767498905093)
          ·
            refine ⟨1733481207759706406044705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9245233108051767498905093 1733481207759706406044705)
            ·
              refine ⟨1300110905819779804533529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1733481207759706406044705 1300110905819779804533529)
              ·
                refine ⟨975083179364834853400147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1300110905819779804533529 975083179364834853400147)
                ·
                  refine ⟨1462624769047252280100221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 975083179364834853400147 1462624769047252280100221)
                  ·
                    refine ⟨548484288392719605037583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1462624769047252280100221 548484288392719605037583)
                    ·
                      rfl

theorem cell22_1602254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_1602254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602254 prefixEnd_1602254 := by exact prefixLift 1602254
  have htrace : WordTrace (prefixWord ++ tailWord_1602254) baseStart_1602254 baseEnd_1602254 := by
    simpa [prefixWord, tailWord_1602254, baseEnd_1602254] using wordTrace_append hprefix tailTrace_1602254
  have hstable : (prefixWord ++ tailWord_1602254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602254).length < 2 ^ (prefixWord ++ tailWord_1602254).sum := by decide
  have hdescent : baseEnd_1602254 < baseStart_1602254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602308 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_1602308 : Nat := 118140960795 + 1602308 * 2 ^ 59
def prefixEnd_1602308 : Nat := 4983230072969 + 3 ^ 40 * 1602308 * 2
def baseEnd_1602308 : Nat := 548502773696281464187417

theorem tailTrace_1602308 : CollatzResearch.WordTrace tailWord_1602308 prefixEnd_1602308 548502773696281464187417 := by
  unfold tailWord_1602308
  simp only [CollatzResearch.WordTrace]
  refine ⟨29220486939559621632463789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38960649252746162176618385 29220486939559621632463789)
  ·
    refine ⟨10957682602334858112173921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29220486939559621632463789 10957682602334858112173921)
    ·
      refine ⟨8218261951751143584130441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10957682602334858112173921 8218261951751143584130441)
      ·
        refine ⟨6163696463813357688097831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8218261951751143584130441 6163696463813357688097831)
        ·
          refine ⟨9245544695720036532146747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6163696463813357688097831 9245544695720036532146747)
          ·
            refine ⟨13868317043580054798220121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9245544695720036532146747 13868317043580054798220121)
            ·
              refine ⟨10401237782685041098665091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13868317043580054798220121 10401237782685041098665091)
              ·
                refine ⟨15601856674027561647997637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10401237782685041098665091 15601856674027561647997637)
                ·
                  refine ⟨2925348126380167808999557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15601856674027561647997637 2925348126380167808999557)
                  ·
                    refine ⟨548502773696281464187417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2925348126380167808999557 548502773696281464187417)
                    ·
                      rfl

theorem cell22_1602308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_1602308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602308 prefixEnd_1602308 := by exact prefixLift 1602308
  have htrace : WordTrace (prefixWord ++ tailWord_1602308) baseStart_1602308 baseEnd_1602308 := by
    simpa [prefixWord, tailWord_1602308, baseEnd_1602308] using wordTrace_append hprefix tailTrace_1602308
  have hstable : (prefixWord ++ tailWord_1602308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602308).length < 2 ^ (prefixWord ++ tailWord_1602308).sum := by decide
  have hdescent : baseEnd_1602308 < baseStart_1602308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602327 : List Nat := [1, 1, 3, 4, 4, 1, 1, 1, 1, 5]
def baseStart_1602327 : Nat := 118140960795 + 1602327 * 2 ^ 59
def prefixEnd_1602327 : Nat := 4983230072969 + 3 ^ 40 * 1602327 * 2
def baseEnd_1602327 : Nat := 548509277784571747962359

theorem tailTrace_1602327 : CollatzResearch.WordTrace tailWord_1602327 prefixEnd_1602327 548509277784571747962359 := by
  unfold tailWord_1602327
  simp only [CollatzResearch.WordTrace]
  refine ⟨58441666866050409509869235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38961111244033606339912823 58441666866050409509869235)
  ·
    refine ⟨87662500299075614264803853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58441666866050409509869235 87662500299075614264803853)
    ·
      refine ⟨32873437612153355349301445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87662500299075614264803853 32873437612153355349301445)
      ·
        refine ⟨6163769552278754127994021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32873437612153355349301445 6163769552278754127994021)
        ·
          refine ⟨1155706791052266398998879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6163769552278754127994021 1155706791052266398998879)
          ·
            refine ⟨1733560186578399598498319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155706791052266398998879 1733560186578399598498319)
            ·
              refine ⟨2600340279867599397747479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733560186578399598498319 2600340279867599397747479)
              ·
                refine ⟨3900510419801399096621219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2600340279867599397747479 3900510419801399096621219)
                ·
                  refine ⟨5850765629702098644931829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900510419801399096621219 5850765629702098644931829)
                  ·
                    refine ⟨548509277784571747962359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5850765629702098644931829 548509277784571747962359)
                    ·
                      rfl

theorem cell22_1602327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 1, 5].length) (baseStart_1602327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602327 prefixEnd_1602327 := by exact prefixLift 1602327
  have htrace : WordTrace (prefixWord ++ tailWord_1602327) baseStart_1602327 baseEnd_1602327 := by
    simpa [prefixWord, tailWord_1602327, baseEnd_1602327] using wordTrace_append hprefix tailTrace_1602327
  have hstable : (prefixWord ++ tailWord_1602327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602327).length < 2 ^ (prefixWord ++ tailWord_1602327).sum := by decide
  have hdescent : baseEnd_1602327 < baseStart_1602327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602346 : List Nat := [3, 1, 4, 3, 2, 1, 1, 3, 4]
def baseStart_1602346 : Nat := 118140960795 + 1602346 * 2 ^ 59
def prefixEnd_1602346 : Nat := 4983230072969 + 3 ^ 40 * 1602346 * 2
def baseEnd_1602346 : Nat := 182838593957620677245767

theorem tailTrace_1602346 : CollatzResearch.WordTrace tailWord_1602346 prefixEnd_1602346 182838593957620677245767 := by
  unfold tailWord_1602346
  simp only [CollatzResearch.WordTrace]
  refine ⟨14610589963245393938702723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38961573235321050503207261 14610589963245393938702723)
  ·
    refine ⟨21915884944868090908054085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14610589963245393938702723 21915884944868090908054085)
    ·
      refine ⟨4109228427162767045260141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21915884944868090908054085 4109228427162767045260141)
      ·
        refine ⟨1540960660186037641972553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4109228427162767045260141 1540960660186037641972553)
        ·
          refine ⟨1155720495139528231479415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1540960660186037641972553 1155720495139528231479415)
          ·
            refine ⟨1733580742709292347219123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1155720495139528231479415 1733580742709292347219123)
            ·
              refine ⟨2600371114063938520828685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733580742709292347219123 2600371114063938520828685)
              ·
                refine ⟨975139167773976945310757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2600371114063938520828685 975139167773976945310757)
                ·
                  refine ⟨182838593957620677245767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 975139167773976945310757 182838593957620677245767)
                  ·
                    rfl

theorem cell22_1602346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_1602346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602346 prefixEnd_1602346 := by exact prefixLift 1602346
  have htrace : WordTrace (prefixWord ++ tailWord_1602346) baseStart_1602346 baseEnd_1602346 := by
    simpa [prefixWord, tailWord_1602346, baseEnd_1602346] using wordTrace_append hprefix tailTrace_1602346
  have hstable : (prefixWord ++ tailWord_1602346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602346).length < 2 ^ (prefixWord ++ tailWord_1602346).sum := by decide
  have hdescent : baseEnd_1602346 < baseStart_1602346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602385 : List Nat := [1, 2, 2, 1, 6, 1, 1, 3, 5]
def baseStart_1602385 : Nat := 118140960795 + 1602385 * 2 ^ 59
def prefixEnd_1602385 : Nat := 4983230072969 + 3 ^ 40 * 1602385 * 2
def baseEnd_1602385 : Nat := 182843044123292976670727

theorem tailTrace_1602385 : CollatzResearch.WordTrace tailWord_1602385 prefixEnd_1602385 182843044123292976670727 := by
  unfold tailWord_1602385
  simp only [CollatzResearch.WordTrace]
  refine ⟨58443782299840285415480609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38962521533226856943653739 58443782299840285415480609)
  ·
    refine ⟨43832836724880214061610457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58443782299840285415480609 43832836724880214061610457)
    ·
      refine ⟨32874627543660160546207843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43832836724880214061610457 32874627543660160546207843)
      ·
        refine ⟨49311941315490240819311765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32874627543660160546207843 49311941315490240819311765)
        ·
          refine ⟨2311497249163605038405239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49311941315490240819311765 2311497249163605038405239)
          ·
            refine ⟨3467245873745407557607859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2311497249163605038405239 3467245873745407557607859)
            ·
              refine ⟨5200868810618111336411789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3467245873745407557607859 5200868810618111336411789)
              ·
                refine ⟨1950325803981791751154421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5200868810618111336411789 1950325803981791751154421)
                ·
                  refine ⟨182843044123292976670727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1950325803981791751154421 182843044123292976670727)
                  ·
                    rfl

theorem cell22_1602385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 5].length) (baseStart_1602385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602385 prefixEnd_1602385 := by exact prefixLift 1602385
  have htrace : WordTrace (prefixWord ++ tailWord_1602385) baseStart_1602385 baseEnd_1602385 := by
    simpa [prefixWord, tailWord_1602385, baseEnd_1602385] using wordTrace_append hprefix tailTrace_1602385
  have hstable : (prefixWord ++ tailWord_1602385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602385).length < 2 ^ (prefixWord ++ tailWord_1602385).sum := by decide
  have hdescent : baseEnd_1602385 < baseStart_1602385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602434 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_1602434 : Nat := 118140960795 + 1602434 * 2 ^ 59
def prefixEnd_1602434 : Nat := 4983230072969 + 3 ^ 40 * 1602434 * 2
def baseEnd_1602434 : Nat := 548545906071259135537031

theorem tailTrace_1602434 : CollatzResearch.WordTrace tailWord_1602434 prefixEnd_1602434 548545906071259135537031 := by
  unfold tailWord_1602434
  simp only [CollatzResearch.WordTrace]
  refine ⟨14611392369165691696003589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38963712984441844522676237 14611392369165691696003589)
  ·
    refine ⟨2739636069218567193000673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14611392369165691696003589 2739636069218567193000673)
    ·
      refine ⟨2054727051913925394750505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2739636069218567193000673 2054727051913925394750505)
      ·
        refine ⟨1541045288935444046062879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2054727051913925394750505 1541045288935444046062879)
        ·
          refine ⟨2311567933403166069094319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1541045288935444046062879 2311567933403166069094319)
          ·
            refine ⟨3467351900104749103641479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2311567933403166069094319 3467351900104749103641479)
            ·
              refine ⟨5201027850157123655462219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3467351900104749103641479 5201027850157123655462219)
              ·
                refine ⟨7801541775235685483193329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5201027850157123655462219 7801541775235685483193329)
                ·
                  refine ⟨5851156331426764112394997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7801541775235685483193329 5851156331426764112394997)
                  ·
                    refine ⟨548545906071259135537031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5851156331426764112394997 548545906071259135537031)
                    ·
                      rfl

theorem cell22_1602434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_1602434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602434 prefixEnd_1602434 := by exact prefixLift 1602434
  have htrace : WordTrace (prefixWord ++ tailWord_1602434) baseStart_1602434 baseEnd_1602434 := by
    simpa [prefixWord, tailWord_1602434, baseEnd_1602434] using wordTrace_append hprefix tailTrace_1602434
  have hstable : (prefixWord ++ tailWord_1602434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602434).length < 2 ^ (prefixWord ++ tailWord_1602434).sum := by decide
  have hdescent : baseEnd_1602434 < baseStart_1602434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602443 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 4, 4]
def baseStart_1602443 : Nat := 118140960795 + 1602443 * 2 ^ 59
def prefixEnd_1602443 : Nat := 4983230072969 + 3 ^ 40 * 1602443 * 2
def baseEnd_1602443 : Nat := 548548986955186112062003

theorem tailTrace_1602443 : CollatzResearch.WordTrace tailWord_1602443 prefixEnd_1602443 548548986955186112062003 := by
  unfold tailWord_1602443
  simp only [CollatzResearch.WordTrace]
  refine ⟨58445897733630161321091983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38963931822420107547394655 58445897733630161321091983)
  ·
    refine ⟨87668846600445241981637975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58445897733630161321091983 87668846600445241981637975)
    ·
      refine ⟨131503269900667862972456963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87668846600445241981637975 131503269900667862972456963)
      ·
        refine ⟨197254904851001794458685445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131503269900667862972456963 197254904851001794458685445)
        ·
          refine ⟨36985294659562836461003521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197254904851001794458685445 36985294659562836461003521)
          ·
            refine ⟨27738970994672127345752641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36985294659562836461003521 27738970994672127345752641)
            ·
              refine ⟨20804228246004095509314481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27738970994672127345752641 20804228246004095509314481)
              ·
                refine ⟨15603171184503071631985861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20804228246004095509314481 15603171184503071631985861)
                ·
                  refine ⟨2925594597094325930997349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15603171184503071631985861 2925594597094325930997349)
                  ·
                    refine ⟨548548986955186112062003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2925594597094325930997349 548548986955186112062003)
                    ·
                      rfl

theorem cell22_1602443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 4].length) (baseStart_1602443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602443 prefixEnd_1602443 := by exact prefixLift 1602443
  have htrace : WordTrace (prefixWord ++ tailWord_1602443) baseStart_1602443 baseEnd_1602443 := by
    simpa [prefixWord, tailWord_1602443, baseEnd_1602443] using wordTrace_append hprefix tailTrace_1602443
  have hstable : (prefixWord ++ tailWord_1602443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602443).length < 2 ^ (prefixWord ++ tailWord_1602443).sum := by decide
  have hdescent : baseEnd_1602443 < baseStart_1602443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602584 : List Nat := [2, 1, 2, 3, 2, 3, 3, 1, 1, 4]
def baseStart_1602584 : Nat := 118140960795 + 1602584 * 2 ^ 59
def prefixEnd_1602584 : Nat := 4983230072969 + 3 ^ 40 * 1602584 * 2
def baseEnd_1602584 : Nat := 548597254136708744286571

theorem tailTrace_1602584 : CollatzResearch.WordTrace tailWord_1602584 prefixEnd_1602584 548597254136708744286571 := by
  unfold tailWord_1602584
  simp only [CollatzResearch.WordTrace]
  refine ⟨29225520213059671200987403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38967360284079561601316537 29225520213059671200987403)
  ·
    refine ⟨43838280319589506801481105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29225520213059671200987403 43838280319589506801481105)
    ·
      refine ⟨32878710239692130101110829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43838280319589506801481105 32878710239692130101110829)
      ·
        refine ⟨12329516339884548787916561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32878710239692130101110829 12329516339884548787916561)
        ·
          refine ⟨9247137254913411590937421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12329516339884548787916561 9247137254913411590937421)
          ·
            refine ⟨3467676470592529346601533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9247137254913411590937421 3467676470592529346601533)
            ·
              refine ⟨1300378676472198504975575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3467676470592529346601533 1300378676472198504975575)
              ·
                refine ⟨1950568014708297757463363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1300378676472198504975575 1950568014708297757463363)
                ·
                  refine ⟨2925852022062446636195045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1950568014708297757463363 2925852022062446636195045)
                  ·
                    refine ⟨548597254136708744286571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2925852022062446636195045 548597254136708744286571)
                    ·
                      rfl

theorem cell22_1602584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 1, 4].length) (baseStart_1602584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602584 prefixEnd_1602584 := by exact prefixLift 1602584
  have htrace : WordTrace (prefixWord ++ tailWord_1602584) baseStart_1602584 baseEnd_1602584 := by
    simpa [prefixWord, tailWord_1602584, baseEnd_1602584] using wordTrace_append hprefix tailTrace_1602584
  have hstable : (prefixWord ++ tailWord_1602584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602584).length < 2 ^ (prefixWord ++ tailWord_1602584).sum := by decide
  have hdescent : baseEnd_1602584 < baseStart_1602584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602614 : List Nat := [5, 1, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_1602614 : Nat := 118140960795 + 1602614 * 2 ^ 59
def prefixEnd_1602614 : Nat := 4983230072969 + 3 ^ 40 * 1602614 * 2
def baseEnd_1602614 : Nat := 548607523749798666036479

theorem tailTrace_1602614 : CollatzResearch.WordTrace tailWord_1602614 prefixEnd_1602614 548607523749798666036479 := by
  unfold tailWord_1602614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3653258413500666095347931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38968089744007105017044597 3653258413500666095347931)
  ·
    refine ⟨5479887620250999143021897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3653258413500666095347931 5479887620250999143021897)
    ·
      refine ⟨4109915715188249357266423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5479887620250999143021897 4109915715188249357266423)
      ·
        refine ⟨6164873572782374035899635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4109915715188249357266423 6164873572782374035899635)
        ·
          refine ⟨9247310359173561053849453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6164873572782374035899635 9247310359173561053849453)
          ·
            refine ⟨3467741384690085395193545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9247310359173561053849453 3467741384690085395193545)
            ·
              refine ⟨2600806038517564046395159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3467741384690085395193545 2600806038517564046395159)
              ·
                refine ⟨3901209057776346069592739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2600806038517564046395159 3901209057776346069592739)
                ·
                  refine ⟨5851813586664519104389109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3901209057776346069592739 5851813586664519104389109)
                  ·
                    refine ⟨548607523749798666036479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5851813586664519104389109 548607523749798666036479)
                    ·
                      rfl

theorem cell22_1602614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_1602614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602614 prefixEnd_1602614 := by exact prefixLift 1602614
  have htrace : WordTrace (prefixWord ++ tailWord_1602614) baseStart_1602614 baseEnd_1602614 := by
    simpa [prefixWord, tailWord_1602614, baseEnd_1602614] using wordTrace_append hprefix tailTrace_1602614
  have hstable : (prefixWord ++ tailWord_1602614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602614).length < 2 ^ (prefixWord ++ tailWord_1602614).sum := by decide
  have hdescent : baseEnd_1602614 < baseStart_1602614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602655 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 7]
def baseStart_1602655 : Nat := 118140960795 + 1602655 * 2 ^ 59
def prefixEnd_1602655 : Nat := 4983230072969 + 3 ^ 40 * 1602655 * 2
def baseEnd_1602655 : Nat := 182873852962562741920451

theorem tailTrace_1602655 : CollatzResearch.WordTrace tailWord_1602655 prefixEnd_1602655 182873852962562741920451 := by
  unfold tailWord_1602655
  simp only [CollatzResearch.WordTrace]
  refine ⟨58453630008862121527809419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38969086672574747685206279 58453630008862121527809419)
  ·
    refine ⟨87680445013293182291714129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58453630008862121527809419 87680445013293182291714129)
    ·
      refine ⟨65760333759969886718785597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87680445013293182291714129 65760333759969886718785597)
      ·
        refine ⟨24660125159988707519544599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65760333759969886718785597 24660125159988707519544599)
        ·
          refine ⟨36990187739983061279316899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24660125159988707519544599 36990187739983061279316899)
          ·
            refine ⟨55485281609974591918975349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36990187739983061279316899 55485281609974591918975349)
            ·
              refine ⟨5201745150935117992403939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55485281609974591918975349 5201745150935117992403939)
              ·
                refine ⟨7802617726402676988605909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5201745150935117992403939 7802617726402676988605909)
                ·
                  refine ⟨182873852962562741920451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7802617726402676988605909 182873852962562741920451)
                  ·
                    rfl

theorem cell22_1602655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 7].length) (baseStart_1602655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602655 prefixEnd_1602655 := by exact prefixLift 1602655
  have htrace : WordTrace (prefixWord ++ tailWord_1602655) baseStart_1602655 baseEnd_1602655 := by
    simpa [prefixWord, tailWord_1602655, baseEnd_1602655] using wordTrace_append hprefix tailTrace_1602655
  have hstable : (prefixWord ++ tailWord_1602655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602655).length < 2 ^ (prefixWord ++ tailWord_1602655).sum := by decide
  have hdescent : baseEnd_1602655 < baseStart_1602655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602693 : List Nat := [1, 3, 1, 1, 6, 2, 1, 3, 1, 3]
def baseStart_1602693 : Nat := 118140960795 + 1602693 * 2 ^ 59
def prefixEnd_1602693 : Nat := 4983230072969 + 3 ^ 40 * 1602693 * 2
def baseEnd_1602693 : Nat := 548634567064268793311237

theorem tailTrace_1602693 : CollatzResearch.WordTrace tailWord_1602693 prefixEnd_1602693 548634567064268793311237 := by
  unfold tailWord_1602693
  simp only [CollatzResearch.WordTrace]
  refine ⟨58455015982724454017692733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38970010655149636011795155 58455015982724454017692733)
  ·
    refine ⟨21920630993521670256634775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58455015982724454017692733 21920630993521670256634775)
    ·
      refine ⟨32880946490282505384952163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21920630993521670256634775 32880946490282505384952163)
      ·
        refine ⟨49321419735423758077428245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32880946490282505384952163 49321419735423758077428245)
        ·
          refine ⟨2311941550097988659879449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49321419735423758077428245 2311941550097988659879449)
          ·
            refine ⟨1733956162573491494909587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2311941550097988659879449 1733956162573491494909587)
            ·
              refine ⟨2600934243860237242364381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1733956162573491494909587 2600934243860237242364381)
              ·
                refine ⟨975350341447588965886643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2600934243860237242364381 975350341447588965886643)
                ·
                  refine ⟨1463025512171383448829965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 975350341447588965886643 1463025512171383448829965)
                  ·
                    refine ⟨548634567064268793311237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1463025512171383448829965 548634567064268793311237)
                    ·
                      rfl

theorem cell22_1602693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 1, 3].length) (baseStart_1602693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602693 prefixEnd_1602693 := by exact prefixLift 1602693
  have htrace : WordTrace (prefixWord ++ tailWord_1602693) baseStart_1602693 baseEnd_1602693 := by
    simpa [prefixWord, tailWord_1602693, baseEnd_1602693] using wordTrace_append hprefix tailTrace_1602693
  have hstable : (prefixWord ++ tailWord_1602693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602693).length < 2 ^ (prefixWord ++ tailWord_1602693).sum := by decide
  have hdescent : baseEnd_1602693 < baseStart_1602693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602700 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 8]
def baseStart_1602700 : Nat := 118140960795 + 1602700 * 2 ^ 59
def prefixEnd_1602700 : Nat := 4983230072969 + 3 ^ 40 * 1602700 * 2
def baseEnd_1602700 : Nat := 182878987769107702795405

theorem tailTrace_1602700 : CollatzResearch.WordTrace tailWord_1602700 prefixEnd_1602700 182878987769107702795405 := by
  unfold tailWord_1602700
  simp only [CollatzResearch.WordTrace]
  refine ⟨29227635646849547106598777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38970180862466062808798369 29227635646849547106598777)
  ·
    refine ⟨21920726735137160329949083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29227635646849547106598777 21920726735137160329949083)
    ·
      refine ⟨32881090102705740494923625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21920726735137160329949083 32881090102705740494923625)
      ·
        refine ⟨24660817577029305371192719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32881090102705740494923625 24660817577029305371192719)
        ·
          refine ⟨36991226365543958056789079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24660817577029305371192719 36991226365543958056789079)
          ·
            refine ⟨55486839548315937085183619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36991226365543958056789079 55486839548315937085183619)
            ·
              refine ⟨83230259322473905627775429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55486839548315937085183619 83230259322473905627775429)
              ·
                refine ⟨15605673622963857305207893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83230259322473905627775429 15605673622963857305207893)
                ·
                  refine ⟨182878987769107702795405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15605673622963857305207893 182878987769107702795405)
                  ·
                    rfl

theorem cell22_1602700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_1602700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602700 prefixEnd_1602700 := by exact prefixLift 1602700
  have htrace : WordTrace (prefixWord ++ tailWord_1602700) baseStart_1602700 baseEnd_1602700 := by
    simpa [prefixWord, tailWord_1602700, baseEnd_1602700] using wordTrace_append hprefix tailTrace_1602700
  have hstable : (prefixWord ++ tailWord_1602700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602700).length < 2 ^ (prefixWord ++ tailWord_1602700).sum := by decide
  have hdescent : baseEnd_1602700 < baseStart_1602700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602732 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 6, 3]
def baseStart_1602732 : Nat := 118140960795 + 1602732 * 2 ^ 59
def prefixEnd_1602732 : Nat := 4983230072969 + 3 ^ 40 * 1602732 * 2
def baseEnd_1602732 : Nat := 548647917561285691586117

theorem tailTrace_1602732 : CollatzResearch.WordTrace tailWord_1602732 prefixEnd_1602732 548647917561285691586117 := by
  unfold tailWord_1602732
  simp only [CollatzResearch.WordTrace]
  refine ⟨29228219214791581839181225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38970958953055442452241633 29228219214791581839181225)
  ·
    refine ⟨21921164411093686379385919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29228219214791581839181225 21921164411093686379385919)
    ·
      refine ⟨32881746616640529569078879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21921164411093686379385919 32881746616640529569078879)
      ·
        refine ⟨49322619924960794353618319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32881746616640529569078879 49322619924960794353618319)
        ·
          refine ⟨73983929887441191530427479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49322619924960794353618319 73983929887441191530427479)
          ·
            refine ⟨110975894831161787295641219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73983929887441191530427479 110975894831161787295641219)
            ·
              refine ⟨166463842246742680943461829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110975894831161787295641219 166463842246742680943461829)
              ·
                refine ⟨31211970421264252676899093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166463842246742680943461829 31211970421264252676899093)
                ·
                  refine ⟨1463061113496761844229645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 31211970421264252676899093 1463061113496761844229645)
                  ·
                    refine ⟨548647917561285691586117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1463061113496761844229645 548647917561285691586117)
                    ·
                      rfl

theorem cell22_1602732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 3].length) (baseStart_1602732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602732 prefixEnd_1602732 := by exact prefixLift 1602732
  have htrace : WordTrace (prefixWord ++ tailWord_1602732) baseStart_1602732 baseEnd_1602732 := by
    simpa [prefixWord, tailWord_1602732, baseEnd_1602732] using wordTrace_append hprefix tailTrace_1602732
  have hstable : (prefixWord ++ tailWord_1602732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602732).length < 2 ^ (prefixWord ++ tailWord_1602732).sum := by decide
  have hdescent : baseEnd_1602732 < baseStart_1602732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602753 : List Nat := [1, 2, 6, 1, 1, 2, 3, 1, 1, 4]
def baseStart_1602753 : Nat := 118140960795 + 1602753 * 2 ^ 59
def prefixEnd_1602753 : Nat := 4983230072969 + 3 ^ 40 * 1602753 * 2
def baseEnd_1602753 : Nat := 548655106290448636811053

theorem tailTrace_1602753 : CollatzResearch.WordTrace tailWord_1602753 prefixEnd_1602753 548655106290448636811053 := by
  unfold tailWord_1602753
  simp only [CollatzResearch.WordTrace]
  refine ⟨58457204362507084264876913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38971469575004722843251275 58457204362507084264876913)
  ·
    refine ⟨43842903271880313198657685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58457204362507084264876913 43842903271880313198657685)
    ·
      refine ⟨2055136090869389681187079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43842903271880313198657685 2055136090869389681187079)
      ·
        refine ⟨3082704136304084521780619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2055136090869389681187079 3082704136304084521780619)
        ·
          refine ⟨4624056204456126782670929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3082704136304084521780619 4624056204456126782670929)
          ·
            refine ⟨3468042153342095087003197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4624056204456126782670929 3468042153342095087003197)
            ·
              refine ⟨1300515807503285657626199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3468042153342095087003197 1300515807503285657626199)
              ·
                refine ⟨1950773711254928486439299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1300515807503285657626199 1950773711254928486439299)
                ·
                  refine ⟨2926160566882392729658949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1950773711254928486439299 2926160566882392729658949)
                  ·
                    refine ⟨548655106290448636811053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2926160566882392729658949 548655106290448636811053)
                    ·
                      rfl

theorem cell22_1602753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_1602753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602753 prefixEnd_1602753 := by exact prefixLift 1602753
  have htrace : WordTrace (prefixWord ++ tailWord_1602753) baseStart_1602753 baseEnd_1602753 := by
    simpa [prefixWord, tailWord_1602753, baseEnd_1602753] using wordTrace_append hprefix tailTrace_1602753
  have hstable : (prefixWord ++ tailWord_1602753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602753).length < 2 ^ (prefixWord ++ tailWord_1602753).sum := by decide
  have hdescent : baseEnd_1602753 < baseStart_1602753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602792 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 2, 6]
def baseStart_1602792 : Nat := 118140960795 + 1602792 * 2 ^ 59
def prefixEnd_1602792 : Nat := 4983230072969 + 3 ^ 40 * 1602792 * 2
def baseEnd_1602792 : Nat := 548668456787465535085933

theorem tailTrace_1602792 : CollatzResearch.WordTrace tailWord_1602792 prefixEnd_1602792 548668456787465535085933 := by
  unfold tailWord_1602792
  simp only [CollatzResearch.WordTrace]
  refine ⟨29229313404682896962773315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38972417872910529283697753 29229313404682896962773315)
  ·
    refine ⟨43843970107024345444159973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29229313404682896962773315 43843970107024345444159973)
    ·
      refine ⟨8220744395067064770779995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43843970107024345444159973 8220744395067064770779995)
      ·
        refine ⟨12331116592600597156169993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8220744395067064770779995 12331116592600597156169993)
        ·
          refine ⟨9248337444450447867127495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12331116592600597156169993 9248337444450447867127495)
          ·
            refine ⟨13872506166675671800691243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9248337444450447867127495 13872506166675671800691243)
            ·
              refine ⟨20808759250013507701036865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13872506166675671800691243 20808759250013507701036865)
              ·
                refine ⟨15606569437510130775777649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20808759250013507701036865 15606569437510130775777649)
                ·
                  refine ⟨11704927078132598081833237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15606569437510130775777649 11704927078132598081833237)
                  ·
                    refine ⟨548668456787465535085933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11704927078132598081833237 548668456787465535085933)
                    ·
                      rfl

theorem cell22_1602792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_1602792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602792 prefixEnd_1602792 := by exact prefixLift 1602792
  have htrace : WordTrace (prefixWord ++ tailWord_1602792) baseStart_1602792 baseEnd_1602792 := by
    simpa [prefixWord, tailWord_1602792, baseEnd_1602792] using wordTrace_append hprefix tailTrace_1602792
  have hstable : (prefixWord ++ tailWord_1602792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602792).length < 2 ^ (prefixWord ++ tailWord_1602792).sum := by decide
  have hdescent : baseEnd_1602792 < baseStart_1602792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602794 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 5, 3]
def baseStart_1602794 : Nat := 118140960795 + 1602794 * 2 ^ 59
def prefixEnd_1602794 : Nat := 4983230072969 + 3 ^ 40 * 1602794 * 2
def baseEnd_1602794 : Nat := 548669141428338196535927

theorem tailTrace_1602794 : CollatzResearch.WordTrace tailWord_1602794 prefixEnd_1602794 548669141428338196535927 := by
  unfold tailWord_1602794
  simp only [CollatzResearch.WordTrace]
  refine ⟨14614674938839637066779859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38972466503572365511412957 14614674938839637066779859)
  ·
    refine ⟨21922012408259455600169789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14614674938839637066779859 21922012408259455600169789)
    ·
      refine ⟨8220754653097295850063671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21922012408259455600169789 8220754653097295850063671)
      ·
        refine ⟨12331131979645943775095507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8220754653097295850063671 12331131979645943775095507)
        ·
          refine ⟨18496697969468915662643261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12331131979645943775095507 18496697969468915662643261)
          ·
            refine ⟨6936261738550843373491223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18496697969468915662643261 6936261738550843373491223)
            ·
              refine ⟨10404392607826265060236835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6936261738550843373491223 10404392607826265060236835)
              ·
                refine ⟨15606588911739397590355253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10404392607826265060236835 15606588911739397590355253)
                ·
                  refine ⟨1463117710475568524095805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15606588911739397590355253 1463117710475568524095805)
                  ·
                    refine ⟨548669141428338196535927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1463117710475568524095805 548669141428338196535927)
                    ·
                      rfl

theorem cell22_1602794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_1602794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602794 prefixEnd_1602794 := by exact prefixLift 1602794
  have htrace : WordTrace (prefixWord ++ tailWord_1602794) baseStart_1602794 baseEnd_1602794 := by
    simpa [prefixWord, tailWord_1602794, baseEnd_1602794] using wordTrace_append hprefix tailTrace_1602794
  have hstable : (prefixWord ++ tailWord_1602794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602794).length < 2 ^ (prefixWord ++ tailWord_1602794).sum := by decide
  have hdescent : baseEnd_1602794 < baseStart_1602794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602804 : List Nat := [2, 6, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_1602804 : Nat := 118140960795 + 1602804 * 2 ^ 59
def prefixEnd_1602804 : Nat := 4983230072969 + 3 ^ 40 * 1602804 * 2
def baseEnd_1602804 : Nat := 548672564632701503785897

theorem tailTrace_1602804 : CollatzResearch.WordTrace tailWord_1602804 prefixEnd_1602804 548672564632701503785897 := by
  unfold tailWord_1602804
  simp only [CollatzResearch.WordTrace]
  refine ⟨29229532242661159987491733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38972709656881546649988977 29229532242661159987491733)
  ·
    refine ⟨1370134323874741874413675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 29229532242661159987491733 1370134323874741874413675)
    ·
      refine ⟨2055201485812112811620513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1370134323874741874413675 2055201485812112811620513)
      ·
        refine ⟨1541401114359084608715385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2055201485812112811620513 1541401114359084608715385)
        ·
          refine ⟨1156050835769313456536539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1541401114359084608715385 1156050835769313456536539)
          ·
            refine ⟨1734076253653970184804809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1156050835769313456536539 1734076253653970184804809)
            ·
              refine ⟨1300557190240477638603607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1734076253653970184804809 1300557190240477638603607)
              ·
                refine ⟨1950835785360716457905411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1300557190240477638603607 1950835785360716457905411)
                ·
                  refine ⟨2926253678041074686858117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1950835785360716457905411 2926253678041074686858117)
                  ·
                    refine ⟨548672564632701503785897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2926253678041074686858117 548672564632701503785897)
                    ·
                      rfl

theorem cell22_1602804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_1602804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602804 prefixEnd_1602804 := by exact prefixLift 1602804
  have htrace : WordTrace (prefixWord ++ tailWord_1602804) baseStart_1602804 baseEnd_1602804 := by
    simpa [prefixWord, tailWord_1602804, baseEnd_1602804] using wordTrace_append hprefix tailTrace_1602804
  have hstable : (prefixWord ++ tailWord_1602804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602804).length < 2 ^ (prefixWord ++ tailWord_1602804).sum := by decide
  have hdescent : baseEnd_1602804 < baseStart_1602804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602824 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 7]
def baseStart_1602824 : Nat := 118140960795 + 1602824 * 2 ^ 59
def prefixEnd_1602824 : Nat := 4983230072969 + 3 ^ 40 * 1602824 * 2
def baseEnd_1602824 : Nat := 182893137013809372761945

theorem tailTrace_1602824 : CollatzResearch.WordTrace tailWord_1602824 prefixEnd_1602824 182893137013809372761945 := by
  unfold tailWord_1602824
  simp only [CollatzResearch.WordTrace]
  refine ⟨29229896972624931695355763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38973195963499908927141017 29229896972624931695355763)
  ·
    refine ⟨43844845458937397543033645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29229896972624931695355763 43844845458937397543033645)
    ·
      refine ⟨16441817047101524078637617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43844845458937397543033645 16441817047101524078637617)
      ·
        refine ⟨12331362785326143058978213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16441817047101524078637617 12331362785326143058978213)
        ·
          refine ⟨2312130522248651823558415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12331362785326143058978213 2312130522248651823558415)
          ·
            refine ⟨3468195783372977735337623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2312130522248651823558415 3468195783372977735337623)
            ·
              refine ⟨5202293675059466603006435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3468195783372977735337623 5202293675059466603006435)
              ·
                refine ⟨7803440512589199904509653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5202293675059466603006435 7803440512589199904509653)
                ·
                  refine ⟨182893137013809372761945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7803440512589199904509653 182893137013809372761945)
                  ·
                    rfl

theorem cell22_1602824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 7].length) (baseStart_1602824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602824 prefixEnd_1602824 := by exact prefixLift 1602824
  have htrace : WordTrace (prefixWord ++ tailWord_1602824) baseStart_1602824 baseEnd_1602824 := by
    simpa [prefixWord, tailWord_1602824, baseEnd_1602824] using wordTrace_append hprefix tailTrace_1602824
  have hstable : (prefixWord ++ tailWord_1602824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602824).length < 2 ^ (prefixWord ++ tailWord_1602824).sum := by decide
  have hdescent : baseEnd_1602824 < baseStart_1602824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602914 : List Nat := [3, 3, 2, 1, 1, 1, 1, 10]
def baseStart_1602914 : Nat := 118140960795 + 1602914 * 2 ^ 59
def prefixEnd_1602914 : Nat := 4983230072969 + 3 ^ 40 * 1602914 * 2
def baseEnd_1602914 : Nat := 60967802208966431503951

theorem tailTrace_1602914 : CollatzResearch.WordTrace tailWord_1602914 prefixEnd_1602914 60967802208966431503951 := by
  unfold tailWord_1602914
  simp only [CollatzResearch.WordTrace]
  refine ⟨14615769128730952190371949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38975384343282539174325197 14615769128730952190371949)
  ·
    refine ⟨5480913423274107071389481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14615769128730952190371949 5480913423274107071389481)
    ·
      refine ⟨4110685067455580303542111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5480913423274107071389481 4110685067455580303542111)
      ·
        refine ⟨6166027601183370455313167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4110685067455580303542111 6166027601183370455313167)
        ·
          refine ⟨9249041401775055682969751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6166027601183370455313167 9249041401775055682969751)
          ·
            refine ⟨13873562102662583524454627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9249041401775055682969751 13873562102662583524454627)
            ·
              refine ⟨20810343153993875286681941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13873562102662583524454627 20810343153993875286681941)
              ·
                refine ⟨60967802208966431503951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20810343153993875286681941 60967802208966431503951)
                ·
                  rfl

theorem cell22_1602914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 10].length) (baseStart_1602914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602914 prefixEnd_1602914 := by exact prefixLift 1602914
  have htrace : WordTrace (prefixWord ++ tailWord_1602914) baseStart_1602914 baseEnd_1602914 := by
    simpa [prefixWord, tailWord_1602914, baseEnd_1602914] using wordTrace_append hprefix tailTrace_1602914
  have hstable : (prefixWord ++ tailWord_1602914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602914).length < 2 ^ (prefixWord ++ tailWord_1602914).sum := by decide
  have hdescent : baseEnd_1602914 < baseStart_1602914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1602916 : List Nat := [2, 3, 1, 1, 3, 3, 2, 1, 2, 4]
def baseStart_1602916 : Nat := 118140960795 + 1602916 * 2 ^ 59
def prefixEnd_1602916 : Nat := 4983230072969 + 3 ^ 40 * 1602916 * 2
def baseEnd_1602916 : Nat := 548710904521570544985553

theorem tailTrace_1602916 : CollatzResearch.WordTrace tailWord_1602916 prefixEnd_1602916 548710904521570544985553 := by
  unfold tailWord_1602916
  simp only [CollatzResearch.WordTrace]
  refine ⟨29231574730458281551530301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38975432973944375402040401 29231574730458281551530301)
  ·
    refine ⟨10961840523921855581823863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29231574730458281551530301 10961840523921855581823863)
    ·
      refine ⟨16442760785882783372735795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10961840523921855581823863 16442760785882783372735795)
      ·
        refine ⟨24664141178824175059103693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16442760785882783372735795 24664141178824175059103693)
        ·
          refine ⟨9249052942059065647163885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24664141178824175059103693 9249052942059065647163885)
          ·
            refine ⟨3468394853272149617686457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9249052942059065647163885 3468394853272149617686457)
            ·
              refine ⟨2601296139954112213264843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3468394853272149617686457 2601296139954112213264843)
              ·
                refine ⟨3901944209931168319897265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2601296139954112213264843 3901944209931168319897265)
                ·
                  refine ⟨2926458157448376239922949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3901944209931168319897265 2926458157448376239922949)
                  ·
                    refine ⟨548710904521570544985553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2926458157448376239922949 548710904521570544985553)
                    ·
                      rfl

theorem cell22_1602916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_1602916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1602916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1602916 prefixEnd_1602916 := by exact prefixLift 1602916
  have htrace : WordTrace (prefixWord ++ tailWord_1602916) baseStart_1602916 baseEnd_1602916 := by
    simpa [prefixWord, tailWord_1602916, baseEnd_1602916] using wordTrace_append hprefix tailTrace_1602916
  have hstable : (prefixWord ++ tailWord_1602916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1602916).length < 2 ^ (prefixWord ++ tailWord_1602916).sum := by decide
  have hdescent : baseEnd_1602916 < baseStart_1602916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1602916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603081 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 5, 3]
def baseStart_1603081 : Nat := 118140960795 + 1603081 * 2 ^ 59
def prefixEnd_1603081 : Nat := 4983230072969 + 3 ^ 40 * 1603081 * 2
def baseEnd_1603081 : Nat := 548767387393565114610047

theorem tailTrace_1603081 : CollatzResearch.WordTrace tailWord_1603081 prefixEnd_1603081 548767387393565114610047 := by
  unfold tailWord_1603081
  simp only [CollatzResearch.WordTrace]
  refine ⟨58469167505318796282817097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38979445003545864188544731 58469167505318796282817097)
  ·
    refine ⟨43851875628989097212112823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58469167505318796282817097 43851875628989097212112823)
    ·
      refine ⟨65777813443483645818169235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43851875628989097212112823 65777813443483645818169235)
      ·
        refine ⟨98666720165225468727253853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65777813443483645818169235 98666720165225468727253853)
        ·
          refine ⟨37000020061959550772720195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98666720165225468727253853 37000020061959550772720195)
          ·
            refine ⟨55500030092939326159080293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37000020061959550772720195 55500030092939326159080293)
            ·
              refine ⟨10406255642426123654827555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55500030092939326159080293 10406255642426123654827555)
              ·
                refine ⟨15609383463639185482241333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10406255642426123654827555 15609383463639185482241333)
                ·
                  refine ⟨1463379699716173638960125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15609383463639185482241333 1463379699716173638960125)
                  ·
                    refine ⟨548767387393565114610047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1463379699716173638960125 548767387393565114610047)
                    ·
                      rfl

theorem cell22_1603081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 5, 3].length) (baseStart_1603081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603081 prefixEnd_1603081 := by exact prefixLift 1603081
  have htrace : WordTrace (prefixWord ++ tailWord_1603081) baseStart_1603081 baseEnd_1603081 := by
    simpa [prefixWord, tailWord_1603081, baseEnd_1603081] using wordTrace_append hprefix tailTrace_1603081
  have hstable : (prefixWord ++ tailWord_1603081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603081).length < 2 ^ (prefixWord ++ tailWord_1603081).sum := by decide
  have hdescent : baseEnd_1603081 < baseStart_1603081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603141 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 3, 4]
def baseStart_1603141 : Nat := 118140960795 + 1603141 * 2 ^ 59
def prefixEnd_1603141 : Nat := 4983230072969 + 3 ^ 40 * 1603141 * 2
def baseEnd_1603141 : Nat := 548787926619744958109863

theorem tailTrace_1603141 : CollatzResearch.WordTrace tailWord_1603141 prefixEnd_1603141 548787926619744958109863 := by
  unfold tailWord_1603141
  simp only [CollatzResearch.WordTrace]
  refine ⟨58471355885101426530001277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38980903923400951020000851 58471355885101426530001277)
  ·
    refine ⟨21926758456913034948750479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58471355885101426530001277 21926758456913034948750479)
    ·
      refine ⟨32890137685369552423125719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21926758456913034948750479 32890137685369552423125719)
      ·
        refine ⟨49335206528054328634688579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32890137685369552423125719 49335206528054328634688579)
        ·
          refine ⟨74002809792081492952032869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49335206528054328634688579 74002809792081492952032869)
          ·
            refine ⟨13875526836015279928506163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74002809792081492952032869 13875526836015279928506163)
            ·
              refine ⟨20813290254022919892759245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13875526836015279928506163 20813290254022919892759245)
              ·
                refine ⟨7804983845258594959784717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20813290254022919892759245 7804983845258594959784717)
                ·
                  refine ⟨2926868941971973109919269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7804983845258594959784717 2926868941971973109919269)
                  ·
                    refine ⟨548787926619744958109863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2926868941971973109919269 548787926619744958109863)
                    ·
                      rfl

theorem cell22_1603141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_1603141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603141 prefixEnd_1603141 := by exact prefixLift 1603141
  have htrace : WordTrace (prefixWord ++ tailWord_1603141) baseStart_1603141 baseEnd_1603141 := by
    simpa [prefixWord, tailWord_1603141, baseEnd_1603141] using wordTrace_append hprefix tailTrace_1603141
  have hstable : (prefixWord ++ tailWord_1603141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603141).length < 2 ^ (prefixWord ++ tailWord_1603141).sum := by decide
  have hdescent : baseEnd_1603141 < baseStart_1603141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603149 : List Nat := [1, 6, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_1603149 : Nat := 118140960795 + 1603149 * 2 ^ 59
def prefixEnd_1603149 : Nat := 4983230072969 + 3 ^ 40 * 1603149 * 2
def baseEnd_1603149 : Nat := 548790665183235603909839

theorem tailTrace_1603149 : CollatzResearch.WordTrace tailWord_1603149 prefixEnd_1603149 548790665183235603909839 := by
  unfold tailWord_1603149
  simp only [CollatzResearch.WordTrace]
  refine ⟨58471647669072443896292501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38981098446048295930861667 58471647669072443896292501)
  ·
    refine ⟨2740858484487770807638711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58471647669072443896292501 2740858484487770807638711)
    ·
      refine ⟨4111287726731656211458067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2740858484487770807638711 4111287726731656211458067)
      ·
        refine ⟨6166931590097484317187101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4111287726731656211458067 6166931590097484317187101)
        ·
          refine ⟨2312599346286556618945163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6166931590097484317187101 2312599346286556618945163)
          ·
            refine ⟨3468899019429834928417745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2312599346286556618945163 3468899019429834928417745)
            ·
              refine ⟨2601674264572376196313309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3468899019429834928417745 2601674264572376196313309)
              ·
                refine ⟨975627849214641073617491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2601674264572376196313309 975627849214641073617491)
                ·
                  refine ⟨1463441773821961610426237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 975627849214641073617491 1463441773821961610426237)
                  ·
                    refine ⟨548790665183235603909839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1463441773821961610426237 548790665183235603909839)
                    ·
                      rfl

theorem cell22_1603149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_1603149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603149 prefixEnd_1603149 := by exact prefixLift 1603149
  have htrace : WordTrace (prefixWord ++ tailWord_1603149) baseStart_1603149 baseEnd_1603149 := by
    simpa [prefixWord, tailWord_1603149, baseEnd_1603149] using wordTrace_append hprefix tailTrace_1603149
  have hstable : (prefixWord ++ tailWord_1603149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603149).length < 2 ^ (prefixWord ++ tailWord_1603149).sum := by decide
  have hdescent : baseEnd_1603149 < baseStart_1603149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603156 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 8]
def baseStart_1603156 : Nat := 118140960795 + 1603156 * 2 ^ 59
def prefixEnd_1603156 : Nat := 4983230072969 + 3 ^ 40 * 1603156 * 2
def baseEnd_1603156 : Nat := 182931020475429972994939

theorem tailTrace_1603156 : CollatzResearch.WordTrace tailWord_1603156 prefixEnd_1603156 182931020475429972994939 := by
  unfold tailWord_1603156
  simp only [CollatzResearch.WordTrace]
  refine ⟨29235951490023542045898661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38981268653364722727864881 29235951490023542045898661)
  ·
    refine ⟨5481740904379414133605999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29235951490023542045898661 5481740904379414133605999)
    ·
      refine ⟨8222611356569121200408999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5481740904379414133605999 8222611356569121200408999)
      ·
        refine ⟨12333917034853681800613499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8222611356569121200408999 12333917034853681800613499)
        ·
          refine ⟨18500875552280522700920249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12333917034853681800613499 18500875552280522700920249)
          ·
            refine ⟨13875656664210392025690187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18500875552280522700920249 13875656664210392025690187)
            ·
              refine ⟨20813484996315588038535281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13875656664210392025690187 20813484996315588038535281)
              ·
                refine ⟨15610113747236691028901461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20813484996315588038535281 15610113747236691028901461)
                ·
                  refine ⟨182931020475429972994939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15610113747236691028901461 182931020475429972994939)
                  ·
                    rfl

theorem cell22_1603156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_1603156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603156 prefixEnd_1603156 := by exact prefixLift 1603156
  have htrace : WordTrace (prefixWord ++ tailWord_1603156) baseStart_1603156 baseEnd_1603156 := by
    simpa [prefixWord, tailWord_1603156, baseEnd_1603156] using wordTrace_append hprefix tailTrace_1603156
  have hstable : (prefixWord ++ tailWord_1603156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603156).length < 2 ^ (prefixWord ++ tailWord_1603156).sum := by decide
  have hdescent : baseEnd_1603156 < baseStart_1603156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603173 : List Nat := [1, 3, 1, 3, 3, 2, 2, 1, 6]
def baseStart_1603173 : Nat := 118140960795 + 1603173 * 2 ^ 59
def prefixEnd_1603173 : Nat := 4983230072969 + 3 ^ 40 * 1603173 * 2
def baseEnd_1603173 : Nat := 182932960291235847103255

theorem tailTrace_1603173 : CollatzResearch.WordTrace tailWord_1603173 prefixEnd_1603173 182932960291235847103255 := by
  unfold tailWord_1603173
  simp only [CollatzResearch.WordTrace]
  refine ⟨58472523020985495995166173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38981682013990330663444115 58472523020985495995166173)
  ·
    refine ⟨21927196132869560998187315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58472523020985495995166173 21927196132869560998187315)
    ·
      refine ⟨32890794199304341497280973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21927196132869560998187315 32890794199304341497280973)
      ·
        refine ⟨12334047824739128061480365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32890794199304341497280973 12334047824739128061480365)
        ·
          refine ⟨4625267934277173023055137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12334047824739128061480365 4625267934277173023055137)
          ·
            refine ⟨3468950950707879767291353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4625267934277173023055137 3468950950707879767291353)
            ·
              refine ⟨2601713213030909825468515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3468950950707879767291353 2601713213030909825468515)
              ·
                refine ⟨3902569819546364738202773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2601713213030909825468515 3902569819546364738202773)
                ·
                  refine ⟨182932960291235847103255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3902569819546364738202773 182932960291235847103255)
                  ·
                    rfl

theorem cell22_1603173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_1603173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603173 prefixEnd_1603173 := by exact prefixLift 1603173
  have htrace : WordTrace (prefixWord ++ tailWord_1603173) baseStart_1603173 baseEnd_1603173 := by
    simpa [prefixWord, tailWord_1603173, baseEnd_1603173] using wordTrace_append hprefix tailTrace_1603173
  have hstable : (prefixWord ++ tailWord_1603173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603173).length < 2 ^ (prefixWord ++ tailWord_1603173).sum := by decide
  have hdescent : baseEnd_1603173 < baseStart_1603173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603278 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_1603278 : Nat := 118140960795 + 1603278 * 2 ^ 59
def prefixEnd_1603278 : Nat := 4983230072969 + 3 ^ 40 * 1603278 * 2
def baseEnd_1603278 : Nat := 548834824519522267434443

theorem tailTrace_1603278 : CollatzResearch.WordTrace tailWord_1603278 prefixEnd_1603278 548834824519522267434443 := by
  unfold tailWord_1603278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7309544085700637365967311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38984235123736732618492325 7309544085700637365967311)
  ·
    refine ⟨10964316128550956048950967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7309544085700637365967311 10964316128550956048950967)
    ·
      refine ⟨16446474192826434073426451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10964316128550956048950967 16446474192826434073426451)
      ·
        refine ⟨24669711289239651110139677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16446474192826434073426451 24669711289239651110139677)
        ·
          refine ⟨9251141733464869166302379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24669711289239651110139677 9251141733464869166302379)
          ·
            refine ⟨13876712600197303749453569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9251141733464869166302379 13876712600197303749453569)
            ·
              refine ⟨10407534450147977812090177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13876712600197303749453569 10407534450147977812090177)
              ·
                refine ⟨7805650837610983359067633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10407534450147977812090177 7805650837610983359067633)
                ·
                  refine ⟨5854238128208237519300725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7805650837610983359067633 5854238128208237519300725)
                  ·
                    refine ⟨548834824519522267434443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5854238128208237519300725 548834824519522267434443)
                    ·
                      rfl

theorem cell22_1603278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_1603278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603278 prefixEnd_1603278 := by exact prefixLift 1603278
  have htrace : WordTrace (prefixWord ++ tailWord_1603278) baseStart_1603278 baseEnd_1603278 := by
    simpa [prefixWord, tailWord_1603278, baseEnd_1603278] using wordTrace_append hprefix tailTrace_1603278
  have hstable : (prefixWord ++ tailWord_1603278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603278).length < 2 ^ (prefixWord ++ tailWord_1603278).sum := by decide
  have hdescent : baseEnd_1603278 < baseStart_1603278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603284 : List Nat := [2, 4, 1, 3, 1, 2, 1, 4, 1, 3]
def baseStart_1603284 : Nat := 118140960795 + 1603284 * 2 ^ 59
def prefixEnd_1603284 : Nat := 4983230072969 + 3 ^ 40 * 1603284 * 2
def baseEnd_1603284 : Nat := 548836878442140251784425

theorem tailTrace_1603284 : CollatzResearch.WordTrace tailWord_1603284 prefixEnd_1603284 548836878442140251784425 := by
  unfold tailWord_1603284
  simp only [CollatzResearch.WordTrace]
  refine ⟨29238285761791680976228453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38984381015722241301637937 29238285761791680976228453)
  ·
    refine ⟨5482178580335940183042835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29238285761791680976228453 5482178580335940183042835)
    ·
      refine ⟨8223267870503910274564253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5482178580335940183042835 8223267870503910274564253)
      ·
        refine ⟨3083725451438966352961595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8223267870503910274564253 3083725451438966352961595)
        ·
          refine ⟨4625588177158449529442393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3083725451438966352961595 4625588177158449529442393)
          ·
            refine ⟨3469191132868837147081795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4625588177158449529442393 3469191132868837147081795)
            ·
              refine ⟨5203786699303255720622693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3469191132868837147081795 5203786699303255720622693)
              ·
                refine ⟨975710006119360447616755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5203786699303255720622693 975710006119360447616755)
                ·
                  refine ⟨1463565009179040671425133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 975710006119360447616755 1463565009179040671425133)
                  ·
                    refine ⟨548836878442140251784425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1463565009179040671425133 548836878442140251784425)
                    ·
                      rfl

theorem cell22_1603284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_1603284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603284 prefixEnd_1603284 := by exact prefixLift 1603284
  have htrace : WordTrace (prefixWord ++ tailWord_1603284) baseStart_1603284 baseEnd_1603284 := by
    simpa [prefixWord, tailWord_1603284, baseEnd_1603284] using wordTrace_append hprefix tailTrace_1603284
  have hstable : (prefixWord ++ tailWord_1603284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603284).length < 2 ^ (prefixWord ++ tailWord_1603284).sum := by decide
  have hdescent : baseEnd_1603284 < baseStart_1603284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603310 : List Nat := [4, 1, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_1603310 : Nat := 118140960795 + 1603310 * 2 ^ 59
def prefixEnd_1603310 : Nat := 4983230072969 + 3 ^ 40 * 1603310 * 2
def baseEnd_1603310 : Nat := 548845778773484850634345

theorem tailTrace_1603310 : CollatzResearch.WordTrace tailWord_1603310 prefixEnd_1603310 548845778773484850634345 := by
  unfold tailWord_1603310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7309689977686146049112923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38985013214326112261935589 7309689977686146049112923)
  ·
    refine ⟨10964534966529219073669385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7309689977686146049112923 10964534966529219073669385)
    ·
      refine ⟨8223401224896914305252039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10964534966529219073669385 8223401224896914305252039)
      ·
        refine ⟨12335101837345371457878059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8223401224896914305252039 12335101837345371457878059)
        ·
          refine ⟨18502652756018057186817089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12335101837345371457878059 18502652756018057186817089)
          ·
            refine ⟨13876989567013542890112817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18502652756018057186817089 13876989567013542890112817)
            ·
              refine ⟨10407742175260157167584613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13876989567013542890112817 10407742175260157167584613)
              ·
                refine ⟨1951451657861279468922115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10407742175260157167584613 1951451657861279468922115)
                ·
                  refine ⟨2927177486791919203383173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1951451657861279468922115 2927177486791919203383173)
                  ·
                    refine ⟨548845778773484850634345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2927177486791919203383173 548845778773484850634345)
                    ·
                      rfl

theorem cell22_1603310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_1603310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603310 prefixEnd_1603310 := by exact prefixLift 1603310
  have htrace : WordTrace (prefixWord ++ tailWord_1603310) baseStart_1603310 baseEnd_1603310 := by
    simpa [prefixWord, tailWord_1603310, baseEnd_1603310] using wordTrace_append hprefix tailTrace_1603310
  have hstable : (prefixWord ++ tailWord_1603310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603310).length < 2 ^ (prefixWord ++ tailWord_1603310).sum := by decide
  have hdescent : baseEnd_1603310 < baseStart_1603310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603496 : List Nat := [2, 1, 6, 2, 1, 1, 1, 3, 1, 4]
def baseStart_1603496 : Nat := 118140960795 + 1603496 * 2 ^ 59
def prefixEnd_1603496 : Nat := 4983230072969 + 3 ^ 40 * 1603496 * 2
def baseEnd_1603496 : Nat := 548909450374642365483775

theorem tailTrace_1603496 : CollatzResearch.WordTrace tailWord_1603496 prefixEnd_1603496 548909450374642365483775 := by
  unfold tailWord_1603496
  simp only [CollatzResearch.WordTrace]
  refine ⟨29242151899407661079587171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38989535865876881439449561 29242151899407661079587171)
  ·
    refine ⟨43863227849111491619380757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29242151899407661079587171 43863227849111491619380757)
    ·
      refine ⟨2056088805427101169658473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43863227849111491619380757 2056088805427101169658473)
      ·
        refine ⟨1542066604070325877243855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2056088805427101169658473 1542066604070325877243855)
        ·
          refine ⟨2313099906105488815865783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1542066604070325877243855 2313099906105488815865783)
          ·
            refine ⟨3469649859158233223798675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2313099906105488815865783 3469649859158233223798675)
            ·
              refine ⟨5204474788737349835698013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3469649859158233223798675 5204474788737349835698013)
              ·
                refine ⟨1951678045776506188386755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5204474788737349835698013 1951678045776506188386755)
                ·
                  refine ⟨2927517068664759282580133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1951678045776506188386755 2927517068664759282580133)
                  ·
                    refine ⟨548909450374642365483775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2927517068664759282580133 548909450374642365483775)
                    ·
                      rfl

theorem cell22_1603496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_1603496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603496 prefixEnd_1603496 := by exact prefixLift 1603496
  have htrace : WordTrace (prefixWord ++ tailWord_1603496) baseStart_1603496 baseEnd_1603496 := by
    simpa [prefixWord, tailWord_1603496, baseEnd_1603496] using wordTrace_append hprefix tailTrace_1603496
  have hstable : (prefixWord ++ tailWord_1603496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603496).length < 2 ^ (prefixWord ++ tailWord_1603496).sum := by decide
  have hdescent : baseEnd_1603496 < baseStart_1603496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603505 : List Nat := [1, 2, 2, 4, 2, 2, 9]
def baseStart_1603505 : Nat := 118140960795 + 1603505 * 2 ^ 59
def prefixEnd_1603505 : Nat := 4983230072969 + 3 ^ 40 * 1603505 * 2
def baseEnd_1603505 : Nat := 20330093750317383037361

theorem tailTrace_1603505 : CollatzResearch.WordTrace tailWord_1603505 prefixEnd_1603505 20330093750317383037361 := by
  unfold tailWord_1603505
  simp only [CollatzResearch.WordTrace]
  refine ⟨58484632055782716696251969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38989754703855144464167979 58484632055782716696251969)
  ·
    refine ⟨43863474041837037522188977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58484632055782716696251969 43863474041837037522188977)
    ·
      refine ⟨32897605531377778141641733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43863474041837037522188977 32897605531377778141641733)
      ·
        refine ⟨6168301037133333401557825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32897605531377778141641733 6168301037133333401557825)
        ·
          refine ⟨4626225777850000051168369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6168301037133333401557825 4626225777850000051168369)
          ·
            refine ⟨3469669333387500038376277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4626225777850000051168369 3469669333387500038376277)
            ·
              refine ⟨20330093750317383037361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3469669333387500038376277 20330093750317383037361)
              ·
                rfl

theorem cell22_1603505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 9].length) (baseStart_1603505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603505 prefixEnd_1603505 := by exact prefixLift 1603505
  have htrace : WordTrace (prefixWord ++ tailWord_1603505) baseStart_1603505 baseEnd_1603505 := by
    simpa [prefixWord, tailWord_1603505, baseEnd_1603505] using wordTrace_append hprefix tailTrace_1603505
  have hstable : (prefixWord ++ tailWord_1603505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603505).length < 2 ^ (prefixWord ++ tailWord_1603505).sum := by decide
  have hdescent : baseEnd_1603505 < baseStart_1603505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603509 : List Nat := [1, 3, 3, 2, 1, 2, 3, 2, 2, 3]
def baseStart_1603509 : Nat := 118140960795 + 1603509 * 2 ^ 59
def prefixEnd_1603509 : Nat := 4983230072969 + 3 ^ 40 * 1603509 * 2
def baseEnd_1603509 : Nat := 548913900540314664908735

theorem tailTrace_1603509 : CollatzResearch.WordTrace tailWord_1603509 prefixEnd_1603509 548913900540314664908735 := by
  unfold tailWord_1603509
  simp only [CollatzResearch.WordTrace]
  refine ⟨58484777947768225379397581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38989851965178816919598387 58484777947768225379397581)
  ·
    refine ⟨21931791730413084517274093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58484777947768225379397581 21931791730413084517274093)
    ·
      refine ⟨8224421898904906693977785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21931791730413084517274093 8224421898904906693977785)
      ·
        refine ⟨6168316424178680020483339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8224421898904906693977785 6168316424178680020483339)
        ·
          refine ⟨9252474636268020030725009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6168316424178680020483339 9252474636268020030725009)
          ·
            refine ⟨6939355977201015023043757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9252474636268020030725009 6939355977201015023043757)
            ·
              refine ⟨2602258491450380633641409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6939355977201015023043757 2602258491450380633641409)
              ·
                refine ⟨1951693868587785475231057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2602258491450380633641409 1951693868587785475231057)
                ·
                  refine ⟨1463770401440839106423293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1951693868587785475231057 1463770401440839106423293)
                  ·
                    refine ⟨548913900540314664908735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1463770401440839106423293 548913900540314664908735)
                    ·
                      rfl

theorem cell22_1603509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_1603509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603509 prefixEnd_1603509 := by exact prefixLift 1603509
  have htrace : WordTrace (prefixWord ++ tailWord_1603509) baseStart_1603509 baseEnd_1603509 := by
    simpa [prefixWord, tailWord_1603509, baseEnd_1603509] using wordTrace_append hprefix tailTrace_1603509
  have hstable : (prefixWord ++ tailWord_1603509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603509).length < 2 ^ (prefixWord ++ tailWord_1603509).sum := by decide
  have hdescent : baseEnd_1603509 < baseStart_1603509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603595 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 8]
def baseStart_1603595 : Nat := 118140960795 + 1603595 * 2 ^ 59
def prefixEnd_1603595 : Nat := 4983230072969 + 3 ^ 40 * 1603595 * 2
def baseEnd_1603595 : Nat := 182981113365946369086157

theorem tailTrace_1603595 : CollatzResearch.WordTrace tailWord_1603595 prefixEnd_1603595 182981113365946369086157 := by
  unfold tailWord_1603595
  simp only [CollatzResearch.WordTrace]
  refine ⟨58487914625456662067028239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38991943083637774711352159 58487914625456662067028239)
  ·
    refine ⟨87731871938184993100542359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58487914625456662067028239 87731871938184993100542359)
    ·
      refine ⟨131597807907277489650813539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87731871938184993100542359 131597807907277489650813539)
      ·
        refine ⟨197396711860916234476220309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131597807907277489650813539 197396711860916234476220309)
        ·
          refine ⟨9252970868480448491072827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 197396711860916234476220309 9252970868480448491072827)
          ·
            refine ⟨13879456302720672736609241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9252970868480448491072827 13879456302720672736609241)
            ·
              refine ⟨10409592227040504552456931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13879456302720672736609241 10409592227040504552456931)
              ·
                refine ⟨15614388340560756828685397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10409592227040504552456931 15614388340560756828685397)
                ·
                  refine ⟨182981113365946369086157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15614388340560756828685397 182981113365946369086157)
                  ·
                    rfl

theorem cell22_1603595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 8].length) (baseStart_1603595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603595 prefixEnd_1603595 := by exact prefixLift 1603595
  have htrace : WordTrace (prefixWord ++ tailWord_1603595) baseStart_1603595 baseEnd_1603595 := by
    simpa [prefixWord, tailWord_1603595, baseEnd_1603595] using wordTrace_append hprefix tailTrace_1603595
  have hstable : (prefixWord ++ tailWord_1603595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603595).length < 2 ^ (prefixWord ++ tailWord_1603595).sum := by decide
  have hdescent : baseEnd_1603595 < baseStart_1603595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603644 : List Nat := [2, 2, 2, 2, 2, 1, 1, 5, 2, 3]
def baseStart_1603644 : Nat := 118140960795 + 1603644 * 2 ^ 59
def prefixEnd_1603644 : Nat := 4983230072969 + 3 ^ 40 * 1603644 * 2
def baseEnd_1603644 : Nat := 548960113799219312783321

theorem tailTrace_1603644 : CollatzResearch.WordTrace tailWord_1603644 prefixEnd_1603644 548960113799219312783321 := by
  unfold tailWord_1603644
  simp only [CollatzResearch.WordTrace]
  refine ⟨29244850901139571717780993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38993134534852762290374657 29244850901139571717780993)
  ·
    refine ⟨21933638175854678788335745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29244850901139571717780993 21933638175854678788335745)
    ·
      refine ⟨16450228631891009091251809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21933638175854678788335745 16450228631891009091251809)
      ·
        refine ⟨12337671473918256818438857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16450228631891009091251809 12337671473918256818438857)
        ·
          refine ⟨9253253605438692613829143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12337671473918256818438857 9253253605438692613829143)
          ·
            refine ⟨13879880408158038920743715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9253253605438692613829143 13879880408158038920743715)
            ·
              refine ⟨20819820612237058381115573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13879880408158038920743715 20819820612237058381115573)
              ·
                refine ⟨1951858182397224223229585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20819820612237058381115573 1951858182397224223229585)
                ·
                  refine ⟨1463893636797918167422189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1951858182397224223229585 1463893636797918167422189)
                  ·
                    refine ⟨548960113799219312783321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1463893636797918167422189 548960113799219312783321)
                    ·
                      rfl

theorem cell22_1603644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_1603644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603644 prefixEnd_1603644 := by exact prefixLift 1603644
  have htrace : WordTrace (prefixWord ++ tailWord_1603644) baseStart_1603644 baseEnd_1603644 := by
    simpa [prefixWord, tailWord_1603644, baseEnd_1603644] using wordTrace_append hprefix tailTrace_1603644
  have hstable : (prefixWord ++ tailWord_1603644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603644).length < 2 ^ (prefixWord ++ tailWord_1603644).sum := by decide
  have hdescent : baseEnd_1603644 < baseStart_1603644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603657 : List Nat := [1, 2, 1, 1, 2, 2, 7, 6]
def baseStart_1603657 : Nat := 118140960795 + 1603657 * 2 ^ 59
def prefixEnd_1603657 : Nat := 4983230072969 + 3 ^ 40 * 1603657 * 2
def baseEnd_1603657 : Nat := 60996062662765734689809

theorem tailTrace_1603657 : CollatzResearch.WordTrace tailWord_1603657 prefixEnd_1603657 60996062662765734689809 := by
  unfold tailWord_1603657
  simp only [CollatzResearch.WordTrace]
  refine ⟨58490175951232046655785225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38993450634154697770523483 58490175951232046655785225)
  ·
    refine ⟨43867631963424034991838919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58490175951232046655785225 43867631963424034991838919)
    ·
      refine ⟨65801447945136052487758379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43867631963424034991838919 65801447945136052487758379)
      ·
        refine ⟨98702171917704078731637569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65801447945136052487758379 98702171917704078731637569)
        ·
          refine ⟨74026628938278059048728177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98702171917704078731637569 74026628938278059048728177)
          ·
            refine ⟨55519971703708544286546133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74026628938278059048728177 55519971703708544286546133)
            ·
              refine ⟨1301249336805669006715925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 55519971703708544286546133 1301249336805669006715925)
              ·
                refine ⟨60996062662765734689809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1301249336805669006715925 60996062662765734689809)
                ·
                  rfl

theorem cell22_1603657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 6].length) (baseStart_1603657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603657 prefixEnd_1603657 := by exact prefixLift 1603657
  have htrace : WordTrace (prefixWord ++ tailWord_1603657) baseStart_1603657 baseEnd_1603657 := by
    simpa [prefixWord, tailWord_1603657, baseEnd_1603657] using wordTrace_append hprefix tailTrace_1603657
  have hstable : (prefixWord ++ tailWord_1603657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603657).length < 2 ^ (prefixWord ++ tailWord_1603657).sum := by decide
  have hdescent : baseEnd_1603657 < baseStart_1603657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603689 : List Nat := [1, 2, 1, 1, 1, 5, 4, 1, 3, 3]
def baseStart_1603689 : Nat := 118140960795 + 1603689 * 2 ^ 59
def prefixEnd_1603689 : Nat := 4983230072969 + 3 ^ 40 * 1603689 * 2
def baseEnd_1603689 : Nat := 548975518218854195408183

theorem tailTrace_1603689 : CollatzResearch.WordTrace tailWord_1603689 prefixEnd_1603689 548975518218854195408183 := by
  unfold tailWord_1603689
  simp only [CollatzResearch.WordTrace]
  refine ⟨58491343087116116120950121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38994228724744077413966747 58491343087116116120950121)
  ·
    refine ⟨43868507315337087090712591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58491343087116116120950121 43868507315337087090712591)
    ·
      refine ⟨65802760973005630636068887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43868507315337087090712591 65802760973005630636068887)
      ·
        refine ⟨98704141459508445954103331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65802760973005630636068887 98704141459508445954103331)
        ·
          refine ⟨148056212189262668931154997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98704141459508445954103331 148056212189262668931154997)
          ·
            refine ⟨13880269892743375212295781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148056212189262668931154997 13880269892743375212295781)
            ·
              refine ⟨2602550604889382852305459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13880269892743375212295781 2602550604889382852305459)
              ·
                refine ⟨3903825907334074278458189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2602550604889382852305459 3903825907334074278458189)
                ·
                  refine ⟨1463934715250277854421821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3903825907334074278458189 1463934715250277854421821)
                  ·
                    refine ⟨548975518218854195408183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1463934715250277854421821 548975518218854195408183)
                    ·
                      rfl

theorem cell22_1603689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 3, 3].length) (baseStart_1603689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603689 prefixEnd_1603689 := by exact prefixLift 1603689
  have htrace : WordTrace (prefixWord ++ tailWord_1603689) baseStart_1603689 baseEnd_1603689 := by
    simpa [prefixWord, tailWord_1603689, baseEnd_1603689] using wordTrace_append hprefix tailTrace_1603689
  have hstable : (prefixWord ++ tailWord_1603689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603689).length < 2 ^ (prefixWord ++ tailWord_1603689).sum := by decide
  have hdescent : baseEnd_1603689 < baseStart_1603689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603807 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 2, 7]
def baseStart_1603807 : Nat := 118140960795 + 1603807 * 2 ^ 59
def prefixEnd_1603807 : Nat := 4983230072969 + 3 ^ 40 * 1603807 * 2
def baseEnd_1603807 : Nat := 549015912030341220957821

theorem tailTrace_1603807 : CollatzResearch.WordTrace tailWord_1603807 prefixEnd_1603807 549015912030341220957821 := by
  unfold tailWord_1603807
  simp only [CollatzResearch.WordTrace]
  refine ⟨58495646900688622273745675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38997097933792414849163783 58495646900688622273745675)
  ·
    refine ⟨87743470351032933410618513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58495646900688622273745675 87743470351032933410618513)
    ·
      refine ⟨65807602763274700057963885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87743470351032933410618513 65807602763274700057963885)
      ·
        refine ⟨24677851036228012521736457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65807602763274700057963885 24677851036228012521736457)
        ·
          refine ⟨18508388277171009391302343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24677851036228012521736457 18508388277171009391302343)
          ·
            refine ⟨27762582415756514086953515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18508388277171009391302343 27762582415756514086953515)
            ·
              refine ⟨41643873623634771130430273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27762582415756514086953515 41643873623634771130430273)
              ·
                refine ⟨31232905217726078347822705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41643873623634771130430273 31232905217726078347822705)
                ·
                  refine ⟨23424678913294558760867029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31232905217726078347822705 23424678913294558760867029)
                  ·
                    refine ⟨549015912030341220957821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23424678913294558760867029 549015912030341220957821)
                    ·
                      rfl

theorem cell22_1603807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_1603807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603807 prefixEnd_1603807 := by exact prefixLift 1603807
  have htrace : WordTrace (prefixWord ++ tailWord_1603807) baseStart_1603807 baseEnd_1603807 := by
    simpa [prefixWord, tailWord_1603807, baseEnd_1603807] using wordTrace_append hprefix tailTrace_1603807
  have hstable : (prefixWord ++ tailWord_1603807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603807).length < 2 ^ (prefixWord ++ tailWord_1603807).sum := by decide
  have hdescent : baseEnd_1603807 < baseStart_1603807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603826 : List Nat := [3, 2, 1, 3, 2, 2, 3, 6]
def baseStart_1603826 : Nat := 118140960795 + 1603826 * 2 ^ 59
def prefixEnd_1603826 : Nat := 4983230072969 + 3 ^ 40 * 1603826 * 2
def baseEnd_1603826 : Nat := 61002490679847944970307

theorem tailTrace_1603826 : CollatzResearch.WordTrace tailWord_1603826 prefixEnd_1603826 61002490679847944970307 := by
  unfold tailWord_1603826
  simp only [CollatzResearch.WordTrace]
  refine ⟨14624084971904947129671833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38997559925079859012458221 14624084971904947129671833)
  ·
    refine ⟨10968063728928710347253875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14624084971904947129671833 10968063728928710347253875)
    ·
      refine ⟨16452095593393065520880813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10968063728928710347253875 16452095593393065520880813)
      ·
        refine ⟨6169535847522399570330305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16452095593393065520880813 6169535847522399570330305)
        ·
          refine ⟨4627151885641799677747729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6169535847522399570330305 4627151885641799677747729)
          ·
            refine ⟨3470363914231349758310797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4627151885641799677747729 3470363914231349758310797)
            ·
              refine ⟨1301386467836756159366549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3470363914231349758310797 1301386467836756159366549)
              ·
                refine ⟨61002490679847944970307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1301386467836756159366549 61002490679847944970307)
                ·
                  rfl

theorem cell22_1603826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 6].length) (baseStart_1603826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603826 prefixEnd_1603826 := by exact prefixLift 1603826
  have htrace : WordTrace (prefixWord ++ tailWord_1603826) baseStart_1603826 baseEnd_1603826 := by
    simpa [prefixWord, tailWord_1603826, baseEnd_1603826] using wordTrace_append hprefix tailTrace_1603826
  have hstable : (prefixWord ++ tailWord_1603826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603826).length < 2 ^ (prefixWord ++ tailWord_1603826).sum := by decide
  have hdescent : baseEnd_1603826 < baseStart_1603826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603847 : List Nat := [1, 1, 4, 5, 2, 1, 1, 2, 2, 3]
def baseStart_1603847 : Nat := 118140960795 + 1603847 * 2 ^ 59
def prefixEnd_1603847 : Nat := 4983230072969 + 3 ^ 40 * 1603847 * 2
def baseEnd_1603847 : Nat := 549029604847794449957699

theorem tailTrace_1603847 : CollatzResearch.WordTrace tailWord_1603847 prefixEnd_1603847 549029604847794449957699 := by
  unfold tailWord_1603847
  simp only [CollatzResearch.WordTrace]
  refine ⟨58497105820543709105201795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38998070547029139403467863 58497105820543709105201795)
  ·
    refine ⟨87745658730815563657802693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58497105820543709105201795 87745658730815563657802693)
    ·
      refine ⟨16452311012027918185838005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87745658730815563657802693 16452311012027918185838005)
      ·
        refine ⟨1542404157377617329922313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16452311012027918185838005 1542404157377617329922313)
        ·
          refine ⟨1156803118033212997441735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1542404157377617329922313 1156803118033212997441735)
          ·
            refine ⟨1735204677049819496162603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1156803118033212997441735 1735204677049819496162603)
            ·
              refine ⟨2602807015574729244243905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1735204677049819496162603 2602807015574729244243905)
              ·
                refine ⟨1952105261681046933182929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2602807015574729244243905 1952105261681046933182929)
                ·
                  refine ⟨1464078946260785199887197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1952105261681046933182929 1464078946260785199887197)
                  ·
                    refine ⟨549029604847794449957699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1464078946260785199887197 549029604847794449957699)
                    ·
                      rfl

theorem cell22_1603847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_1603847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603847 prefixEnd_1603847 := by exact prefixLift 1603847
  have htrace : WordTrace (prefixWord ++ tailWord_1603847) baseStart_1603847 baseEnd_1603847 := by
    simpa [prefixWord, tailWord_1603847, baseEnd_1603847] using wordTrace_append hprefix tailTrace_1603847
  have hstable : (prefixWord ++ tailWord_1603847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603847).length < 2 ^ (prefixWord ++ tailWord_1603847).sum := by decide
  have hdescent : baseEnd_1603847 < baseStart_1603847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603854 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 7]
def baseStart_1603854 : Nat := 118140960795 + 1603854 * 2 ^ 59
def prefixEnd_1603854 : Nat := 4983230072969 + 3 ^ 40 * 1603854 * 2
def baseEnd_1603854 : Nat := 183010667030282921677559

theorem tailTrace_1603854 : CollatzResearch.WordTrace tailWord_1603854 prefixEnd_1603854 183010667030282921677559 := by
  unfold tailWord_1603854
  simp only [CollatzResearch.WordTrace]
  refine ⟨7312170141439793662588327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38998240754345566200471077 7312170141439793662588327)
  ·
    refine ⟨10968255212159690493882491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7312170141439793662588327 10968255212159690493882491)
    ·
      refine ⟨16452382818239535740823737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10968255212159690493882491 16452382818239535740823737)
      ·
        refine ⟨12339287113679651805617803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16452382818239535740823737 12339287113679651805617803)
        ·
          refine ⟨18508930670519477708426705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12339287113679651805617803 18508930670519477708426705)
          ·
            refine ⟨13881698002889608281320029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18508930670519477708426705 13881698002889608281320029)
            ·
              refine ⟨5205636751083603105495011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13881698002889608281320029 5205636751083603105495011)
              ·
                refine ⟨7808455126625404658242517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5205636751083603105495011 7808455126625404658242517)
                ·
                  refine ⟨183010667030282921677559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7808455126625404658242517 183010667030282921677559)
                  ·
                    rfl

theorem cell22_1603854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_1603854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603854 prefixEnd_1603854 := by exact prefixLift 1603854
  have htrace : WordTrace (prefixWord ++ tailWord_1603854) baseStart_1603854 baseEnd_1603854 := by
    simpa [prefixWord, tailWord_1603854, baseEnd_1603854] using wordTrace_append hprefix tailTrace_1603854
  have hstable : (prefixWord ++ tailWord_1603854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603854).length < 2 ^ (prefixWord ++ tailWord_1603854).sum := by decide
  have hdescent : baseEnd_1603854 < baseStart_1603854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603884 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 3, 4]
def baseStart_1603884 : Nat := 118140960795 + 1603884 * 2 ^ 59
def prefixEnd_1603884 : Nat := 4983230072969 + 3 ^ 40 * 1603884 * 2
def baseEnd_1603884 : Nat := 549042270703938686782585

theorem tailTrace_1603884 : CollatzResearch.WordTrace tailWord_1603884 prefixEnd_1603884 549042270703938686782585 := by
  unfold tailWord_1603884
  simp only [CollatzResearch.WordTrace]
  refine ⟨29249227660704832212149353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38998970214273109616199137 29249227660704832212149353)
  ·
    refine ⟨21936920745528624159112015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29249227660704832212149353 21936920745528624159112015)
    ·
      refine ⟨32905381118292936238668023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21936920745528624159112015 32905381118292936238668023)
      ·
        refine ⟨49358071677439404358002035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32905381118292936238668023 49358071677439404358002035)
        ·
          refine ⟨74037107516159106537003053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49358071677439404358002035 74037107516159106537003053)
          ·
            refine ⟨27763915318559664951376145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74037107516159106537003053 27763915318559664951376145)
            ·
              refine ⟨20822936488919748713532109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27763915318559664951376145 20822936488919748713532109)
              ·
                refine ⟨7808601183344905767574541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20822936488919748713532109 7808601183344905767574541)
                ·
                  refine ⟨2928225443754339662840453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7808601183344905767574541 2928225443754339662840453)
                  ·
                    refine ⟨549042270703938686782585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2928225443754339662840453 549042270703938686782585)
                    ·
                      rfl

theorem cell22_1603884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_1603884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603884 prefixEnd_1603884 := by exact prefixLift 1603884
  have htrace : WordTrace (prefixWord ++ tailWord_1603884) baseStart_1603884 baseEnd_1603884 := by
    simpa [prefixWord, tailWord_1603884, baseEnd_1603884] using wordTrace_append hprefix tailTrace_1603884
  have hstable : (prefixWord ++ tailWord_1603884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603884).length < 2 ^ (prefixWord ++ tailWord_1603884).sum := by decide
  have hdescent : baseEnd_1603884 < baseStart_1603884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603892 : List Nat := [2, 5, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_1603892 : Nat := 118140960795 + 1603892 * 2 ^ 59
def prefixEnd_1603892 : Nat := 4983230072969 + 3 ^ 40 * 1603892 * 2
def baseEnd_1603892 : Nat := 549045009267429332582561

theorem tailTrace_1603892 : CollatzResearch.WordTrace tailWord_1603892 prefixEnd_1603892 549045009267429332582561 := by
  unfold tailWord_1603892
  simp only [CollatzResearch.WordTrace]
  refine ⟨29249373552690340895294965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38999164736920454527059953 29249373552690340895294965)
  ·
    refine ⟨2742128770564719458933903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29249373552690340895294965 2742128770564719458933903)
    ·
      refine ⟨4113193155847079188400855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2742128770564719458933903 4113193155847079188400855)
      ·
        refine ⟨6169789733770618782601283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4113193155847079188400855 6169789733770618782601283)
        ·
          refine ⟨9254684600655928173901925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6169789733770618782601283 9254684600655928173901925)
          ·
            refine ⟨1735253362622986532606611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9254684600655928173901925 1735253362622986532606611)
            ·
              refine ⟨2602880043934479798909917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1735253362622986532606611 2602880043934479798909917)
              ·
                refine ⟨976080016475429924591219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2602880043934479798909917 976080016475429924591219)
                ·
                  refine ⟨1464120024713144886886829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 976080016475429924591219 1464120024713144886886829)
                  ·
                    refine ⟨549045009267429332582561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1464120024713144886886829 549045009267429332582561)
                    ·
                      rfl

theorem cell22_1603892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_1603892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603892 prefixEnd_1603892 := by exact prefixLift 1603892
  have htrace : WordTrace (prefixWord ++ tailWord_1603892) baseStart_1603892 baseEnd_1603892 := by
    simpa [prefixWord, tailWord_1603892, baseEnd_1603892] using wordTrace_append hprefix tailTrace_1603892
  have hstable : (prefixWord ++ tailWord_1603892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603892).length < 2 ^ (prefixWord ++ tailWord_1603892).sum := by decide
  have hdescent : baseEnd_1603892 < baseStart_1603892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603929 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 6, 4]
def baseStart_1603929 : Nat := 118140960795 + 1603929 * 2 ^ 59
def prefixEnd_1603929 : Nat := 4983230072969 + 3 ^ 40 * 1603929 * 2
def baseEnd_1603929 : Nat := 549057675123573569407447

theorem tailTrace_1603929 : CollatzResearch.WordTrace tailWord_1603929 prefixEnd_1603929 549057675123573569407447 := by
  unfold tailWord_1603929
  simp only [CollatzResearch.WordTrace]
  refine ⟨58500096606246637109686841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39000064404164424739791227 58500096606246637109686841)
  ·
    refine ⟨43875072454684977832265131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58500096606246637109686841 43875072454684977832265131)
    ·
      refine ⟨65812608682027466748397697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43875072454684977832265131 65812608682027466748397697)
      ·
        refine ⟨49359456511520600061298273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65812608682027466748397697 49359456511520600061298273)
        ·
          refine ⟨37019592383640450045973705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49359456511520600061298273 37019592383640450045973705)
          ·
            refine ⟨27764694287730337534480279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37019592383640450045973705 27764694287730337534480279)
            ·
              refine ⟨41647041431595506301720419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27764694287730337534480279 41647041431595506301720419)
              ·
                refine ⟨62470562147393259452580629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41647041431595506301720419 62470562147393259452580629)
                ·
                  refine ⟨2928307600659059036839717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62470562147393259452580629 2928307600659059036839717)
                  ·
                    refine ⟨549057675123573569407447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2928307600659059036839717 549057675123573569407447)
                    ·
                      rfl

theorem cell22_1603929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_1603929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603929 prefixEnd_1603929 := by exact prefixLift 1603929
  have htrace : WordTrace (prefixWord ++ tailWord_1603929) baseStart_1603929 baseEnd_1603929 := by
    simpa [prefixWord, tailWord_1603929, baseEnd_1603929] using wordTrace_append hprefix tailTrace_1603929
  have hstable : (prefixWord ++ tailWord_1603929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603929).length < 2 ^ (prefixWord ++ tailWord_1603929).sum := by decide
  have hdescent : baseEnd_1603929 < baseStart_1603929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1603989 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 9]
def baseStart_1603989 : Nat := 118140960795 + 1603989 * 2 ^ 59
def prefixEnd_1603989 : Nat := 4983230072969 + 3 ^ 40 * 1603989 * 2
def baseEnd_1603989 : Nat := 183026071449917804302421

theorem tailTrace_1603989 : CollatzResearch.WordTrace tailWord_1603989 prefixEnd_1603989 183026071449917804302421 := by
  unfold tailWord_1603989
  simp only [CollatzResearch.WordTrace]
  refine ⟨58502284986029267356871021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39001523324019511571247347 58502284986029267356871021)
  ·
    refine ⟨21938356869760975258826633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58502284986029267356871021 21938356869760975258826633)
    ·
      refine ⟨16453767652320731444119975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21938356869760975258826633 16453767652320731444119975)
      ·
        refine ⟨24680651478481097166179963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16453767652320731444119975 24680651478481097166179963)
        ·
          refine ⟨37020977217721645749269945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24680651478481097166179963 37020977217721645749269945)
          ·
            refine ⟨27765732913291234311952459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37020977217721645749269945 27765732913291234311952459)
            ·
              refine ⟨41648599369936851467928689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27765732913291234311952459 41648599369936851467928689)
              ·
                refine ⟨31236449527452638600946517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41648599369936851467928689 31236449527452638600946517)
                ·
                  refine ⟨183026071449917804302421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31236449527452638600946517 183026071449917804302421)
                  ·
                    rfl

theorem cell22_1603989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_1603989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1603989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1603989 prefixEnd_1603989 := by exact prefixLift 1603989
  have htrace : WordTrace (prefixWord ++ tailWord_1603989) baseStart_1603989 baseEnd_1603989 := by
    simpa [prefixWord, tailWord_1603989, baseEnd_1603989] using wordTrace_append hprefix tailTrace_1603989
  have hstable : (prefixWord ++ tailWord_1603989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1603989).length < 2 ^ (prefixWord ++ tailWord_1603989).sum := by decide
  have hdescent : baseEnd_1603989 < baseStart_1603989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1603989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604023 : List Nat := [1, 1, 3, 1, 3, 5, 1, 2, 5]
def baseStart_1604023 : Nat := 118140960795 + 1604023 * 2 ^ 59
def prefixEnd_1604023 : Nat := 4983230072969 + 3 ^ 40 * 1604023 * 2
def baseEnd_1604023 : Nat := 183029951081529552519053

theorem tailTrace_1604023 : CollatzResearch.WordTrace tailWord_1604023 prefixEnd_1604023 183029951081529552519053 := by
  unfold tailWord_1604023
  simp only [CollatzResearch.WordTrace]
  refine ⟨58503525067906091163608723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39002350045270727442405815 58503525067906091163608723)
  ·
    refine ⟨87755287601859136745413085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58503525067906091163608723 87755287601859136745413085)
    ·
      refine ⟨32908232850697176279529907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87755287601859136745413085 32908232850697176279529907)
      ·
        refine ⟨49362349276045764419294861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32908232850697176279529907 49362349276045764419294861)
        ·
          refine ⟨18510880978517161657235573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49362349276045764419294861 18510880978517161657235573)
          ·
            refine ⟨1735395091735983905365835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18510880978517161657235573 1735395091735983905365835)
            ·
              refine ⟨2603092637603975858048753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1735395091735983905365835 2603092637603975858048753)
              ·
                refine ⟨1952319478202981893536565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2603092637603975858048753 1952319478202981893536565)
                ·
                  refine ⟨183029951081529552519053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1952319478202981893536565 183029951081529552519053)
                  ·
                    rfl

theorem cell22_1604023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 5].length) (baseStart_1604023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604023 prefixEnd_1604023 := by exact prefixLift 1604023
  have htrace : WordTrace (prefixWord ++ tailWord_1604023) baseStart_1604023 baseEnd_1604023 := by
    simpa [prefixWord, tailWord_1604023, baseEnd_1604023] using wordTrace_append hprefix tailTrace_1604023
  have hstable : (prefixWord ++ tailWord_1604023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604023).length < 2 ^ (prefixWord ++ tailWord_1604023).sum := by decide
  have hdescent : baseEnd_1604023 < baseStart_1604023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604053 : List Nat := [1, 3, 2, 3, 1, 2, 1, 4, 1, 4]
def baseStart_1604053 : Nat := 118140960795 + 1604053 * 2 ^ 59
def prefixEnd_1604053 : Nat := 4983230072969 + 3 ^ 40 * 1604053 * 2
def baseEnd_1604053 : Nat := 549100122857678579307067

theorem tailTrace_1604053 : CollatzResearch.WordTrace tailWord_1604053 prefixEnd_1604053 549100122857678579307067 := by
  unfold tailWord_1604053
  simp only [CollatzResearch.WordTrace]
  refine ⟨58504619257797406287200813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39003079505198270858133875 58504619257797406287200813)
  ·
    refine ⟨21939232221674027357700305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58504619257797406287200813 21939232221674027357700305)
    ·
      refine ⟨16454424166255520518275229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21939232221674027357700305 16454424166255520518275229)
      ·
        refine ⟨6170409062345820194353211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16454424166255520518275229 6170409062345820194353211)
        ·
          refine ⟨9255613593518730291529817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6170409062345820194353211 9255613593518730291529817)
          ·
            refine ⟨6941710195139047718647363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9255613593518730291529817 6941710195139047718647363)
            ·
              refine ⟨10412565292708571577971045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6941710195139047718647363 10412565292708571577971045)
              ·
                refine ⟨1952355992382857170869571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10412565292708571577971045 1952355992382857170869571)
                ·
                  refine ⟨2928533988574285756304357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1952355992382857170869571 2928533988574285756304357)
                  ·
                    refine ⟨549100122857678579307067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2928533988574285756304357 549100122857678579307067)
                    ·
                      rfl

theorem cell22_1604053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_1604053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604053 prefixEnd_1604053 := by exact prefixLift 1604053
  have htrace : WordTrace (prefixWord ++ tailWord_1604053) baseStart_1604053 baseEnd_1604053 := by
    simpa [prefixWord, tailWord_1604053, baseEnd_1604053] using wordTrace_append hprefix tailTrace_1604053
  have hstable : (prefixWord ++ tailWord_1604053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604053).length < 2 ^ (prefixWord ++ tailWord_1604053).sum := by decide
  have hdescent : baseEnd_1604053 < baseStart_1604053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604083 : List Nat := [1, 1, 1, 2, 2, 2, 4, 4, 2, 3]
def baseStart_1604083 : Nat := 118140960795 + 1604083 * 2 ^ 59
def prefixEnd_1604083 : Nat := 4983230072969 + 3 ^ 40 * 1604083 * 2
def baseEnd_1604083 : Nat := 549110392470768501056975

theorem tailTrace_1604083 : CollatzResearch.WordTrace tailWord_1604083 prefixEnd_1604083 549110392470768501056975 := by
  unfold tailWord_1604083
  simp only [CollatzResearch.WordTrace]
  refine ⟨58505713447688721410792903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39003808965125814273861935 58505713447688721410792903)
  ·
    refine ⟨87758570171533082116189355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58505713447688721410792903 87758570171533082116189355)
    ·
      refine ⟨131637855257299623174284033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87758570171533082116189355 131637855257299623174284033)
      ·
        refine ⟨98728391442974717380713025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131637855257299623174284033 98728391442974717380713025)
        ·
          refine ⟨74046293582231038035534769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98728391442974717380713025 74046293582231038035534769)
          ·
            refine ⟨55534720186673278526651077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74046293582231038035534769 55534720186673278526651077)
            ·
              refine ⟨10412760035001239723747077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55534720186673278526651077 10412760035001239723747077)
              ·
                refine ⟨1952392506562732448202577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10412760035001239723747077 1952392506562732448202577)
                ·
                  refine ⟨1464294379922049336151933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1952392506562732448202577 1464294379922049336151933)
                  ·
                    refine ⟨549110392470768501056975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1464294379922049336151933 549110392470768501056975)
                    ·
                      rfl

theorem cell22_1604083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 4, 2, 3].length) (baseStart_1604083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604083 prefixEnd_1604083 := by exact prefixLift 1604083
  have htrace : WordTrace (prefixWord ++ tailWord_1604083) baseStart_1604083 baseEnd_1604083 := by
    simpa [prefixWord, tailWord_1604083, baseEnd_1604083] using wordTrace_append hprefix tailTrace_1604083
  have hstable : (prefixWord ++ tailWord_1604083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604083).length < 2 ^ (prefixWord ++ tailWord_1604083).sum := by decide
  have hdescent : baseEnd_1604083 < baseStart_1604083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604164 : List Nat := [2, 3, 5, 1, 1, 1, 3, 6]
def baseStart_1604164 : Nat := 118140960795 + 1604164 * 2 ^ 59
def prefixEnd_1604164 : Nat := 4983230072969 + 3 ^ 40 * 1604164 * 2
def baseEnd_1604164 : Nat := 61015346714012365531303

theorem tailTrace_1604164 : CollatzResearch.WordTrace tailWord_1604164 prefixEnd_1604164 61015346714012365531303 := by
  unfold tailWord_1604164
  simp only [CollatzResearch.WordTrace]
  refine ⟨29254333880197636122245773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39005778506930181496327697 29254333880197636122245773)
  ·
    refine ⟨10970375205074113545842165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29254333880197636122245773 10970375205074113545842165)
    ·
      refine ⟨1028472675475698144922703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10970375205074113545842165 1028472675475698144922703)
      ·
        refine ⟨1542709013213547217384055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1028472675475698144922703 1542709013213547217384055)
        ·
          refine ⟨2314063519820320826076083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1542709013213547217384055 2314063519820320826076083)
          ·
            refine ⟨3471095279730481239114125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2314063519820320826076083 3471095279730481239114125)
            ·
              refine ⟨1301660729898930464667797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3471095279730481239114125 1301660729898930464667797)
              ·
                refine ⟨61015346714012365531303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1301660729898930464667797 61015346714012365531303)
                ·
                  rfl

theorem cell22_1604164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 6].length) (baseStart_1604164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604164 prefixEnd_1604164 := by exact prefixLift 1604164
  have htrace : WordTrace (prefixWord ++ tailWord_1604164) baseStart_1604164 baseEnd_1604164 := by
    simpa [prefixWord, tailWord_1604164, baseEnd_1604164] using wordTrace_append hprefix tailTrace_1604164
  have hstable : (prefixWord ++ tailWord_1604164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604164).length < 2 ^ (prefixWord ++ tailWord_1604164).sum := by decide
  have hdescent : baseEnd_1604164 < baseStart_1604164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604233 : List Nat := [1, 2, 1, 1, 4, 1, 1, 5, 2, 4]
def baseStart_1604233 : Nat := 118140960795 + 1604233 * 2 ^ 59
def prefixEnd_1604233 : Nat := 4983230072969 + 3 ^ 40 * 1604233 * 2
def baseEnd_1604233 : Nat := 549161740536218109806515

theorem tailTrace_1604233 : CollatzResearch.WordTrace tailWord_1604233 prefixEnd_1604233 549161740536218109806515 := by
  unfold tailWord_1604233
  simp only [CollatzResearch.WordTrace]
  refine ⟨58511184397145297028753353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39007456264763531352502235 58511184397145297028753353)
  ·
    refine ⟨43883388297858972771565015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58511184397145297028753353 43883388297858972771565015)
    ·
      refine ⟨65825082446788459157347523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43883388297858972771565015 65825082446788459157347523)
      ·
        refine ⟨98737623670182688736021285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65825082446788459157347523 98737623670182688736021285)
        ·
          refine ⟨18513304438159254138003991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98737623670182688736021285 18513304438159254138003991)
          ·
            refine ⟨27769956657238881207005987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18513304438159254138003991 27769956657238881207005987)
            ·
              refine ⟨41654934985858321810508981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27769956657238881207005987 41654934985858321810508981)
              ·
                refine ⟨3905150154924217669735217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41654934985858321810508981 3905150154924217669735217)
                ·
                  refine ⟨2928862616193163252301413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3905150154924217669735217 2928862616193163252301413)
                  ·
                    refine ⟨549161740536218109806515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2928862616193163252301413 549161740536218109806515)
                    ·
                      rfl

theorem cell22_1604233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 4].length) (baseStart_1604233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604233 prefixEnd_1604233 := by exact prefixLift 1604233
  have htrace : WordTrace (prefixWord ++ tailWord_1604233) baseStart_1604233 baseEnd_1604233 := by
    simpa [prefixWord, tailWord_1604233, baseEnd_1604233] using wordTrace_append hprefix tailTrace_1604233
  have hstable : (prefixWord ++ tailWord_1604233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604233).length < 2 ^ (prefixWord ++ tailWord_1604233).sum := by decide
  have hdescent : baseEnd_1604233 < baseStart_1604233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604254 : List Nat := [4, 3, 1, 1, 1, 1, 5, 2, 4]
def baseStart_1604254 : Nat := 118140960795 + 1604254 * 2 ^ 59
def prefixEnd_1604254 : Nat := 4983230072969 + 3 ^ 40 * 1604254 * 2
def baseEnd_1604254 : Nat := 183056309755127018343817

theorem tailTrace_1604254 : CollatzResearch.WordTrace tailWord_1604254 prefixEnd_1604254 183056309755127018343817 := by
  unfold tailWord_1604254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7313993791258652201908477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39007966886712811743511877 7313993791258652201908477)
  ·
    refine ⟨2742747671721994575715679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7313993791258652201908477 2742747671721994575715679)
    ·
      refine ⟨4114121507582991863573519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2742747671721994575715679 4114121507582991863573519)
      ·
        refine ⟨6171182261374487795360279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4114121507582991863573519 6171182261374487795360279)
        ·
          refine ⟨9256773392061731693040419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6171182261374487795360279 9256773392061731693040419)
          ·
            refine ⟨13885160088092597539560629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9256773392061731693040419 13885160088092597539560629)
            ·
              refine ⟨1301733758258681019333809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13885160088092597539560629 1301733758258681019333809)
              ·
                refine ⟨976300318694010764500357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1301733758258681019333809 976300318694010764500357)
                ·
                  refine ⟨183056309755127018343817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 976300318694010764500357 183056309755127018343817)
                  ·
                    rfl

theorem cell22_1604254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_1604254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604254 prefixEnd_1604254 := by exact prefixLift 1604254
  have htrace : WordTrace (prefixWord ++ tailWord_1604254) baseStart_1604254 baseEnd_1604254 := by
    simpa [prefixWord, tailWord_1604254, baseEnd_1604254] using wordTrace_append hprefix tailTrace_1604254
  have hstable : (prefixWord ++ tailWord_1604254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604254).length < 2 ^ (prefixWord ++ tailWord_1604254).sum := by decide
  have hdescent : baseEnd_1604254 < baseStart_1604254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604269 : List Nat := [1, 5, 2, 1, 1, 2, 4, 1, 2, 3]
def baseStart_1604269 : Nat := 118140960795 + 1604269 * 2 ^ 59
def prefixEnd_1604269 : Nat := 4983230072969 + 3 ^ 40 * 1604269 * 2
def baseEnd_1604269 : Nat := 549174064071926015906405

theorem tailTrace_1604269 : CollatzResearch.WordTrace tailWord_1604269 prefixEnd_1604269 549174064071926015906405 := by
  unfold tailWord_1604269
  simp only [CollatzResearch.WordTrace]
  refine ⟨58512497425014875177063861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39008331616676583451375907 58512497425014875177063861)
  ·
    refine ⟨5485546633595144547849737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58512497425014875177063861 5485546633595144547849737)
    ·
      refine ⟨4114159975196358410887303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5485546633595144547849737 4114159975196358410887303)
      ·
        refine ⟨6171239962794537616330955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4114159975196358410887303 6171239962794537616330955)
        ·
          refine ⟨9256859944191806424496433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6171239962794537616330955 9256859944191806424496433)
          ·
            refine ⟨6942644958143854818372325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9256859944191806424496433 6942644958143854818372325)
            ·
              refine ⟨1301745929651972778444811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6942644958143854818372325 1301745929651972778444811)
              ·
                refine ⟨1952618894477959167667217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1301745929651972778444811 1952618894477959167667217)
                ·
                  refine ⟨1464464170858469375750413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1952618894477959167667217 1464464170858469375750413)
                  ·
                    refine ⟨549174064071926015906405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1464464170858469375750413 549174064071926015906405)
                    ·
                      rfl

theorem cell22_1604269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_1604269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604269 prefixEnd_1604269 := by exact prefixLift 1604269
  have htrace : WordTrace (prefixWord ++ tailWord_1604269) baseStart_1604269 baseEnd_1604269 := by
    simpa [prefixWord, tailWord_1604269, baseEnd_1604269] using wordTrace_append hprefix tailTrace_1604269
  have hstable : (prefixWord ++ tailWord_1604269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604269).length < 2 ^ (prefixWord ++ tailWord_1604269).sum := by decide
  have hdescent : baseEnd_1604269 < baseStart_1604269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604325 : List Nat := [1, 3, 1, 4, 1, 3, 1, 1, 2, 5]
def baseStart_1604325 : Nat := 118140960795 + 1604325 * 2 ^ 59
def prefixEnd_1604325 : Nat := 4983230072969 + 3 ^ 40 * 1604325 * 2
def baseEnd_1604325 : Nat := 549193234016360536506233

theorem tailTrace_1604325 : CollatzResearch.WordTrace tailWord_1604325 prefixEnd_1604325 549193234016360536506233 := by
  unfold tailWord_1604325
  simp only [CollatzResearch.WordTrace]
  refine ⟨58514539912811996741102429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39009693275207997827401619 58514539912811996741102429)
  ·
    refine ⟨21942952467304498777913411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58514539912811996741102429 21942952467304498777913411)
    ·
      refine ⟨32914428700956748166870117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21942952467304498777913411 32914428700956748166870117)
      ·
        refine ⟨6171455381429390281288147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32914428700956748166870117 6171455381429390281288147)
        ·
          refine ⟨9257183072144085421932221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6171455381429390281288147 9257183072144085421932221)
          ·
            refine ⟨3471443652054032033224583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9257183072144085421932221 3471443652054032033224583)
            ·
              refine ⟨5207165478081048049836875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3471443652054032033224583 5207165478081048049836875)
              ·
                refine ⟨7810748217121572074755313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5207165478081048049836875 7810748217121572074755313)
                ·
                  refine ⟨5858061162841179056066485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7810748217121572074755313 5858061162841179056066485)
                  ·
                    refine ⟨549193234016360536506233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5858061162841179056066485 549193234016360536506233)
                    ·
                      rfl

theorem cell22_1604325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_1604325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604325 prefixEnd_1604325 := by exact prefixLift 1604325
  have htrace : WordTrace (prefixWord ++ tailWord_1604325) baseStart_1604325 baseEnd_1604325 := by
    simpa [prefixWord, tailWord_1604325, baseEnd_1604325] using wordTrace_append hprefix tailTrace_1604325
  have hstable : (prefixWord ++ tailWord_1604325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604325).length < 2 ^ (prefixWord ++ tailWord_1604325).sum := by decide
  have hdescent : baseEnd_1604325 < baseStart_1604325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604432 : List Nat := [2, 1, 1, 1, 1, 4, 5, 1, 3, 3]
def baseStart_1604432 : Nat := 118140960795 + 1604432 * 2 ^ 59
def prefixEnd_1604432 : Nat := 4983230072969 + 3 ^ 40 * 1604432 * 2
def baseEnd_1604432 : Nat := 549229862303047924080905

theorem tailTrace_1604432 : CollatzResearch.WordTrace tailWord_1604432 prefixEnd_1604432 549229862303047924080905 := by
  unfold tailWord_1604432
  simp only [CollatzResearch.WordTrace]
  refine ⟨29259221261712177007623775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39012295015616236010165033 29259221261712177007623775)
  ·
    refine ⟨43888831892568265511435663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29259221261712177007623775 43888831892568265511435663)
    ·
      refine ⟨65833247838852398267153495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43888831892568265511435663 65833247838852398267153495)
      ·
        refine ⟨98749871758278597400730243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65833247838852398267153495 98749871758278597400730243)
        ·
          refine ⟨148124807637417896101095365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98749871758278597400730243 148124807637417896101095365)
          ·
            refine ⟨27773401432015855518955381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148124807637417896101095365 27773401432015855518955381)
            ·
              refine ⟨2603756384251486454902067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27773401432015855518955381 2603756384251486454902067)
              ·
                refine ⟨3905634576377229682353101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2603756384251486454902067 3905634576377229682353101)
                ·
                  refine ⟨1464612966141461130882413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3905634576377229682353101 1464612966141461130882413)
                  ·
                    refine ⟨549229862303047924080905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1464612966141461130882413 549229862303047924080905)
                    ·
                      rfl

theorem cell22_1604432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 3, 3].length) (baseStart_1604432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604432 prefixEnd_1604432 := by exact prefixLift 1604432
  have htrace : WordTrace (prefixWord ++ tailWord_1604432) baseStart_1604432 baseEnd_1604432 := by
    simpa [prefixWord, tailWord_1604432, baseEnd_1604432] using wordTrace_append hprefix tailTrace_1604432
  have hstable : (prefixWord ++ tailWord_1604432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604432).length < 2 ^ (prefixWord ++ tailWord_1604432).sum := by decide
  have hdescent : baseEnd_1604432 < baseStart_1604432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604556 : List Nat := [2, 2, 1, 4, 1, 1, 5, 1, 2, 3]
def baseStart_1604556 : Nat := 118140960795 + 1604556 * 2 ^ 59
def prefixEnd_1604556 : Nat := 4983230072969 + 3 ^ 40 * 1604556 * 2
def baseEnd_1604556 : Nat := 549272310037152933980525

theorem tailTrace_1604556 : CollatzResearch.WordTrace tailWord_1604556 prefixEnd_1604556 549272310037152933980525 := by
  unfold tailWord_1604556
  simp only [CollatzResearch.WordTrace]
  refine ⟨29261482587487561596380761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39015310116650082128507681 29261482587487561596380761)
  ·
    refine ⟨21946111940615671197285571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29261482587487561596380761 21946111940615671197285571)
    ·
      refine ⟨32919167910923506795928357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21946111940615671197285571 32919167910923506795928357)
      ·
        refine ⟨6172343983298157524236567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32919167910923506795928357 6172343983298157524236567)
        ·
          refine ⟨9258515974947236286354851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6172343983298157524236567 9258515974947236286354851)
          ·
            refine ⟨13887773962420854429532277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9258515974947236286354851 13887773962420854429532277)
            ·
              refine ⟨1301978808976955102768651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13887773962420854429532277 1301978808976955102768651)
              ·
                refine ⟨1952968213465432654152977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1301978808976955102768651 1952968213465432654152977)
                ·
                  refine ⟨1464726160099074490614733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1952968213465432654152977 1464726160099074490614733)
                  ·
                    refine ⟨549272310037152933980525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1464726160099074490614733 549272310037152933980525)
                    ·
                      rfl

theorem cell22_1604556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 2, 3].length) (baseStart_1604556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604556 prefixEnd_1604556 := by exact prefixLift 1604556
  have htrace : WordTrace (prefixWord ++ tailWord_1604556) baseStart_1604556 baseEnd_1604556 := by
    simpa [prefixWord, tailWord_1604556, baseEnd_1604556] using wordTrace_append hprefix tailTrace_1604556
  have hstable : (prefixWord ++ tailWord_1604556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604556).length < 2 ^ (prefixWord ++ tailWord_1604556).sum := by decide
  have hdescent : baseEnd_1604556 < baseStart_1604556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604567 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 5, 3]
def baseStart_1604567 : Nat := 118140960795 + 1604567 * 2 ^ 59
def prefixEnd_1604567 : Nat := 4983230072969 + 3 ^ 40 * 1604567 * 2
def baseEnd_1604567 : Nat := 549276075561952571955491

theorem tailTrace_1604567 : CollatzResearch.WordTrace tailWord_1604567 prefixEnd_1604567 549276075561952571955491 := by
  unfold tailWord_1604567
  simp only [CollatzResearch.WordTrace]
  refine ⟨58523366377935272071411955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39015577585290181380941303 58523366377935272071411955)
  ·
    refine ⟨87785049566902908107117933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58523366377935272071411955 87785049566902908107117933)
    ·
      refine ⟨32919393587588590540169225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87785049566902908107117933 32919393587588590540169225)
      ·
        refine ⟨24689545190691442905126919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32919393587588590540169225 24689545190691442905126919)
        ·
          refine ⟨37034317786037164357690379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24689545190691442905126919 37034317786037164357690379)
          ·
            refine ⟨55551476679055746536535569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37034317786037164357690379 55551476679055746536535569)
            ·
              refine ⟨41663607509291809902401677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55551476679055746536535569 41663607509291809902401677)
              ·
                refine ⟨15623852815984428713400629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41663607509291809902401677 15623852815984428713400629)
                ·
                  refine ⟨1464736201498540191881309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15623852815984428713400629 1464736201498540191881309)
                  ·
                    refine ⟨549276075561952571955491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1464736201498540191881309 549276075561952571955491)
                    ·
                      rfl

theorem cell22_1604567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_1604567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604567 prefixEnd_1604567 := by exact prefixLift 1604567
  have htrace : WordTrace (prefixWord ++ tailWord_1604567) baseStart_1604567 baseEnd_1604567 := by
    simpa [prefixWord, tailWord_1604567, baseEnd_1604567] using wordTrace_append hprefix tailTrace_1604567
  have hstable : (prefixWord ++ tailWord_1604567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604567).length < 2 ^ (prefixWord ++ tailWord_1604567).sum := by decide
  have hdescent : baseEnd_1604567 < baseStart_1604567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604569 : List Nat := [1, 2, 1, 2, 5, 3, 2, 6]
def baseStart_1604569 : Nat := 118140960795 + 1604569 * 2 ^ 59
def prefixEnd_1604569 : Nat := 4983230072969 + 3 ^ 40 * 1604569 * 2
def baseEnd_1604569 : Nat := 61030751133647248156165

theorem tailTrace_1604569 : CollatzResearch.WordTrace tailWord_1604569 prefixEnd_1604569 61030751133647248156165 := by
  unfold tailWord_1604569
  simp only [CollatzResearch.WordTrace]
  refine ⟨58523439323928026412984761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39015626215952017608656507 58523439323928026412984761)
  ·
    refine ⟨43892579492946019809738571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58523439323928026412984761 43892579492946019809738571)
    ·
      refine ⟨65838869239419029714607857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43892579492946019809738571 65838869239419029714607857)
      ·
        refine ⟨49379151929564272285955893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65838869239419029714607857 49379151929564272285955893)
        ·
          refine ⟨4629295493396650526808365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49379151929564272285955893 4629295493396650526808365)
          ·
            refine ⟨1735985810023743947553137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4629295493396650526808365 1735985810023743947553137)
            ·
              refine ⟨1301989357517807960664853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1735985810023743947553137 1301989357517807960664853)
              ·
                refine ⟨61030751133647248156165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1301989357517807960664853 61030751133647248156165)
                ·
                  rfl

theorem cell22_1604569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 6].length) (baseStart_1604569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604569 prefixEnd_1604569 := by exact prefixLift 1604569
  have htrace : WordTrace (prefixWord ++ tailWord_1604569) baseStart_1604569 baseEnd_1604569 := by
    simpa [prefixWord, tailWord_1604569, baseEnd_1604569] using wordTrace_append hprefix tailTrace_1604569
  have hstable : (prefixWord ++ tailWord_1604569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604569).length < 2 ^ (prefixWord ++ tailWord_1604569).sum := by decide
  have hdescent : baseEnd_1604569 < baseStart_1604569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604657 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 3, 5]
def baseStart_1604657 : Nat := 118140960795 + 1604657 * 2 ^ 59
def prefixEnd_1604657 : Nat := 4983230072969 + 3 ^ 40 * 1604657 * 2
def baseEnd_1604657 : Nat := 549306884401222337205215

theorem tailTrace_1604657 : CollatzResearch.WordTrace tailWord_1604657 prefixEnd_1604657 549306884401222337205215 := by
  unfold tailWord_1604657
  simp only [CollatzResearch.WordTrace]
  refine ⟨58526648947609217442188225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39017765965072811628125483 58526648947609217442188225)
  ·
    refine ⟨43894986710706913081641169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58526648947609217442188225 43894986710706913081641169)
    ·
      refine ⟨32921240033030184811230877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43894986710706913081641169 32921240033030184811230877)
      ·
        refine ⟨12345465012386319304211579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32921240033030184811230877 12345465012386319304211579)
        ·
          refine ⟨18518197518579478956317369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12345465012386319304211579 18518197518579478956317369)
          ·
            refine ⟨13888648138934609217238027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18518197518579478956317369 13888648138934609217238027)
            ·
              refine ⟨20832972208401913825857041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13888648138934609217238027 20832972208401913825857041)
              ·
                refine ⟨15624729156301435369392781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20832972208401913825857041 15624729156301435369392781)
                ·
                  refine ⟨5859273433613038263522293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15624729156301435369392781 5859273433613038263522293)
                  ·
                    refine ⟨549306884401222337205215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5859273433613038263522293 549306884401222337205215)
                    ·
                      rfl

theorem cell22_1604657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_1604657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604657 prefixEnd_1604657 := by exact prefixLift 1604657
  have htrace : WordTrace (prefixWord ++ tailWord_1604657) baseStart_1604657 baseEnd_1604657 := by
    simpa [prefixWord, tailWord_1604657, baseEnd_1604657] using wordTrace_append hprefix tailTrace_1604657
  have hstable : (prefixWord ++ tailWord_1604657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604657).length < 2 ^ (prefixWord ++ tailWord_1604657).sum := by decide
  have hdescent : baseEnd_1604657 < baseStart_1604657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604672 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 1, 6]
def baseStart_1604672 : Nat := 118140960795 + 1604672 * 2 ^ 59
def prefixEnd_1604672 : Nat := 4983230072969 + 3 ^ 40 * 1604672 * 2
def baseEnd_1604672 : Nat := 549312019207767298080169

theorem tailTrace_1604672 : CollatzResearch.WordTrace tailWord_1604672 prefixEnd_1604672 549312019207767298080169 := by
  unfold tailWord_1604672
  simp only [CollatzResearch.WordTrace]
  refine ⟨29263598021277437501992135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39018130695036583335989513 29263598021277437501992135)
  ·
    refine ⟨43895397031916156252988203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29263598021277437501992135 43895397031916156252988203)
    ·
      refine ⟨65843095547874234379482305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43895397031916156252988203 65843095547874234379482305)
      ·
        refine ⟨49382321660905675784611729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65843095547874234379482305 49382321660905675784611729)
        ·
          refine ⟨37036741245679256838458797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49382321660905675784611729 37036741245679256838458797)
          ·
            refine ⟨13888777967129721314422049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37036741245679256838458797 13888777967129721314422049)
            ·
              refine ⟨10416583475347290985816537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13888777967129721314422049 10416583475347290985816537)
              ·
                refine ⟨7812437606510468239362403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10416583475347290985816537 7812437606510468239362403)
                ·
                  refine ⟨11718656409765702359043605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7812437606510468239362403 11718656409765702359043605)
                  ·
                    refine ⟨549312019207767298080169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11718656409765702359043605 549312019207767298080169)
                    ·
                      rfl

theorem cell22_1604672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_1604672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604672 prefixEnd_1604672 := by exact prefixLift 1604672
  have htrace : WordTrace (prefixWord ++ tailWord_1604672) baseStart_1604672 baseEnd_1604672 := by
    simpa [prefixWord, tailWord_1604672, baseEnd_1604672] using wordTrace_append hprefix tailTrace_1604672
  have hstable : (prefixWord ++ tailWord_1604672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604672).length < 2 ^ (prefixWord ++ tailWord_1604672).sum := by decide
  have hdescent : baseEnd_1604672 < baseStart_1604672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604689 : List Nat := [1, 2, 2, 1, 3, 1, 5, 1, 2, 4]
def baseStart_1604689 : Nat := 118140960795 + 1604689 * 2 ^ 59
def prefixEnd_1604689 : Nat := 4983230072969 + 3 ^ 40 * 1604689 * 2
def baseEnd_1604689 : Nat := 549317838655184920405117

theorem tailTrace_1604689 : CollatzResearch.WordTrace tailWord_1604689 prefixEnd_1604689 549317838655184920405117 := by
  unfold tailWord_1604689
  simp only [CollatzResearch.WordTrace]
  refine ⟨58527816083493286907353121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39018544055662191271568747 58527816083493286907353121)
  ·
    refine ⟨43895862062619965180514841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58527816083493286907353121 43895862062619965180514841)
    ·
      refine ⟨32921896546964973885386131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43895862062619965180514841 32921896546964973885386131)
      ·
        refine ⟨49382844820447460828079197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32921896546964973885386131 49382844820447460828079197)
        ·
          refine ⟨18518566807667797810529699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49382844820447460828079197 18518566807667797810529699)
          ·
            refine ⟨27777850211501696715794549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18518566807667797810529699 27777850211501696715794549)
            ·
              refine ⟨2604173457328284067105739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27777850211501696715794549 2604173457328284067105739)
              ·
                refine ⟨3906260185992426100658609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2604173457328284067105739 3906260185992426100658609)
                ·
                  refine ⟨2929695139494319575493957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3906260185992426100658609 2929695139494319575493957)
                  ·
                    refine ⟨549317838655184920405117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2929695139494319575493957 549317838655184920405117)
                    ·
                      rfl

theorem cell22_1604689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 4].length) (baseStart_1604689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604689 prefixEnd_1604689 := by exact prefixLift 1604689
  have htrace : WordTrace (prefixWord ++ tailWord_1604689) baseStart_1604689 baseEnd_1604689 := by
    simpa [prefixWord, tailWord_1604689, baseEnd_1604689] using wordTrace_append hprefix tailTrace_1604689
  have hstable : (prefixWord ++ tailWord_1604689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604689).length < 2 ^ (prefixWord ++ tailWord_1604689).sum := by decide
  have hdescent : baseEnd_1604689 < baseStart_1604689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604725 : List Nat := [1, 3, 4, 3, 2, 1, 1, 1, 1, 5]
def baseStart_1604725 : Nat := 118140960795 + 1604725 * 2 ^ 59
def prefixEnd_1604725 : Nat := 4983230072969 + 3 ^ 40 * 1604725 * 2
def baseEnd_1604725 : Nat := 549330162190892826505007

theorem tailTrace_1604725 : CollatzResearch.WordTrace tailWord_1604725 prefixEnd_1604725 549330162190892826505007 := by
  unfold tailWord_1604725
  simp only [CollatzResearch.WordTrace]
  refine ⟨58529129111362865055663629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39019419407575243370442419 58529129111362865055663629)
  ·
    refine ⟨21948423416761074395873861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58529129111362865055663629 21948423416761074395873861)
    ·
      refine ⟨4115329390642701449226349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21948423416761074395873861 4115329390642701449226349)
      ·
        refine ⟨1543248521491013043459881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4115329390642701449226349 1543248521491013043459881)
        ·
          refine ⟨1157436391118259782594911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1543248521491013043459881 1157436391118259782594911)
          ·
            refine ⟨1736154586677389673892367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157436391118259782594911 1736154586677389673892367)
            ·
              refine ⟨2604231880016084510838551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736154586677389673892367 2604231880016084510838551)
              ·
                refine ⟨3906347820024126766257827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2604231880016084510838551 3906347820024126766257827)
                ·
                  refine ⟨5859521730036190149386741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3906347820024126766257827 5859521730036190149386741)
                  ·
                    refine ⟨549330162190892826505007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5859521730036190149386741 549330162190892826505007)
                    ·
                      rfl

theorem cell22_1604725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_1604725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604725 prefixEnd_1604725 := by exact prefixLift 1604725
  have htrace : WordTrace (prefixWord ++ tailWord_1604725) baseStart_1604725 baseEnd_1604725 := by
    simpa [prefixWord, tailWord_1604725, baseEnd_1604725] using wordTrace_append hprefix tailTrace_1604725
  have hstable : (prefixWord ++ tailWord_1604725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604725).length < 2 ^ (prefixWord ++ tailWord_1604725).sum := by decide
  have hdescent : baseEnd_1604725 < baseStart_1604725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604747 : List Nat := [1, 1, 1, 1, 4, 1, 1, 4, 1, 7]
def baseStart_1604747 : Nat := 118140960795 + 1604747 * 2 ^ 59
def prefixEnd_1604747 : Nat := 4983230072969 + 3 ^ 40 * 1604747 * 2
def baseEnd_1604747 : Nat := 549337693240492102454939

theorem tailTrace_1604747 : CollatzResearch.WordTrace tailWord_1604747 prefixEnd_1604747 549337693240492102454939 := by
  unfold tailWord_1604747
  simp only [CollatzResearch.WordTrace]
  refine ⟨58529931517283162812964495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39019954344855441875309663 58529931517283162812964495)
  ·
    refine ⟨87794897275924744219446743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58529931517283162812964495 87794897275924744219446743)
    ·
      refine ⟨131692345913887116329170115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87794897275924744219446743 131692345913887116329170115)
      ·
        refine ⟨197538518870830674493755173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131692345913887116329170115 197538518870830674493755173)
        ·
          refine ⟨37038472288280751467579095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197538518870830674493755173 37038472288280751467579095)
          ·
            refine ⟨55557708432421127201368643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37038472288280751467579095 55557708432421127201368643)
            ·
              refine ⟨83336562648631690802052965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55557708432421127201368643 83336562648631690802052965)
              ·
                refine ⟨15625605496618442025384931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83336562648631690802052965 15625605496618442025384931)
                ·
                  refine ⟨23438408244927663038077397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15625605496618442025384931 23438408244927663038077397)
                  ·
                    refine ⟨549337693240492102454939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23438408244927663038077397 549337693240492102454939)
                    ·
                      rfl

theorem cell22_1604747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 7].length) (baseStart_1604747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604747 prefixEnd_1604747 := by exact prefixLift 1604747
  have htrace : WordTrace (prefixWord ++ tailWord_1604747) baseStart_1604747 baseEnd_1604747 := by
    simpa [prefixWord, tailWord_1604747, baseEnd_1604747] using wordTrace_append hprefix tailTrace_1604747
  have hstable : (prefixWord ++ tailWord_1604747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604747).length < 2 ^ (prefixWord ++ tailWord_1604747).sum := by decide
  have hdescent : baseEnd_1604747 < baseStart_1604747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604766 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 7]
def baseStart_1604766 : Nat := 118140960795 + 1604766 * 2 ^ 59
def prefixEnd_1604766 : Nat := 4983230072969 + 3 ^ 40 * 1604766 * 2
def baseEnd_1604766 : Nat := 183114732442927462076627

theorem tailTrace_1604766 : CollatzResearch.WordTrace tailWord_1604766 prefixEnd_1604766 183114732442927462076627 := by
  unfold tailWord_1604766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7316328063026791132238269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39020416336142886038604101 7316328063026791132238269)
  ·
    refine ⟨2743623023635046674589351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7316328063026791132238269 2743623023635046674589351)
    ·
      refine ⟨4115434535452570011884027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2743623023635046674589351 4115434535452570011884027)
      ·
        refine ⟨6173151803178855017826041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4115434535452570011884027 6173151803178855017826041)
        ·
          refine ⟨4629863852384141263369531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6173151803178855017826041 4629863852384141263369531)
          ·
            refine ⟨6944795778576211895054297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4629863852384141263369531 6944795778576211895054297)
            ·
              refine ⟨5208596833932158921290723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6944795778576211895054297 5208596833932158921290723)
              ·
                refine ⟨7812895250898238381936085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5208596833932158921290723 7812895250898238381936085)
                ·
                  refine ⟨183114732442927462076627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7812895250898238381936085 183114732442927462076627)
                  ·
                    rfl

theorem cell22_1604766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_1604766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604766 prefixEnd_1604766 := by exact prefixLift 1604766
  have htrace : WordTrace (prefixWord ++ tailWord_1604766) baseStart_1604766 baseEnd_1604766 := by
    simpa [prefixWord, tailWord_1604766, baseEnd_1604766] using wordTrace_append hprefix tailTrace_1604766
  have hstable : (prefixWord ++ tailWord_1604766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604766).length < 2 ^ (prefixWord ++ tailWord_1604766).sum := by decide
  have hdescent : baseEnd_1604766 < baseStart_1604766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604770 : List Nat := [3, 3, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_1604770 : Nat := 118140960795 + 1604770 * 2 ^ 59
def prefixEnd_1604770 : Nat := 4983230072969 + 3 ^ 40 * 1604770 * 2
def baseEnd_1604770 : Nat := 549345566610527709129869

theorem tailTrace_1604770 : CollatzResearch.WordTrace tailWord_1604770 prefixEnd_1604770 549345566610527709129869 := by
  unfold tailWord_1604770
  simp only [CollatzResearch.WordTrace]
  refine ⟨14632692599049959435262941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39020513597466558494034509 14632692599049959435262941)
  ·
    refine ⟨5487259724643734788223603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14632692599049959435262941 5487259724643734788223603)
    ·
      refine ⟨8230889586965602182335405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5487259724643734788223603 8230889586965602182335405)
      ·
        refine ⟨3086583595112100818375777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8230889586965602182335405 3086583595112100818375777)
        ·
          refine ⟨2314937696334075613781833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3086583595112100818375777 2314937696334075613781833)
          ·
            refine ⟨1736203272250556710336375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2314937696334075613781833 1736203272250556710336375)
            ·
              refine ⟨2604304908375835065504563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736203272250556710336375 2604304908375835065504563)
              ·
                refine ⟨3906457362563752598256845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2604304908375835065504563 3906457362563752598256845)
                ·
                  refine ⟨1464921510961407224346317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3906457362563752598256845 1464921510961407224346317)
                  ·
                    refine ⟨549345566610527709129869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1464921510961407224346317 549345566610527709129869)
                    ·
                      rfl

theorem cell22_1604770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_1604770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604770 prefixEnd_1604770 := by exact prefixLift 1604770
  have htrace : WordTrace (prefixWord ++ tailWord_1604770) baseStart_1604770 baseEnd_1604770 := by
    simpa [prefixWord, tailWord_1604770, baseEnd_1604770] using wordTrace_append hprefix tailTrace_1604770
  have hstable : (prefixWord ++ tailWord_1604770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604770).length < 2 ^ (prefixWord ++ tailWord_1604770).sum := by decide
  have hdescent : baseEnd_1604770 < baseStart_1604770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604777 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 12]
def baseStart_1604777 : Nat := 118140960795 + 1604777 * 2 ^ 59
def prefixEnd_1604777 : Nat := 4983230072969 + 3 ^ 40 * 1604777 * 2
def baseEnd_1604777 : Nat := 183115987617860674734949

theorem tailTrace_1604777 : CollatzResearch.WordTrace tailWord_1604777 prefixEnd_1604777 183115987617860674734949 := by
  unfold tailWord_1604777
  simp only [CollatzResearch.WordTrace]
  refine ⟨58531025707174477936556585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39020683804782985291037723 58531025707174477936556585)
  ·
    refine ⟨43898269280380858452417439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58531025707174477936556585 43898269280380858452417439)
    ·
      refine ⟨65847403920571287678626159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43898269280380858452417439 65847403920571287678626159)
      ·
        refine ⟨98771105880856931517939239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65847403920571287678626159 98771105880856931517939239)
        ·
          refine ⟨148156658821285397276908859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98771105880856931517939239 148156658821285397276908859)
          ·
            refine ⟨222234988231928095915363289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148156658821285397276908859 222234988231928095915363289)
            ·
              refine ⟨166676241173946071936522467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222234988231928095915363289 166676241173946071936522467)
              ·
                refine ⟨250014361760919107904783701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166676241173946071936522467 250014361760919107904783701)
                ·
                  refine ⟨183115987617860674734949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 250014361760919107904783701 183115987617860674734949)
                  ·
                    rfl

theorem cell22_1604777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 12].length) (baseStart_1604777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604777 prefixEnd_1604777 := by exact prefixLift 1604777
  have htrace : WordTrace (prefixWord ++ tailWord_1604777) baseStart_1604777 baseEnd_1604777 := by
    simpa [prefixWord, tailWord_1604777, baseEnd_1604777] using wordTrace_append hprefix tailTrace_1604777
  have hstable : (prefixWord ++ tailWord_1604777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604777).length < 2 ^ (prefixWord ++ tailWord_1604777).sum := by decide
  have hdescent : baseEnd_1604777 < baseStart_1604777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604796 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 3, 4]
def baseStart_1604796 : Nat := 118140960795 + 1604796 * 2 ^ 59
def prefixEnd_1604796 : Nat := 4983230072969 + 3 ^ 40 * 1604796 * 2
def baseEnd_1604796 : Nat := 549354466941872307979789

theorem tailTrace_1604796 : CollatzResearch.WordTrace tailWord_1604796 prefixEnd_1604796 549354466941872307979789 := by
  unfold tailWord_1604796
  simp only [CollatzResearch.WordTrace]
  refine ⟨29265859347052822090749121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39021145796070429454332161 29265859347052822090749121)
  ·
    refine ⟨21949394510289616568061841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29265859347052822090749121 21949394510289616568061841)
    ·
      refine ⟨16462045882717212426046381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21949394510289616568061841 16462045882717212426046381)
      ·
        refine ⟨6173267206018954659767393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16462045882717212426046381 6173267206018954659767393)
        ·
          refine ⟨4629950404514215994825545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6173267206018954659767393 4629950404514215994825545)
          ·
            refine ⟨3472462803385661996119159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4629950404514215994825545 3472462803385661996119159)
            ·
              refine ⟨5208694205078492994178739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3472462803385661996119159 5208694205078492994178739)
              ·
                refine ⟨7813041307617739491268109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5208694205078492994178739 7813041307617739491268109)
                ·
                  refine ⟨2929890490356652309225541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7813041307617739491268109 2929890490356652309225541)
                  ·
                    refine ⟨549354466941872307979789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2929890490356652309225541 549354466941872307979789)
                    ·
                      rfl

theorem cell22_1604796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_1604796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604796 prefixEnd_1604796 := by exact prefixLift 1604796
  have htrace : WordTrace (prefixWord ++ tailWord_1604796) baseStart_1604796 baseEnd_1604796 := by
    simpa [prefixWord, tailWord_1604796, baseEnd_1604796] using wordTrace_append hprefix tailTrace_1604796
  have hstable : (prefixWord ++ tailWord_1604796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604796).length < 2 ^ (prefixWord ++ tailWord_1604796).sum := by decide
  have hdescent : baseEnd_1604796 < baseStart_1604796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604888 : List Nat := [2, 1, 2, 3, 1, 4, 2, 1, 3, 3]
def baseStart_1604888 : Nat := 118140960795 + 1604888 * 2 ^ 59
def prefixEnd_1604888 : Nat := 4983230072969 + 3 ^ 40 * 1604888 * 2
def baseEnd_1604888 : Nat := 549385960422014734679507

theorem tailTrace_1604888 : CollatzResearch.WordTrace tailWord_1604888 prefixEnd_1604888 549385960422014734679507 := by
  unfold tailWord_1604888
  simp only [CollatzResearch.WordTrace]
  refine ⟨29267537104886171946923659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39023382806514895929231545 29267537104886171946923659)
  ·
    refine ⟨43901305657329257920385489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29267537104886171946923659 43901305657329257920385489)
    ·
      refine ⟨32925979242996943440289117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43901305657329257920385489 32925979242996943440289117)
      ·
        refine ⟨12347242216123853790108419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32925979242996943440289117 12347242216123853790108419)
        ·
          refine ⟨18520863324185780685162629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12347242216123853790108419 18520863324185780685162629)
          ·
            refine ⟨3472661873284833878467993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18520863324185780685162629 3472661873284833878467993)
            ·
              refine ⟨2604496404963625408850995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3472661873284833878467993 2604496404963625408850995)
              ·
                refine ⟨3906744607445438113276493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2604496404963625408850995 3906744607445438113276493)
                ·
                  refine ⟨1465029227792039292478685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3906744607445438113276493 1465029227792039292478685)
                  ·
                    refine ⟨549385960422014734679507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1465029227792039292478685 549385960422014734679507)
                    ·
                      rfl

theorem cell22_1604888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_1604888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604888 prefixEnd_1604888 := by exact prefixLift 1604888
  have htrace : WordTrace (prefixWord ++ tailWord_1604888) baseStart_1604888 baseEnd_1604888 := by
    simpa [prefixWord, tailWord_1604888, baseEnd_1604888] using wordTrace_append hprefix tailTrace_1604888
  have hstable : (prefixWord ++ tailWord_1604888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604888).length < 2 ^ (prefixWord ++ tailWord_1604888).sum := by decide
  have hdescent : baseEnd_1604888 < baseStart_1604888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604894 : List Nat := [4, 3, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_1604894 : Nat := 118140960795 + 1604894 * 2 ^ 59
def prefixEnd_1604894 : Nat := 4983230072969 + 3 ^ 40 * 1604894 * 2
def baseEnd_1604894 : Nat := 549388014344632719029489

theorem tailTrace_1604894 : CollatzResearch.WordTrace tailWord_1604894 prefixEnd_1604894 549388014344632719029489 := by
  unfold tailWord_1604894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7316911630968825864820717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39023528698500404612377157 7316911630968825864820717)
  ·
    refine ⟨2743841861613309699307769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7316911630968825864820717 2743841861613309699307769)
    ·
      refine ⟨2057881396209982274480827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2743841861613309699307769 2057881396209982274480827)
      ·
        refine ⟨3086822094314973411721241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2057881396209982274480827 3086822094314973411721241)
        ·
          refine ⟨2315116570736230058790931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3086822094314973411721241 2315116570736230058790931)
          ·
            refine ⟨3472674856104345088186397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2315116570736230058790931 3472674856104345088186397)
            ·
              refine ⟨1302253071039129408069899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3472674856104345088186397 1302253071039129408069899)
              ·
                refine ⟨1953379606558694112104849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302253071039129408069899 1953379606558694112104849)
                ·
                  refine ⟨1465034704919020584078637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1953379606558694112104849 1465034704919020584078637)
                  ·
                    refine ⟨549388014344632719029489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1465034704919020584078637 549388014344632719029489)
                    ·
                      rfl

theorem cell22_1604894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_1604894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604894 prefixEnd_1604894 := by exact prefixLift 1604894
  have htrace : WordTrace (prefixWord ++ tailWord_1604894) baseStart_1604894 baseEnd_1604894 := by
    simpa [prefixWord, tailWord_1604894, baseEnd_1604894] using wordTrace_append hprefix tailTrace_1604894
  have hstable : (prefixWord ++ tailWord_1604894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604894).length < 2 ^ (prefixWord ++ tailWord_1604894).sum := by decide
  have hdescent : baseEnd_1604894 < baseStart_1604894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1604995 : List Nat := [1, 1, 1, 3, 5, 2, 2, 2, 2, 3]
def baseStart_1604995 : Nat := 118140960795 + 1604995 * 2 ^ 59
def prefixEnd_1604995 : Nat := 4983230072969 + 3 ^ 40 * 1604995 * 2
def baseEnd_1604995 : Nat := 549422588708702122254179

theorem tailTrace_1604995 : CollatzResearch.WordTrace tailWord_1604995 prefixEnd_1604995 549422588708702122254179 := by
  unfold tailWord_1604995
  simp only [CollatzResearch.WordTrace]
  refine ⟨58538976820384701167992439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39025984546923134111994959 58538976820384701167992439)
  ·
    refine ⟨87808465230577051751988659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58538976820384701167992439 87808465230577051751988659)
    ·
      refine ⟨131712697845865577627982989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87808465230577051751988659 131712697845865577627982989)
      ·
        refine ⟨49392261692199591610493621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131712697845865577627982989 49392261692199591610493621)
        ·
          refine ⟨4630524533643711713483777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49392261692199591610493621 4630524533643711713483777)
          ·
            refine ⟨3472893400232783785112833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4630524533643711713483777 3472893400232783785112833)
            ·
              refine ⟨2604670050174587838834625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3472893400232783785112833 2604670050174587838834625)
              ·
                refine ⟨1953502537630940879125969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2604670050174587838834625 1953502537630940879125969)
                ·
                  refine ⟨1465126903223205659344477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1953502537630940879125969 1465126903223205659344477)
                  ·
                    refine ⟨549422588708702122254179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1465126903223205659344477 549422588708702122254179)
                    ·
                      rfl

theorem cell22_1604995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 3].length) (baseStart_1604995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1604995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1604995 prefixEnd_1604995 := by exact prefixLift 1604995
  have htrace : WordTrace (prefixWord ++ tailWord_1604995) baseStart_1604995 baseEnd_1604995 := by
    simpa [prefixWord, tailWord_1604995, baseEnd_1604995] using wordTrace_append hprefix tailTrace_1604995
  have hstable : (prefixWord ++ tailWord_1604995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1604995).length < 2 ^ (prefixWord ++ tailWord_1604995).sum := by decide
  have hdescent : baseEnd_1604995 < baseStart_1604995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1604995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605023 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 5, 3]
def baseStart_1605023 : Nat := 118140960795 + 1605023 * 2 ^ 59
def prefixEnd_1605023 : Nat := 4983230072969 + 3 ^ 40 * 1605023 * 2
def baseEnd_1605023 : Nat := 549432173680919382554093

theorem tailTrace_1605023 : CollatzResearch.WordTrace tailWord_1605023 prefixEnd_1605023 549432173680919382554093 := by
  unfold tailWord_1605023
  simp only [CollatzResearch.WordTrace]
  refine ⟨58539998064283261950011723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39026665376188841300007815 58539998064283261950011723)
  ·
    refine ⟨87809997096424892925017585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58539998064283261950011723 87809997096424892925017585)
    ·
      refine ⟨65857497822318669693763189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87809997096424892925017585 65857497822318669693763189)
      ·
        refine ⟨6174140420842375283790299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65857497822318669693763189 6174140420842375283790299)
        ·
          refine ⟨9261210631263562925685449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6174140420842375283790299 9261210631263562925685449)
          ·
            refine ⟨6945907973447672194264087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9261210631263562925685449 6945907973447672194264087)
            ·
              refine ⟨10418861960171508291396131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6945907973447672194264087 10418861960171508291396131)
              ·
                refine ⟨15628292940257262437094197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10418861960171508291396131 15628292940257262437094197)
                ·
                  refine ⟨1465152463149118353477581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15628292940257262437094197 1465152463149118353477581)
                  ·
                    refine ⟨549432173680919382554093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1465152463149118353477581 549432173680919382554093)
                    ·
                      rfl

theorem cell22_1605023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 3].length) (baseStart_1605023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605023 prefixEnd_1605023 := by exact prefixLift 1605023
  have htrace : WordTrace (prefixWord ++ tailWord_1605023) baseStart_1605023 baseEnd_1605023 := by
    simpa [prefixWord, tailWord_1605023, baseEnd_1605023] using wordTrace_append hprefix tailTrace_1605023
  have hstable : (prefixWord ++ tailWord_1605023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605023).length < 2 ^ (prefixWord ++ tailWord_1605023).sum := by decide
  have hdescent : baseEnd_1605023 < baseStart_1605023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605068 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 2, 5]
def baseStart_1605068 : Nat := 118140960795 + 1605068 * 2 ^ 59
def prefixEnd_1605068 : Nat := 4983230072969 + 3 ^ 40 * 1605068 * 2
def baseEnd_1605068 : Nat := 549447578100554265178955

theorem tailTrace_1605068 : CollatzResearch.WordTrace tailWord_1605068 prefixEnd_1605068 549447578100554265178955 := by
  unfold tailWord_1605068
  simp only [CollatzResearch.WordTrace]
  refine ⟨29270819674560117317699929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39027759566080156423599905 29270819674560117317699929)
  ·
    refine ⟨21953114755920087988274947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29270819674560117317699929 21953114755920087988274947)
    ·
      refine ⟨32929672133880131982412421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21953114755920087988274947 32929672133880131982412421)
      ·
        refine ⟨6174313525102524746702329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32929672133880131982412421 6174313525102524746702329)
        ·
          refine ⟨4630735143826893560026747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6174313525102524746702329 4630735143826893560026747)
          ·
            refine ⟨6946102715740340340040121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4630735143826893560026747 6946102715740340340040121)
            ·
              refine ⟨5209577036805255255030091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6946102715740340340040121 5209577036805255255030091)
              ·
                refine ⟨7814365555207882882545137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5209577036805255255030091 7814365555207882882545137)
                ·
                  refine ⟨5860774166405912161908853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7814365555207882882545137 5860774166405912161908853)
                  ·
                    refine ⟨549447578100554265178955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5860774166405912161908853 549447578100554265178955)
                    ·
                      rfl

theorem cell22_1605068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_1605068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605068 prefixEnd_1605068 := by exact prefixLift 1605068
  have htrace : WordTrace (prefixWord ++ tailWord_1605068) baseStart_1605068 baseEnd_1605068 := by
    simpa [prefixWord, tailWord_1605068, baseEnd_1605068] using wordTrace_append hprefix tailTrace_1605068
  have hstable : (prefixWord ++ tailWord_1605068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605068).length < 2 ^ (prefixWord ++ tailWord_1605068).sum := by decide
  have hdescent : baseEnd_1605068 < baseStart_1605068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605111 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 3, 6]
def baseStart_1605111 : Nat := 118140960795 + 1605111 * 2 ^ 59
def prefixEnd_1605111 : Nat := 4983230072969 + 3 ^ 40 * 1605111 * 2
def baseEnd_1605111 : Nat := 549462297879316486353823

theorem tailTrace_1605111 : CollatzResearch.WordTrace tailWord_1605111 prefixEnd_1605111 549462297879316486353823 := by
  unfold tailWord_1605111
  simp only [CollatzResearch.WordTrace]
  refine ⟨58543207687964452979215187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39028805125309635319476791 58543207687964452979215187)
  ·
    refine ⟨87814811531946679468822781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58543207687964452979215187 87814811531946679468822781)
    ·
      refine ⟨32930554324480004800808543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87814811531946679468822781 32930554324480004800808543)
      ·
        refine ⟨49395831486720007201212815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32930554324480004800808543 49395831486720007201212815)
        ·
          refine ⟨74093747230080010801819223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49395831486720007201212815 74093747230080010801819223)
          ·
            refine ⟨111140620845120016202728835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74093747230080010801819223 111140620845120016202728835)
            ·
              refine ⟨166710931267680024304093253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111140620845120016202728835 166710931267680024304093253)
              ·
                refine ⟨31258299612690004557017485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166710931267680024304093253 31258299612690004557017485)
                ·
                  refine ⟨11721862354758751708881557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31258299612690004557017485 11721862354758751708881557)
                  ·
                    refine ⟨549462297879316486353823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11721862354758751708881557 549462297879316486353823)
                    ·
                      rfl

theorem cell22_1605111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_1605111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605111 prefixEnd_1605111 := by exact prefixLift 1605111
  have htrace : WordTrace (prefixWord ++ tailWord_1605111) baseStart_1605111 baseEnd_1605111 := by
    simpa [prefixWord, tailWord_1605111, baseEnd_1605111] using wordTrace_append hprefix tailTrace_1605111
  have hstable : (prefixWord ++ tailWord_1605111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605111).length < 2 ^ (prefixWord ++ tailWord_1605111).sum := by decide
  have hdescent : baseEnd_1605111 < baseStart_1605111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605134 : List Nat := [4, 1, 1, 2, 5, 1, 1, 2, 1, 4]
def baseStart_1605134 : Nat := 118140960795 + 1605134 * 2 ^ 59
def prefixEnd_1605134 : Nat := 4983230072969 + 3 ^ 40 * 1605134 * 2
def baseEnd_1605134 : Nat := 549470171249352093028753

theorem tailTrace_1605134 : CollatzResearch.WordTrace tailWord_1605134 prefixEnd_1605134 549470171249352093028753 := by
  unfold tailWord_1605134
  simp only [CollatzResearch.WordTrace]
  refine ⟨7318005820860140988412807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39029364377920751938201637 7318005820860140988412807)
  ·
    refine ⟨10977008731290211482619211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7318005820860140988412807 10977008731290211482619211)
    ·
      refine ⟨16465513096935317223928817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10977008731290211482619211 16465513096935317223928817)
      ·
        refine ⟨12349134822701487917946613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16465513096935317223928817 12349134822701487917946613)
        ·
          refine ⟨1157731389628264492307495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12349134822701487917946613 1157731389628264492307495)
          ·
            refine ⟨1736597084442396738461243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1157731389628264492307495 1736597084442396738461243)
            ·
              refine ⟨2604895626663595107691865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1736597084442396738461243 2604895626663595107691865)
              ·
                refine ⟨1953671719997696330768899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2604895626663595107691865 1953671719997696330768899)
                ·
                  refine ⟨2930507579996544496153349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1953671719997696330768899 2930507579996544496153349)
                  ·
                    refine ⟨549470171249352093028753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2930507579996544496153349 549470171249352093028753)
                    ·
                      rfl

theorem cell22_1605134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_1605134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605134 prefixEnd_1605134 := by exact prefixLift 1605134
  have htrace : WordTrace (prefixWord ++ tailWord_1605134) baseStart_1605134 baseEnd_1605134 := by
    simpa [prefixWord, tailWord_1605134, baseEnd_1605134] using wordTrace_append hprefix tailTrace_1605134
  have hstable : (prefixWord ++ tailWord_1605134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605134).length < 2 ^ (prefixWord ++ tailWord_1605134).sum := by decide
  have hdescent : baseEnd_1605134 < baseStart_1605134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605160 : List Nat := [2, 1, 5, 2, 3, 9]
def baseStart_1605160 : Nat := 118140960795 + 1605160 * 2 ^ 59
def prefixEnd_1605160 : Nat := 4983230072969 + 3 ^ 40 * 1605160 * 2
def baseEnd_1605160 : Nat := 6783692241736996196033

theorem tailTrace_1605160 : CollatzResearch.WordTrace tailWord_1605160 prefixEnd_1605160 6783692241736996196033 := by
  unfold tailWord_1605160
  simp only [CollatzResearch.WordTrace]
  refine ⟨29272497432393467173874467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39029996576524622898499289 29272497432393467173874467)
  ·
    refine ⟨43908746148590200760811701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29272497432393467173874467 43908746148590200760811701)
    ·
      refine ⟨4116444951430331321326097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43908746148590200760811701 4116444951430331321326097)
      ·
        refine ⟨3087333713572748490994573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4116444951430331321326097 3087333713572748490994573)
        ·
          refine ⟨1157750142589780684122965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3087333713572748490994573 1157750142589780684122965)
          ·
            refine ⟨6783692241736996196033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1157750142589780684122965 6783692241736996196033)
            ·
              rfl

theorem cell22_1605160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 9].length) (baseStart_1605160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605160 prefixEnd_1605160 := by exact prefixLift 1605160
  have htrace : WordTrace (prefixWord ++ tailWord_1605160) baseStart_1605160 baseEnd_1605160 := by
    simpa [prefixWord, tailWord_1605160, baseEnd_1605160] using wordTrace_append hprefix tailTrace_1605160
  have hstable : (prefixWord ++ tailWord_1605160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605160).length < 2 ^ (prefixWord ++ tailWord_1605160).sum := by decide
  have hdescent : baseEnd_1605160 < baseStart_1605160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605173 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 2, 6]
def baseStart_1605173 : Nat := 118140960795 + 1605173 * 2 ^ 59
def prefixEnd_1605173 : Nat := 4983230072969 + 3 ^ 40 * 1605173 * 2
def baseEnd_1605173 : Nat := 549483521746368991303633

theorem tailTrace_1605173 : CollatzResearch.WordTrace tailWord_1605173 prefixEnd_1605173 549483521746368991303633 := by
  unfold tailWord_1605173
  simp only [CollatzResearch.WordTrace]
  refine ⟨58545469013739837567972173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39030312675826558378648115 58545469013739837567972173)
  ·
    refine ⟨21954550880152439087989565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58545469013739837567972173 21954550880152439087989565)
    ·
      refine ⟨8232956580057164657996087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21954550880152439087989565 8232956580057164657996087)
      ·
        refine ⟨12349434870085746986994131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8232956580057164657996087 12349434870085746986994131)
        ·
          refine ⟨18524152305128620480491197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12349434870085746986994131 18524152305128620480491197)
          ·
            refine ⟨6946557114423232680184199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18524152305128620480491197 6946557114423232680184199)
            ·
              refine ⟨10419835671634849020276299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6946557114423232680184199 10419835671634849020276299)
              ·
                refine ⟨15629753507452273530414449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10419835671634849020276299 15629753507452273530414449)
                ·
                  refine ⟨11722315130589205147810837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15629753507452273530414449 11722315130589205147810837)
                  ·
                    refine ⟨549483521746368991303633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11722315130589205147810837 549483521746368991303633)
                    ·
                      rfl

theorem cell22_1605173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_1605173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605173 prefixEnd_1605173 := by exact prefixLift 1605173
  have htrace : WordTrace (prefixWord ++ tailWord_1605173) baseStart_1605173 baseEnd_1605173 := by
    simpa [prefixWord, tailWord_1605173, baseEnd_1605173] using wordTrace_append hprefix tailTrace_1605173
  have hstable : (prefixWord ++ tailWord_1605173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605173).length < 2 ^ (prefixWord ++ tailWord_1605173).sum := by decide
  have hdescent : baseEnd_1605173 < baseStart_1605173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605280 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 4, 4]
def baseStart_1605280 : Nat := 118140960795 + 1605280 * 2 ^ 59
def prefixEnd_1605280 : Nat := 4983230072969 + 3 ^ 40 * 1605280 * 2
def baseEnd_1605280 : Nat := 549520150033056378878305

theorem tailTrace_1605280 : CollatzResearch.WordTrace tailWord_1605280 prefixEnd_1605280 549520150033056378878305 := by
  unfold tailWord_1605280
  simp only [CollatzResearch.WordTrace]
  refine ⟨29274685812176097421058647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39032914416234796561411529 29274685812176097421058647)
  ·
    refine ⟨43912028718264146131587971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29274685812176097421058647 43912028718264146131587971)
    ·
      refine ⟨65868043077396219197381957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43912028718264146131587971 65868043077396219197381957)
      ·
        refine ⟨12350258077011791099509117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65868043077396219197381957 12350258077011791099509117)
        ·
          refine ⟨4631346778879421662315919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12350258077011791099509117 4631346778879421662315919)
          ·
            refine ⟨6947020168319132493473879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4631346778879421662315919 6947020168319132493473879)
            ·
              refine ⟨10420530252478698740210819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6947020168319132493473879 10420530252478698740210819)
              ·
                refine ⟨15630795378718048110316229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10420530252478698740210819 15630795378718048110316229)
                ·
                  refine ⟨2930774133509634020684293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15630795378718048110316229 2930774133509634020684293)
                  ·
                    refine ⟨549520150033056378878305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2930774133509634020684293 549520150033056378878305)
                    ·
                      rfl

theorem cell22_1605280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_1605280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605280 prefixEnd_1605280 := by exact prefixLift 1605280
  have htrace : WordTrace (prefixWord ++ tailWord_1605280) baseStart_1605280 baseEnd_1605280 := by
    simpa [prefixWord, tailWord_1605280, baseEnd_1605280] using wordTrace_append hprefix tailTrace_1605280
  have hstable : (prefixWord ++ tailWord_1605280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605280).length < 2 ^ (prefixWord ++ tailWord_1605280).sum := by decide
  have hdescent : baseEnd_1605280 < baseStart_1605280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605284 : List Nat := [2, 3, 1, 2, 2, 3, 3, 2, 4]
def baseStart_1605284 : Nat := 118140960795 + 1605284 * 2 ^ 59
def prefixEnd_1605284 : Nat := 4983230072969 + 3 ^ 40 * 1605284 * 2
def baseEnd_1605284 : Nat := 183173839771600567259431

theorem tailTrace_1605284 : CollatzResearch.WordTrace tailWord_1605284 prefixEnd_1605284 183173839771600567259431 := by
  unfold tailWord_1605284
  simp only [CollatzResearch.WordTrace]
  refine ⟨29274758758168851762631453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39033011677558469016841937 29274758758168851762631453)
  ·
    refine ⟨10978034534313319410986795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29274758758168851762631453 10978034534313319410986795)
    ·
      refine ⟨16467051801469979116480193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10978034534313319410986795 16467051801469979116480193)
      ·
        refine ⟨12350288851102484337360145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16467051801469979116480193 12350288851102484337360145)
        ·
          refine ⟨9262716638326863253020109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12350288851102484337360145 9262716638326863253020109)
          ·
            refine ⟨3473518739372573719882541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9262716638326863253020109 3473518739372573719882541)
            ·
              refine ⟨1302569527264715144955953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3473518739372573719882541 1302569527264715144955953)
              ·
                refine ⟨976927145448536358716965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1302569527264715144955953 976927145448536358716965)
                ·
                  refine ⟨183173839771600567259431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 976927145448536358716965 183173839771600567259431)
                  ·
                    rfl

theorem cell22_1605284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_1605284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605284 prefixEnd_1605284 := by exact prefixLift 1605284
  have htrace : WordTrace (prefixWord ++ tailWord_1605284) baseStart_1605284 baseEnd_1605284 := by
    simpa [prefixWord, tailWord_1605284, baseEnd_1605284] using wordTrace_append hprefix tailTrace_1605284
  have hstable : (prefixWord ++ tailWord_1605284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605284).length < 2 ^ (prefixWord ++ tailWord_1605284).sum := by decide
  have hdescent : baseEnd_1605284 < baseStart_1605284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605323 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 9]
def baseStart_1605323 : Nat := 118140960795 + 1605323 * 2 ^ 59
def prefixEnd_1605323 : Nat := 4983230072969 + 3 ^ 40 * 1605323 * 2
def baseEnd_1605323 : Nat := 183178289937272866684391

theorem tailTrace_1605323 : CollatzResearch.WordTrace tailWord_1605323 prefixEnd_1605323 183178289937272866684391 := by
  unfold tailWord_1605323
  simp only [CollatzResearch.WordTrace]
  refine ⟨58550939963196413185932623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39033959975464275457288415 58550939963196413185932623)
  ·
    refine ⟨87826409944794619778898935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58550939963196413185932623 87826409944794619778898935)
    ·
      refine ⟨131739614917191929668348403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87826409944794619778898935 131739614917191929668348403)
      ·
        refine ⟨197609422375787894502522605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131739614917191929668348403 197609422375787894502522605)
        ·
          refine ⟨74103533390920460438445977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197609422375787894502522605 74103533390920460438445977)
          ·
            refine ⟨55577650043190345328834483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74103533390920460438445977 55577650043190345328834483)
            ·
              refine ⟨83366475064785517993251725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55577650043190345328834483 83366475064785517993251725)
              ·
                refine ⟨31262428149294569247469397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83366475064785517993251725 31262428149294569247469397)
                ·
                  refine ⟨183178289937272866684391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31262428149294569247469397 183178289937272866684391)
                  ·
                    rfl

theorem cell22_1605323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 9].length) (baseStart_1605323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605323 prefixEnd_1605323 := by exact prefixLift 1605323
  have htrace : WordTrace (prefixWord ++ tailWord_1605323) baseStart_1605323 baseEnd_1605323 := by
    simpa [prefixWord, tailWord_1605323, baseEnd_1605323] using wordTrace_append hprefix tailTrace_1605323
  have hstable : (prefixWord ++ tailWord_1605323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605323).length < 2 ^ (prefixWord ++ tailWord_1605323).sum := by decide
  have hdescent : baseEnd_1605323 < baseStart_1605323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605357 : List Nat := [1, 5, 1, 2, 1, 2, 2, 3, 5]
def baseStart_1605357 : Nat := 118140960795 + 1605357 * 2 ^ 59
def prefixEnd_1605357 : Nat := 4983230072969 + 3 ^ 40 * 1605357 * 2
def baseEnd_1605357 : Nat := 183182169568884614901023

theorem tailTrace_1605357 : CollatzResearch.WordTrace tailWord_1605357 prefixEnd_1605357 183182169568884614901023 := by
  unfold tailWord_1605357
  simp only [CollatzResearch.WordTrace]
  refine ⟨58552180045073236992670325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39034786696715491328446883 58552180045073236992670325)
  ·
    refine ⟨5489266879225615968062843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58552180045073236992670325 5489266879225615968062843)
    ·
      refine ⟨8233900318838423952094265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5489266879225615968062843 8233900318838423952094265)
      ·
        refine ⟨6175425239128817964070699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8233900318838423952094265 6175425239128817964070699)
        ·
          refine ⟨9263137858693226946106049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6175425239128817964070699 9263137858693226946106049)
          ·
            refine ⟨6947353394019920209579537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9263137858693226946106049 6947353394019920209579537)
            ·
              refine ⟨5210515045514940157184653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6947353394019920209579537 5210515045514940157184653)
              ·
                refine ⟨1953943142068102558944245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5210515045514940157184653 1953943142068102558944245)
                ·
                  refine ⟨183182169568884614901023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1953943142068102558944245 183182169568884614901023)
                  ·
                    rfl

theorem cell22_1605357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_1605357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605357 prefixEnd_1605357 := by exact prefixLift 1605357
  have htrace : WordTrace (prefixWord ++ tailWord_1605357) baseStart_1605357 baseEnd_1605357 := by
    simpa [prefixWord, tailWord_1605357, baseEnd_1605357] using wordTrace_append hprefix tailTrace_1605357
  have hstable : (prefixWord ++ tailWord_1605357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605357).length < 2 ^ (prefixWord ++ tailWord_1605357).sum := by decide
  have hdescent : baseEnd_1605357 < baseStart_1605357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605400 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 3, 5]
def baseStart_1605400 : Nat := 118140960795 + 1605400 * 2 ^ 59
def prefixEnd_1605400 : Nat := 4983230072969 + 3 ^ 40 * 1605400 * 2
def baseEnd_1605400 : Nat := 549561228485416065877937

theorem tailTrace_1605400 : CollatzResearch.WordTrace tailWord_1605400 prefixEnd_1605400 549561228485416065877937 := by
  unfold tailWord_1605400
  simp only [CollatzResearch.WordTrace]
  refine ⟨29276874191958727668242827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39035832255944970224323769 29276874191958727668242827)
  ·
    refine ⟨43915311287938091502364241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29276874191958727668242827 43915311287938091502364241)
    ·
      refine ⟨32936483465953568626773181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43915311287938091502364241 32936483465953568626773181)
      ·
        refine ⟨12351181299732588235039943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32936483465953568626773181 12351181299732588235039943)
        ·
          refine ⟨18526771949598882352559915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12351181299732588235039943 18526771949598882352559915)
          ·
            refine ⟨27790157924398323528839873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18526771949598882352559915 27790157924398323528839873)
            ·
              refine ⟨20842618443298742646629905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27790157924398323528839873 20842618443298742646629905)
              ·
                refine ⟨15631963832474056984972429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20842618443298742646629905 15631963832474056984972429)
                ·
                  refine ⟨5861986437177771369364661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15631963832474056984972429 5861986437177771369364661)
                  ·
                    refine ⟨549561228485416065877937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5861986437177771369364661 549561228485416065877937)
                    ·
                      rfl

theorem cell22_1605400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_1605400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605400 prefixEnd_1605400 := by exact prefixLift 1605400
  have htrace : WordTrace (prefixWord ++ tailWord_1605400) baseStart_1605400 baseEnd_1605400 := by
    simpa [prefixWord, tailWord_1605400, baseEnd_1605400] using wordTrace_append hprefix tailTrace_1605400
  have hstable : (prefixWord ++ tailWord_1605400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605400).length < 2 ^ (prefixWord ++ tailWord_1605400).sum := by decide
  have hdescent : baseEnd_1605400 < baseStart_1605400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605402 : List Nat := [3, 1, 1, 3, 2, 3, 2, 1, 6]
def baseStart_1605402 : Nat := 118140960795 + 1605402 * 2 ^ 59
def prefixEnd_1605402 : Nat := 4983230072969 + 3 ^ 40 * 1605402 * 2
def baseEnd_1605402 : Nat := 183187304375429575775977

theorem tailTrace_1605402 : CollatzResearch.WordTrace tailWord_1605402 prefixEnd_1605402 183187304375429575775977 := by
  unfold tailWord_1605402
  simp only [CollatzResearch.WordTrace]
  refine ⟨14638455332477552419514615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39035880886606806452038973 14638455332477552419514615)
  ·
    refine ⟨21957682998716328629271923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14638455332477552419514615 21957682998716328629271923)
    ·
      refine ⟨32936524498074492943907885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21957682998716328629271923 32936524498074492943907885)
      ·
        refine ⟨12351196686777934853965457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32936524498074492943907885 12351196686777934853965457)
        ·
          refine ⟨9263397515083451140474093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12351196686777934853965457 9263397515083451140474093)
          ·
            refine ⟨3473774068156294177677785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9263397515083451140474093 3473774068156294177677785)
            ·
              refine ⟨2605330551117220633258339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3473774068156294177677785 2605330551117220633258339)
              ·
                refine ⟨3907995826675830949887509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2605330551117220633258339 3907995826675830949887509)
                ·
                  refine ⟨183187304375429575775977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3907995826675830949887509 183187304375429575775977)
                  ·
                    rfl

theorem cell22_1605402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_1605402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605402 prefixEnd_1605402 := by exact prefixLift 1605402
  have htrace : WordTrace (prefixWord ++ tailWord_1605402) baseStart_1605402 baseEnd_1605402 := by
    simpa [prefixWord, tailWord_1605402, baseEnd_1605402] using wordTrace_append hprefix tailTrace_1605402
  have hstable : (prefixWord ++ tailWord_1605402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605402).length < 2 ^ (prefixWord ++ tailWord_1605402).sum := by decide
  have hdescent : baseEnd_1605402 < baseStart_1605402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605453 : List Nat := [1, 6, 1, 2, 1, 2, 3, 2, 4]
def baseStart_1605453 : Nat := 118140960795 + 1605453 * 2 ^ 59
def prefixEnd_1605453 : Nat := 4983230072969 + 3 ^ 40 * 1605453 * 2
def baseEnd_1605453 : Nat := 183193123822847198100925

theorem tailTrace_1605453 : CollatzResearch.WordTrace tailWord_1605453 prefixEnd_1605453 183193123822847198100925 := by
  unfold tailWord_1605453
  simp only [CollatzResearch.WordTrace]
  refine ⟨58555681452725445388165013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39037120968483630258776675 58555681452725445388165013)
  ·
    refine ⟨2744797568096505252570235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58555681452725445388165013 2744797568096505252570235)
    ·
      refine ⟨4117196352144757878855353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2744797568096505252570235 4117196352144757878855353)
      ·
        refine ⟨3087897264108568409141515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4117196352144757878855353 3087897264108568409141515)
        ·
          refine ⟨4631845896162852613712273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3087897264108568409141515 4631845896162852613712273)
          ·
            refine ⟨3473884422122139460284205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4631845896162852613712273 3473884422122139460284205)
            ·
              refine ⟨1302706658295802297606577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3473884422122139460284205 1302706658295802297606577)
              ·
                refine ⟨977029993721851723204933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1302706658295802297606577 977029993721851723204933)
                ·
                  refine ⟨183193123822847198100925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 977029993721851723204933 183193123822847198100925)
                  ·
                    rfl

theorem cell22_1605453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_1605453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605453 prefixEnd_1605453 := by exact prefixLift 1605453
  have htrace : WordTrace (prefixWord ++ tailWord_1605453) baseStart_1605453 baseEnd_1605453 := by
    simpa [prefixWord, tailWord_1605453, baseEnd_1605453] using wordTrace_append hprefix tailTrace_1605453
  have hstable : (prefixWord ++ tailWord_1605453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605453).length < 2 ^ (prefixWord ++ tailWord_1605453).sum := by decide
  have hdescent : baseEnd_1605453 < baseStart_1605453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605524 : List Nat := [2, 4, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1605524 : Nat := 118140960795 + 1605524 * 2 ^ 59
def prefixEnd_1605524 : Nat := 4983230072969 + 3 ^ 40 * 1605524 * 2
def baseEnd_1605524 : Nat := 549603676219521075777557

theorem tailTrace_1605524 : CollatzResearch.WordTrace tailWord_1605524 prefixEnd_1605524 549603676219521075777557 := by
  unfold tailWord_1605524
  simp only [CollatzResearch.WordTrace]
  refine ⟨29279135517734112256999813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39038847356978816342666417 29279135517734112256999813)
  ·
    refine ⟨5489837909575146048187465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29279135517734112256999813 5489837909575146048187465)
    ·
      refine ⟨4117378432181359536140599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5489837909575146048187465 4117378432181359536140599)
      ·
        refine ⟨6176067648272039304210899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4117378432181359536140599 6176067648272039304210899)
        ·
          refine ⟨9264101472408058956316349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6176067648272039304210899 9264101472408058956316349)
          ·
            refine ⟨3474038052153022108618631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9264101472408058956316349 3474038052153022108618631)
            ·
              refine ⟨5211057078229533162927947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3474038052153022108618631 5211057078229533162927947)
              ·
                refine ⟨7816585617344299744391921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5211057078229533162927947 7816585617344299744391921)
                ·
                  refine ⟨5862439213008224808293941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7816585617344299744391921 5862439213008224808293941)
                  ·
                    refine ⟨549603676219521075777557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5862439213008224808293941 549603676219521075777557)
                    ·
                      rfl

theorem cell22_1605524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1605524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605524 prefixEnd_1605524 := by exact prefixLift 1605524
  have htrace : WordTrace (prefixWord ++ tailWord_1605524) baseStart_1605524 baseEnd_1605524 := by
    simpa [prefixWord, tailWord_1605524, baseEnd_1605524] using wordTrace_append hprefix tailTrace_1605524
  have hstable : (prefixWord ++ tailWord_1605524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605524).length < 2 ^ (prefixWord ++ tailWord_1605524).sum := by decide
  have hdescent : baseEnd_1605524 < baseStart_1605524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605567 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 4, 4]
def baseStart_1605567 : Nat := 118140960795 + 1605567 * 2 ^ 59
def prefixEnd_1605567 : Nat := 4983230072969 + 3 ^ 40 * 1605567 * 2
def baseEnd_1605567 : Nat := 549618395998283296952425

theorem tailTrace_1605567 : CollatzResearch.WordTrace tailWord_1605567 prefixEnd_1605567 549618395998283296952425 := by
  unfold tailWord_1605567
  simp only [CollatzResearch.WordTrace]
  refine ⟨58559839374312442857814955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39039892916208295238543303 58559839374312442857814955)
  ·
    refine ⟨87839759061468664286722433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58559839374312442857814955 87839759061468664286722433)
    ·
      refine ⟨65879819296101498215041825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87839759061468664286722433 65879819296101498215041825)
      ·
        refine ⟨49409864472076123661281369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65879819296101498215041825 49409864472076123661281369)
        ·
          refine ⟨37057398354057092745961027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49409864472076123661281369 37057398354057092745961027)
          ·
            refine ⟨55586097531085639118941541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37057398354057092745961027 55586097531085639118941541)
            ·
              refine ⟨10422393287078557334801539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55586097531085639118941541 10422393287078557334801539)
              ·
                refine ⟨15633589930617836002202309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10422393287078557334801539 15633589930617836002202309)
                ·
                  refine ⟨2931298111990844250412933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15633589930617836002202309 2931298111990844250412933)
                  ·
                    refine ⟨549618395998283296952425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2931298111990844250412933 549618395998283296952425)
                    ·
                      rfl

theorem cell22_1605567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_1605567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605567 prefixEnd_1605567 := by exact prefixLift 1605567
  have htrace : WordTrace (prefixWord ++ tailWord_1605567) baseStart_1605567 baseEnd_1605567 := by
    simpa [prefixWord, tailWord_1605567, baseEnd_1605567] using wordTrace_append hprefix tailTrace_1605567
  have hstable : (prefixWord ++ tailWord_1605567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605567).length < 2 ^ (prefixWord ++ tailWord_1605567).sum := by decide
  have hdescent : baseEnd_1605567 < baseStart_1605567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605582 : List Nat := [4, 1, 1, 1, 2, 2, 2, 9]
def baseStart_1605582 : Nat := 118140960795 + 1605582 * 2 ^ 59
def prefixEnd_1605582 : Nat := 4983230072969 + 3 ^ 40 * 1605582 * 2
def baseEnd_1605582 : Nat := 61069281200536473091931

theorem tailTrace_1605582 : CollatzResearch.WordTrace tailWord_1605582 prefixEnd_1605582 61069281200536473091931 := by
  unfold tailWord_1605582
  simp only [CollatzResearch.WordTrace]
  refine ⟨7320048308657262552451375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39040257646172066946407333 7320048308657262552451375)
  ·
    refine ⟨10980072462985893828677063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7320048308657262552451375 10980072462985893828677063)
    ·
      refine ⟨16470108694478840743015595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10980072462985893828677063 16470108694478840743015595)
      ·
        refine ⟨24705163041718261114523393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16470108694478840743015595 24705163041718261114523393)
        ·
          refine ⟨18528872281288695835892545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24705163041718261114523393 18528872281288695835892545)
          ·
            refine ⟨13896654210966521876919409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18528872281288695835892545 13896654210966521876919409)
            ·
              refine ⟨10422490658224891407689557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13896654210966521876919409 10422490658224891407689557)
              ·
                refine ⟨61069281200536473091931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10422490658224891407689557 61069281200536473091931)
                ·
                  rfl

theorem cell22_1605582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 9].length) (baseStart_1605582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605582 prefixEnd_1605582 := by exact prefixLift 1605582
  have htrace : WordTrace (prefixWord ++ tailWord_1605582) baseStart_1605582 baseEnd_1605582 := by
    simpa [prefixWord, tailWord_1605582, baseEnd_1605582] using wordTrace_append hprefix tailTrace_1605582
  have hstable : (prefixWord ++ tailWord_1605582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605582).length < 2 ^ (prefixWord ++ tailWord_1605582).sum := by decide
  have hdescent : baseEnd_1605582 < baseStart_1605582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605599 : List Nat := [1, 1, 2, 3, 4, 1, 4, 6]
def baseStart_1605599 : Nat := 118140960795 + 1605599 * 2 ^ 59
def prefixEnd_1605599 : Nat := 4983230072969 + 3 ^ 40 * 1605599 * 2
def baseEnd_1605599 : Nat := 61069927805805097794703

theorem tailTrace_1605599 : CollatzResearch.WordTrace tailWord_1605599 prefixEnd_1605599 61069927805805097794703 := by
  unfold tailWord_1605599
  simp only [CollatzResearch.WordTrace]
  refine ⟨58561006510196512322979851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39040671006797674881986567 58561006510196512322979851)
  ·
    refine ⟨87841509765294768484469777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58561006510196512322979851 87841509765294768484469777)
    ·
      refine ⟨65881132323971076363352333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87841509765294768484469777 65881132323971076363352333)
      ·
        refine ⟨24705424621489153636257125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65881132323971076363352333 24705424621489153636257125)
        ·
          refine ⟨4632267116529216306798211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24705424621489153636257125 4632267116529216306798211)
          ·
            refine ⟨6948400674793824460197317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4632267116529216306798211 6948400674793824460197317)
            ·
              refine ⟨1302825126523842086286997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6948400674793824460197317 1302825126523842086286997)
              ·
                refine ⟨61069927805805097794703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1302825126523842086286997 61069927805805097794703)
                ·
                  rfl

theorem cell22_1605599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 6].length) (baseStart_1605599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605599 prefixEnd_1605599 := by exact prefixLift 1605599
  have htrace : WordTrace (prefixWord ++ tailWord_1605599) baseStart_1605599 baseEnd_1605599 := by
    simpa [prefixWord, tailWord_1605599, baseEnd_1605599] using wordTrace_append hprefix tailTrace_1605599
  have hstable : (prefixWord ++ tailWord_1605599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605599).length < 2 ^ (prefixWord ++ tailWord_1605599).sum := by decide
  have hdescent : baseEnd_1605599 < baseStart_1605599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605627 : List Nat := [1, 1, 1, 1, 1, 3, 6, 1, 7]
def baseStart_1605627 : Nat := 118140960795 + 1605627 * 2 ^ 59
def prefixEnd_1605627 : Nat := 4983230072969 + 3 ^ 40 * 1605627 * 2
def baseEnd_1605627 : Nat := 183212978408154380150747

theorem tailTrace_1605627 : CollatzResearch.WordTrace tailWord_1605627 prefixEnd_1605627 183212978408154380150747 := by
  unfold tailWord_1605627
  simp only [CollatzResearch.WordTrace]
  refine ⟨58562027754095073104999135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39041351836063382069999423 58562027754095073104999135)
  ·
    refine ⟨87843041631142609657498703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58562027754095073104999135 87843041631142609657498703)
    ·
      refine ⟨131764562446713914486248055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87843041631142609657498703 131764562446713914486248055)
      ·
        refine ⟨197646843670070871729372083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131764562446713914486248055 197646843670070871729372083)
        ·
          refine ⟨296470265505106307594058125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197646843670070871729372083 296470265505106307594058125)
          ·
            refine ⟨111176349564414865347771797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296470265505106307594058125 111176349564414865347771797)
            ·
              refine ⟨5211391385831946813176803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111176349564414865347771797 5211391385831946813176803)
              ·
                refine ⟨7817087078747920219765205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5211391385831946813176803 7817087078747920219765205)
                ·
                  refine ⟨183212978408154380150747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7817087078747920219765205 183212978408154380150747)
                  ·
                    rfl

theorem cell22_1605627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 1, 7].length) (baseStart_1605627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605627 prefixEnd_1605627 := by exact prefixLift 1605627
  have htrace : WordTrace (prefixWord ++ tailWord_1605627) baseStart_1605627 baseEnd_1605627 := by
    simpa [prefixWord, tailWord_1605627, baseEnd_1605627] using wordTrace_append hprefix tailTrace_1605627
  have hstable : (prefixWord ++ tailWord_1605627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605627).length < 2 ^ (prefixWord ++ tailWord_1605627).sum := by decide
  have hdescent : baseEnd_1605627 < baseStart_1605627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605631 : List Nat := [1, 1, 2, 2, 1, 2, 1, 8, 1, 3]
def baseStart_1605631 : Nat := 118140960795 + 1605631 * 2 ^ 59
def prefixEnd_1605631 : Nat := 4983230072969 + 3 ^ 40 * 1605631 * 2
def baseEnd_1605631 : Nat := 549640304506208463352229

theorem tailTrace_1605631 : CollatzResearch.WordTrace tailWord_1605631 prefixEnd_1605631 549640304506208463352229 := by
  unfold tailWord_1605631
  simp only [CollatzResearch.WordTrace]
  refine ⟨58562173646080581788144747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39041449097387054525429831 58562173646080581788144747)
  ·
    refine ⟨87843260469120872682217121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58562173646080581788144747 87843260469120872682217121)
    ·
      refine ⟨65882445351840654511662841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87843260469120872682217121 65882445351840654511662841)
      ·
        refine ⟨49411834013880490883747131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65882445351840654511662841 49411834013880490883747131)
        ·
          refine ⟨74117751020820736325620697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49411834013880490883747131 74117751020820736325620697)
          ·
            refine ⟨55588313265615552244215523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74117751020820736325620697 55588313265615552244215523)
            ·
              refine ⟨83382469898423328366323285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55588313265615552244215523 83382469898423328366323285)
              ·
                refine ⟨977138319122148379292851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 83382469898423328366323285 977138319122148379292851)
                ·
                  refine ⟨1465707478683222568939277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 977138319122148379292851 1465707478683222568939277)
                  ·
                    refine ⟨549640304506208463352229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1465707478683222568939277 549640304506208463352229)
                    ·
                      rfl

theorem cell22_1605631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 8, 1, 3].length) (baseStart_1605631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605631 prefixEnd_1605631 := by exact prefixLift 1605631
  have htrace : WordTrace (prefixWord ++ tailWord_1605631) baseStart_1605631 baseEnd_1605631 := by
    simpa [prefixWord, tailWord_1605631, baseEnd_1605631] using wordTrace_append hprefix tailTrace_1605631
  have hstable : (prefixWord ++ tailWord_1605631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605631).length < 2 ^ (prefixWord ++ tailWord_1605631).sum := by decide
  have hdescent : baseEnd_1605631 < baseStart_1605631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605644 : List Nat := [2, 2, 1, 2, 3, 1, 3, 3, 5]
def baseStart_1605644 : Nat := 118140960795 + 1605644 * 2 ^ 59
def prefixEnd_1605644 : Nat := 4983230072969 + 3 ^ 40 * 1605644 * 2
def baseEnd_1605644 : Nat := 183214918223960254259063

theorem tailTrace_1605644 : CollatzResearch.WordTrace tailWord_1605644 prefixEnd_1605644 183214918223960254259063 := by
  unfold tailWord_1605644
  simp only [CollatzResearch.WordTrace]
  refine ⟨29281323897516742504183993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39041765196688990005578657 29281323897516742504183993)
  ·
    refine ⟨21960992923137556878137995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29281323897516742504183993 21960992923137556878137995)
    ·
      refine ⟨32941489384706335317206993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21960992923137556878137995 32941489384706335317206993)
      ·
        refine ⟨24706117038529751487905245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32941489384706335317206993 24706117038529751487905245)
        ·
          refine ⟨9264793889448656807964467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24706117038529751487905245 9264793889448656807964467)
          ·
            refine ⟨13897190834172985211946701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9264793889448656807964467 13897190834172985211946701)
            ·
              refine ⟨5211446562814869454480013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13897190834172985211946701 5211446562814869454480013)
              ·
                refine ⟨1954292461055576045430005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5211446562814869454480013 1954292461055576045430005)
                ·
                  refine ⟨183214918223960254259063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1954292461055576045430005 183214918223960254259063)
                  ·
                    rfl

theorem cell22_1605644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_1605644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605644 prefixEnd_1605644 := by exact prefixLift 1605644
  have htrace : WordTrace (prefixWord ++ tailWord_1605644) baseStart_1605644 baseEnd_1605644 := by
    simpa [prefixWord, tailWord_1605644, baseEnd_1605644] using wordTrace_append hprefix tailTrace_1605644
  have hstable : (prefixWord ++ tailWord_1605644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605644).length < 2 ^ (prefixWord ++ tailWord_1605644).sum := by decide
  have hdescent : baseEnd_1605644 < baseStart_1605644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605725 : List Nat := [1, 4, 4, 1, 1, 1, 4, 1, 1, 4]
def baseStart_1605725 : Nat := 118140960795 + 1605725 * 2 ^ 59
def prefixEnd_1605725 : Nat := 4983230072969 + 3 ^ 40 * 1605725 * 2
def baseEnd_1605725 : Nat := 549672482627223551501941

theorem tailTrace_1605725 : CollatzResearch.WordTrace tailWord_1605725 prefixEnd_1605725 549672482627223551501941 := by
  unfold tailWord_1605725
  simp only [CollatzResearch.WordTrace]
  refine ⟨58565602107740035842066629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39043734738493357228044419 58565602107740035842066629)
  ·
    refine ⟨10981050395201256720387493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58565602107740035842066629 10981050395201256720387493)
    ·
      refine ⟨2058946949100235635072655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10981050395201256720387493 2058946949100235635072655)
      ·
        refine ⟨3088420423650353452608983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2058946949100235635072655 3088420423650353452608983)
        ·
          refine ⟨4632630635475530178913475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3088420423650353452608983 4632630635475530178913475)
          ·
            refine ⟨6948945953213295268370213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4632630635475530178913475 6948945953213295268370213)
            ·
              refine ⟨1302927366227492862819415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6948945953213295268370213 1302927366227492862819415)
              ·
                refine ⟨1954391049341239294229123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302927366227492862819415 1954391049341239294229123)
                ·
                  refine ⟨2931586574011858941343685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1954391049341239294229123 2931586574011858941343685)
                  ·
                    refine ⟨549672482627223551501941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2931586574011858941343685 549672482627223551501941)
                    ·
                      rfl

theorem cell22_1605725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_1605725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605725 prefixEnd_1605725 := by exact prefixLift 1605725
  have htrace : WordTrace (prefixWord ++ tailWord_1605725) baseStart_1605725 baseEnd_1605725 := by
    simpa [prefixWord, tailWord_1605725, baseEnd_1605725] using wordTrace_append hprefix tailTrace_1605725
  have hstable : (prefixWord ++ tailWord_1605725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605725).length < 2 ^ (prefixWord ++ tailWord_1605725).sum := by decide
  have hdescent : baseEnd_1605725 < baseStart_1605725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605738 : List Nat := [3, 1, 3, 2, 3, 1, 1, 1, 4, 3]
def baseStart_1605738 : Nat := 118140960795 + 1605738 * 2 ^ 59
def prefixEnd_1605738 : Nat := 4983230072969 + 3 ^ 40 * 1605738 * 2
def baseEnd_1605738 : Nat := 549676932792895850926901

theorem tailTrace_1605738 : CollatzResearch.WordTrace tailWord_1605738 prefixEnd_1605738 549676932792895850926901 := by
  unfold tailWord_1605738
  simp only [CollatzResearch.WordTrace]
  refine ⟨14641519064173234765572467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39044050837795292708193245 14641519064173234765572467)
  ·
    refine ⟨21962278596259852148358701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14641519064173234765572467 21962278596259852148358701)
    ·
      refine ⟨8235854473597444555634513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21962278596259852148358701 8235854473597444555634513)
      ·
        refine ⟨6176890855198083416725885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8235854473597444555634513 6176890855198083416725885)
        ·
          refine ⟨2316334070699281281272207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6176890855198083416725885 2316334070699281281272207)
          ·
            refine ⟨3474501106048921921908311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2316334070699281281272207 3474501106048921921908311)
            ·
              refine ⟨5211751659073382882862467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3474501106048921921908311 5211751659073382882862467)
              ·
                refine ⟨7817627488610074324293701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5211751659073382882862467 7817627488610074324293701)
                ·
                  refine ⟨1465805154114388935805069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7817627488610074324293701 1465805154114388935805069)
                  ·
                    refine ⟨549676932792895850926901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1465805154114388935805069 549676932792895850926901)
                    ·
                      rfl

theorem cell22_1605738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_1605738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605738 prefixEnd_1605738 := by exact prefixLift 1605738
  have htrace : WordTrace (prefixWord ++ tailWord_1605738) baseStart_1605738 baseEnd_1605738 := by
    simpa [prefixWord, tailWord_1605738, baseEnd_1605738] using wordTrace_append hprefix tailTrace_1605738
  have hstable : (prefixWord ++ tailWord_1605738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605738).length < 2 ^ (prefixWord ++ tailWord_1605738).sum := by decide
  have hdescent : baseEnd_1605738 < baseStart_1605738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605768 : List Nat := [2, 1, 3, 4, 1, 3, 2, 6]
def baseStart_1605768 : Nat := 118140960795 + 1605768 * 2 ^ 59
def prefixEnd_1605768 : Nat := 4983230072969 + 3 ^ 40 * 1605768 * 2
def baseEnd_1605768 : Nat := 61076355822887308075201

theorem tailTrace_1605768 : CollatzResearch.WordTrace tailWord_1605768 prefixEnd_1605768 61076355822887308075201 := by
  unfold tailWord_1605768
  simp only [CollatzResearch.WordTrace]
  refine ⟨29283585223292127092940979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39044780297722836123921305 29283585223292127092940979)
  ·
    refine ⟨43925377834938190639411469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29283585223292127092940979 43925377834938190639411469)
    ·
      refine ⟨16472016688101821489779301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43925377834938190639411469 16472016688101821489779301)
      ·
        refine ⟨3088503129019091529333619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16472016688101821489779301 3088503129019091529333619)
        ·
          refine ⟨4632754693528637294000429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3088503129019091529333619 4632754693528637294000429)
          ·
            refine ⟨1737283010073238985250161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4632754693528637294000429 1737283010073238985250161)
            ·
              refine ⟨1302962257554929238937621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1737283010073238985250161 1302962257554929238937621)
              ·
                refine ⟨61076355822887308075201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1302962257554929238937621 61076355822887308075201)
                ·
                  rfl

theorem cell22_1605768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 6].length) (baseStart_1605768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605768 prefixEnd_1605768 := by exact prefixLift 1605768
  have htrace : WordTrace (prefixWord ++ tailWord_1605768) baseStart_1605768 baseEnd_1605768 := by
    simpa [prefixWord, tailWord_1605768, baseEnd_1605768] using wordTrace_append hprefix tailTrace_1605768
  have hstable : (prefixWord ++ tailWord_1605768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605768).length < 2 ^ (prefixWord ++ tailWord_1605768).sum := by decide
  have hdescent : baseEnd_1605768 < baseStart_1605768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605806 : List Nat := [4, 1, 4, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1605806 : Nat := 118140960795 + 1605806 * 2 ^ 59
def prefixEnd_1605806 : Nat := 4983230072969 + 3 ^ 40 * 1605806 * 2
def baseEnd_1605806 : Nat := 549700210582566340226693

theorem tailTrace_1605806 : CollatzResearch.WordTrace tailWord_1605806 prefixEnd_1605806 549700210582566340226693 := by
  unfold tailWord_1605806
  simp only [CollatzResearch.WordTrace]
  refine ⟨7321069552555823334470659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39045704280297724450510181 7321069552555823334470659)
  ·
    refine ⟨10981604328833735001705989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7321069552555823334470659 10981604328833735001705989)
    ·
      refine ⟨2059050811656325312819873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10981604328833735001705989 2059050811656325312819873)
      ·
        refine ⟨1544288108742243984614905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2059050811656325312819873 1544288108742243984614905)
        ·
          refine ⟨1158216081556682988461179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1544288108742243984614905 1158216081556682988461179)
          ·
            refine ⟨1737324122335024482691769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1158216081556682988461179 1737324122335024482691769)
            ·
              refine ⟨1302993091751268362018827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1737324122335024482691769 1302993091751268362018827)
              ·
                refine ⟨1954489637626902543028241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1302993091751268362018827 1954489637626902543028241)
                ·
                  refine ⟨1465867228220176907271181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1954489637626902543028241 1465867228220176907271181)
                  ·
                    refine ⟨549700210582566340226693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1465867228220176907271181 549700210582566340226693)
                    ·
                      rfl

theorem cell22_1605806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1605806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605806 prefixEnd_1605806 := by exact prefixLift 1605806
  have htrace : WordTrace (prefixWord ++ tailWord_1605806) baseStart_1605806 baseEnd_1605806 := by
    simpa [prefixWord, tailWord_1605806, baseEnd_1605806] using wordTrace_append hprefix tailTrace_1605806
  have hstable : (prefixWord ++ tailWord_1605806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605806).length < 2 ^ (prefixWord ++ tailWord_1605806).sum := by decide
  have hdescent : baseEnd_1605806 < baseStart_1605806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605873 : List Nat := [1, 2, 2, 2, 2, 1, 4, 3, 2, 3]
def baseStart_1605873 : Nat := 118140960795 + 1605873 * 2 ^ 59
def prefixEnd_1605873 : Nat := 4983230072969 + 3 ^ 40 * 1605873 * 2
def baseEnd_1605873 : Nat := 549723146051800498801487

theorem tailTrace_1605873 : CollatzResearch.WordTrace tailWord_1605873 prefixEnd_1605873 549723146051800498801487 := by
  unfold tailWord_1605873
  simp only [CollatzResearch.WordTrace]
  refine ⟨58571000111203857118454273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39047333407469238078969515 58571000111203857118454273)
  ·
    refine ⟨43928250083402892838840705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58571000111203857118454273 43928250083402892838840705)
    ·
      refine ⟨32946187562552169629130529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43928250083402892838840705 32946187562552169629130529)
      ·
        refine ⟨24709640671914127221847897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32946187562552169629130529 24709640671914127221847897)
        ·
          refine ⟨18532230503935595416385923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24709640671914127221847897 18532230503935595416385923)
          ·
            refine ⟨27798345755903393124578885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18532230503935595416385923 27798345755903393124578885)
            ·
              refine ⟨5212189829231886210858541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27798345755903393124578885 5212189829231886210858541)
              ·
                refine ⟨1954571185961957329071953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5212189829231886210858541 1954571185961957329071953)
                ·
                  refine ⟨1465928389471467996803965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1954571185961957329071953 1465928389471467996803965)
                  ·
                    refine ⟨549723146051800498801487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1465928389471467996803965 549723146051800498801487)
                    ·
                      rfl

theorem cell22_1605873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_1605873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605873 prefixEnd_1605873 := by exact prefixLift 1605873
  have htrace : WordTrace (prefixWord ++ tailWord_1605873) baseStart_1605873 baseEnd_1605873 := by
    simpa [prefixWord, tailWord_1605873, baseEnd_1605873] using wordTrace_append hprefix tailTrace_1605873
  have hstable : (prefixWord ++ tailWord_1605873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605873).length < 2 ^ (prefixWord ++ tailWord_1605873).sum := by decide
  have hdescent : baseEnd_1605873 < baseStart_1605873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605961 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 5, 4]
def baseStart_1605961 : Nat := 118140960795 + 1605961 * 2 ^ 59
def prefixEnd_1605961 : Nat := 4983230072969 + 3 ^ 40 * 1605961 * 2
def baseEnd_1605961 : Nat := 549753270250197602601217

theorem tailTrace_1605961 : CollatzResearch.WordTrace tailWord_1605961 prefixEnd_1605961 549753270250197602601217 := by
  unfold tailWord_1605961
  simp only [CollatzResearch.WordTrace]
  refine ⟨58574209734885048147657737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39049473156590032098438491 58574209734885048147657737)
  ·
    refine ⟨43930657301163786110743303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58574209734885048147657737 43930657301163786110743303)
    ·
      refine ⟨65895985951745679166114955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43930657301163786110743303 65895985951745679166114955)
      ·
        refine ⟨98843978927618518749172433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65895985951745679166114955 98843978927618518749172433)
        ·
          refine ⟨74132984195713889061879325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98843978927618518749172433 74132984195713889061879325)
          ·
            refine ⟨27799869073392708398204747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74132984195713889061879325 27799869073392708398204747)
            ·
              refine ⟨41699803610089062597307121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27799869073392708398204747 41699803610089062597307121)
              ·
                refine ⟨31274852707566796947980341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41699803610089062597307121 31274852707566796947980341)
                ·
                  refine ⟨2932017441334387213873157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31274852707566796947980341 2932017441334387213873157)
                  ·
                    refine ⟨549753270250197602601217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2932017441334387213873157 549753270250197602601217)
                    ·
                      rfl

theorem cell22_1605961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 4].length) (baseStart_1605961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605961 prefixEnd_1605961 := by exact prefixLift 1605961
  have htrace : WordTrace (prefixWord ++ tailWord_1605961) baseStart_1605961 baseEnd_1605961 := by
    simpa [prefixWord, tailWord_1605961, baseEnd_1605961] using wordTrace_append hprefix tailTrace_1605961
  have hstable : (prefixWord ++ tailWord_1605961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605961).length < 2 ^ (prefixWord ++ tailWord_1605961).sum := by decide
  have hdescent : baseEnd_1605961 < baseStart_1605961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1605976 : List Nat := [2, 1, 2, 2, 1, 1, 2, 5, 6]
def baseStart_1605976 : Nat := 118140960795 + 1605976 * 2 ^ 59
def prefixEnd_1605976 : Nat := 4983230072969 + 3 ^ 40 * 1605976 * 2
def baseEnd_1605976 : Nat := 183252801685580854492057

theorem tailTrace_1605976 : CollatzResearch.WordTrace tailWord_1605976 prefixEnd_1605976 183252801685580854492057 := by
  unfold tailWord_1605976
  simp only [CollatzResearch.WordTrace]
  refine ⟨29287378414915352854726891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39049837886553803806302521 29287378414915352854726891)
  ·
    refine ⟨43931067622373029282090337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29287378414915352854726891 43931067622373029282090337)
    ·
      refine ⟨32948300716779771961567753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43931067622373029282090337 32948300716779771961567753)
      ·
        refine ⟨24711225537584828971175815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32948300716779771961567753 24711225537584828971175815)
        ·
          refine ⟨37066838306377243456763723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24711225537584828971175815 37066838306377243456763723)
          ·
            refine ⟨55600257459565865185145585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37066838306377243456763723 55600257459565865185145585)
            ·
              refine ⟨41700193094674398888859189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55600257459565865185145585 41700193094674398888859189)
              ·
                refine ⟨3909393102625724895830549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41700193094674398888859189 3909393102625724895830549)
                ·
                  refine ⟨183252801685580854492057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3909393102625724895830549 183252801685580854492057)
                  ·
                    rfl

theorem cell22_1605976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 6].length) (baseStart_1605976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1605976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1605976 prefixEnd_1605976 := by exact prefixLift 1605976
  have htrace : WordTrace (prefixWord ++ tailWord_1605976) baseStart_1605976 baseEnd_1605976 := by
    simpa [prefixWord, tailWord_1605976, baseEnd_1605976] using wordTrace_append hprefix tailTrace_1605976
  have hstable : (prefixWord ++ tailWord_1605976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1605976).length < 2 ^ (prefixWord ++ tailWord_1605976).sum := by decide
  have hdescent : baseEnd_1605976 < baseStart_1605976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1605976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606023 : List Nat := [1, 1, 4, 2, 2, 1, 1, 4, 2, 4]
def baseStart_1606023 : Nat := 118140960795 + 1606023 * 2 ^ 59
def prefixEnd_1606023 : Nat := 4983230072969 + 3 ^ 40 * 1606023 * 2
def baseEnd_1606023 : Nat := 549774494117250107551027

theorem tailTrace_1606023 : CollatzResearch.WordTrace tailWord_1606023 prefixEnd_1606023 549774494117250107551027 := by
  unfold tailWord_1606023
  simp only [CollatzResearch.WordTrace]
  refine ⟨58576471060660432736414723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39050980707106955157609815 58576471060660432736414723)
  ·
    refine ⟨87864706590990649104622085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58576471060660432736414723 87864706590990649104622085)
    ·
      refine ⟨16474632485810746707116641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87864706590990649104622085 16474632485810746707116641)
      ·
        refine ⟨12355974364358060030337481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16474632485810746707116641 12355974364358060030337481)
        ·
          refine ⟨9266980773268545022753111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12355974364358060030337481 9266980773268545022753111)
          ·
            refine ⟨13900471159902817534129667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9266980773268545022753111 13900471159902817534129667)
            ·
              refine ⟨20850706739854226301194501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13900471159902817534129667 20850706739854226301194501)
              ·
                refine ⟨3909507513722667431473969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20850706739854226301194501 3909507513722667431473969)
                ·
                  refine ⟨2932130635292000573605477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3909507513722667431473969 2932130635292000573605477)
                  ·
                    refine ⟨549774494117250107551027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2932130635292000573605477 549774494117250107551027)
                    ·
                      rfl

theorem cell22_1606023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_1606023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606023 prefixEnd_1606023 := by exact prefixLift 1606023
  have htrace : WordTrace (prefixWord ++ tailWord_1606023) baseStart_1606023 baseEnd_1606023 := by
    simpa [prefixWord, tailWord_1606023, baseEnd_1606023] using wordTrace_append hprefix tailTrace_1606023
  have hstable : (prefixWord ++ tailWord_1606023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606023).length < 2 ^ (prefixWord ++ tailWord_1606023).sum := by decide
  have hdescent : baseEnd_1606023 < baseStart_1606023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606025 : List Nat := [1, 2, 1, 1, 6, 1, 1, 4, 2, 3]
def baseStart_1606025 : Nat := 118140960795 + 1606025 * 2 ^ 59
def prefixEnd_1606025 : Nat := 4983230072969 + 3 ^ 40 * 1606025 * 2
def baseEnd_1606025 : Nat := 549775178758122769001021

theorem tailTrace_1606025 : CollatzResearch.WordTrace tailWord_1606025 prefixEnd_1606025 549775178758122769001021 := by
  unfold tailWord_1606025
  simp only [CollatzResearch.WordTrace]
  refine ⟨58576544006653187077987529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39051029337768791385325019 58576544006653187077987529)
  ·
    refine ⟨43932408004989890308490647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58576544006653187077987529 43932408004989890308490647)
    ·
      refine ⟨65898612007484835462735971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43932408004989890308490647 65898612007484835462735971)
      ·
        refine ⟨98847918011227253194103957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65898612007484835462735971 98847918011227253194103957)
        ·
          refine ⟨4633496156776277493473623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98847918011227253194103957 4633496156776277493473623)
          ·
            refine ⟨6950244235164416240210435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4633496156776277493473623 6950244235164416240210435)
            ·
              refine ⟨10425366352746624360315653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6950244235164416240210435 10425366352746624360315653)
              ·
                refine ⟨1954756191139992067559185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10425366352746624360315653 1954756191139992067559185)
                ·
                  refine ⟨1466067143354994050669389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1954756191139992067559185 1466067143354994050669389)
                  ·
                    refine ⟨549775178758122769001021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1466067143354994050669389 549775178758122769001021)
                    ·
                      rfl

theorem cell22_1606025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 3].length) (baseStart_1606025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606025 prefixEnd_1606025 := by exact prefixLift 1606025
  have htrace : WordTrace (prefixWord ++ tailWord_1606025) baseStart_1606025 baseEnd_1606025 := by
    simpa [prefixWord, tailWord_1606025, baseEnd_1606025] using wordTrace_append hprefix tailTrace_1606025
  have hstable : (prefixWord ++ tailWord_1606025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606025).length < 2 ^ (prefixWord ++ tailWord_1606025).sum := by decide
  have hdescent : baseEnd_1606025 < baseStart_1606025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606027 : List Nat := [1, 1, 1, 1, 4, 6, 2, 2, 4]
def baseStart_1606027 : Nat := 118140960795 + 1606027 * 2 ^ 59
def prefixEnd_1606027 : Nat := 4983230072969 + 3 ^ 40 * 1606027 * 2
def baseEnd_1606027 : Nat := 183258621132998476817005

theorem tailTrace_1606027 : CollatzResearch.WordTrace tailWord_1606027 prefixEnd_1606027 183258621132998476817005 := by
  unfold tailWord_1606027
  simp only [CollatzResearch.WordTrace]
  refine ⟨58576616952645941419560335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39051077968430627613040223 58576616952645941419560335)
  ·
    refine ⟨87864925428968912129340503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58576616952645941419560335 87864925428968912129340503)
    ·
      refine ⟨131797388143453368194010755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87864925428968912129340503 131797388143453368194010755)
      ·
        refine ⟨197696082215180052291016133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131797388143453368194010755 197696082215180052291016133)
        ·
          refine ⟨37068015415346259804565525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197696082215180052291016133 37068015415346259804565525)
          ·
            refine ⟨1737563222594355928339009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37068015415346259804565525 1737563222594355928339009)
            ·
              refine ⟨1303172416945766946254257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1737563222594355928339009 1303172416945766946254257)
              ·
                refine ⟨977379312709325209690693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1303172416945766946254257 977379312709325209690693)
                ·
                  refine ⟨183258621132998476817005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 977379312709325209690693 183258621132998476817005)
                  ·
                    rfl

theorem cell22_1606027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 2, 4].length) (baseStart_1606027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606027 prefixEnd_1606027 := by exact prefixLift 1606027
  have htrace : WordTrace (prefixWord ++ tailWord_1606027) baseStart_1606027 baseEnd_1606027 := by
    simpa [prefixWord, tailWord_1606027, baseEnd_1606027] using wordTrace_append hprefix tailTrace_1606027
  have hstable : (prefixWord ++ tailWord_1606027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606027).length < 2 ^ (prefixWord ++ tailWord_1606027).sum := by decide
  have hdescent : baseEnd_1606027 < baseStart_1606027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606055 : List Nat := [1, 1, 6, 1, 1, 3, 3, 6]
def baseStart_1606055 : Nat := 118140960795 + 1606055 * 2 ^ 59
def prefixEnd_1606055 : Nat := 4983230072969 + 3 ^ 40 * 1606055 * 2
def baseEnd_1606055 : Nat := 61087272041245854527881

theorem tailTrace_1606055 : CollatzResearch.WordTrace tailWord_1606055 prefixEnd_1606055 61087272041245854527881 := by
  unfold tailWord_1606055
  simp only [CollatzResearch.WordTrace]
  refine ⟨58577638196544502201579619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39051758797696334801053079 58577638196544502201579619)
  ·
    refine ⟨87866457294816753302369429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58577638196544502201579619 87866457294816753302369429)
    ·
      refine ⟨4118740185694535311048567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87866457294816753302369429 4118740185694535311048567)
      ·
        refine ⟨6178110278541802966572851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4118740185694535311048567 6178110278541802966572851)
        ·
          refine ⟨9267165417812704449859277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6178110278541802966572851 9267165417812704449859277)
          ·
            refine ⟨3475187031679764168697229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9267165417812704449859277 3475187031679764168697229)
            ·
              refine ⟨1303195136879911563261461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3475187031679764168697229 1303195136879911563261461)
              ·
                refine ⟨61087272041245854527881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1303195136879911563261461 61087272041245854527881)
                ·
                  rfl

theorem cell22_1606055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 6].length) (baseStart_1606055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606055 prefixEnd_1606055 := by exact prefixLift 1606055
  have htrace : WordTrace (prefixWord ++ tailWord_1606055) baseStart_1606055 baseEnd_1606055 := by
    simpa [prefixWord, tailWord_1606055, baseEnd_1606055] using wordTrace_append hprefix tailTrace_1606055
  have hstable : (prefixWord ++ tailWord_1606055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606055).length < 2 ^ (prefixWord ++ tailWord_1606055).sum := by decide
  have hdescent : baseEnd_1606055 < baseStart_1606055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606087 : List Nat := [1, 1, 4, 1, 1, 4, 2, 4, 1, 3]
def baseStart_1606087 : Nat := 118140960795 + 1606087 * 2 ^ 59
def prefixEnd_1606087 : Nat := 4983230072969 + 3 ^ 40 * 1606087 * 2
def baseEnd_1606087 : Nat := 549796402625175273950831

theorem tailTrace_1606087 : CollatzResearch.WordTrace tailWord_1606087 prefixEnd_1606087 549796402625175273950831 := by
  unfold tailWord_1606087
  simp only [CollatzResearch.WordTrace]
  refine ⟨58578805332428571666744515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39052536888285714444496343 58578805332428571666744515)
  ·
    refine ⟨87868207998642857500116773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58578805332428571666744515 87868207998642857500116773)
    ·
      refine ⟨16475288999745535781271895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87868207998642857500116773 16475288999745535781271895)
      ·
        refine ⟨24712933499618303671907843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16475288999745535781271895 24712933499618303671907843)
        ·
          refine ⟨37069400249427455507861765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24712933499618303671907843 37069400249427455507861765)
          ·
            refine ⟨6950512546767647907724081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37069400249427455507861765 6950512546767647907724081)
            ·
              refine ⟨5212884410075735930793061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6950512546767647907724081 5212884410075735930793061)
              ·
                refine ⟨977415826889200487023699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5212884410075735930793061 977415826889200487023699)
                ·
                  refine ⟨1466123740333800730535549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 977415826889200487023699 1466123740333800730535549)
                  ·
                    refine ⟨549796402625175273950831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1466123740333800730535549 549796402625175273950831)
                    ·
                      rfl

theorem cell22_1606087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_1606087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606087 prefixEnd_1606087 := by exact prefixLift 1606087
  have htrace : WordTrace (prefixWord ++ tailWord_1606087) baseStart_1606087 baseEnd_1606087 := by
    simpa [prefixWord, tailWord_1606087, baseEnd_1606087] using wordTrace_append hprefix tailTrace_1606087
  have hstable : (prefixWord ++ tailWord_1606087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606087).length < 2 ^ (prefixWord ++ tailWord_1606087).sum := by decide
  have hdescent : baseEnd_1606087 < baseStart_1606087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606145 : List Nat := [1, 2, 4, 1, 3, 1, 3, 1, 6]
def baseStart_1606145 : Nat := 118140960795 + 1606145 * 2 ^ 59
def prefixEnd_1606145 : Nat := 4983230072969 + 3 ^ 40 * 1606145 * 2
def baseEnd_1606145 : Nat := 183272085736827485333551

theorem tailTrace_1606145 : CollatzResearch.WordTrace tailWord_1606145 prefixEnd_1606145 183272085736827485333551 := by
  unfold tailWord_1606145
  simp only [CollatzResearch.WordTrace]
  refine ⟨58580920766218447572355889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39053947177478965048237259 58580920766218447572355889)
  ·
    refine ⟨43935690574663835679266917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58580920766218447572355889 43935690574663835679266917)
    ·
      refine ⟨8237941982749469189862547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43935690574663835679266917 8237941982749469189862547)
      ·
        refine ⟨12356912974124203784793821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8237941982749469189862547 12356912974124203784793821)
        ·
          refine ⟨4633842365296576419297683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12356912974124203784793821 4633842365296576419297683)
          ·
            refine ⟨6950763547944864628946525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4633842365296576419297683 6950763547944864628946525)
            ·
              refine ⟨2606536330479324235854947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6950763547944864628946525 2606536330479324235854947)
              ·
                refine ⟨3909804495718986353782421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2606536330479324235854947 3909804495718986353782421)
                ·
                  refine ⟨183272085736827485333551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3909804495718986353782421 183272085736827485333551)
                  ·
                    rfl

theorem cell22_1606145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 6].length) (baseStart_1606145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606145 prefixEnd_1606145 := by exact prefixLift 1606145
  have htrace : WordTrace (prefixWord ++ tailWord_1606145) baseStart_1606145 baseEnd_1606145 := by
    simpa [prefixWord, tailWord_1606145, baseEnd_1606145] using wordTrace_append hprefix tailTrace_1606145
  have hstable : (prefixWord ++ tailWord_1606145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606145).length < 2 ^ (prefixWord ++ tailWord_1606145).sum := by decide
  have hdescent : baseEnd_1606145 < baseStart_1606145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606164 : List Nat := [2, 4, 3, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1606164 : Nat := 118140960795 + 1606164 * 2 ^ 59
def prefixEnd_1606164 : Nat := 4983230072969 + 3 ^ 40 * 1606164 * 2
def baseEnd_1606164 : Nat := 549822761298772739775595

theorem tailTrace_1606164 : CollatzResearch.WordTrace tailWord_1606164 prefixEnd_1606164 549822761298772739775595 := by
  unfold tailWord_1606164
  simp only [CollatzResearch.WordTrace]
  refine ⟨29290806876574806908648773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39054409168766409211531697 29290806876574806908648773)
  ·
    refine ⟨5492026289357776295371645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29290806876574806908648773 5492026289357776295371645)
    ·
      refine ⟨2059509858509166110764367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5492026289357776295371645 2059509858509166110764367)
      ·
        refine ⟨3089264787763749166146551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2059509858509166110764367 3089264787763749166146551)
        ·
          refine ⟨4633897181645623749219827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3089264787763749166146551 4633897181645623749219827)
          ·
            refine ⟨6950845772468435623829741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4633897181645623749219827 6950845772468435623829741)
            ·
              refine ⟨2606567164675663358936153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6950845772468435623829741 2606567164675663358936153)
              ·
                refine ⟨1954925373506747519202115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2606567164675663358936153 1954925373506747519202115)
                ·
                  refine ⟨2932388060260121278803173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1954925373506747519202115 2932388060260121278803173)
                  ·
                    refine ⟨549822761298772739775595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2932388060260121278803173 549822761298772739775595)
                    ·
                      rfl

theorem cell22_1606164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1606164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606164 prefixEnd_1606164 := by exact prefixLift 1606164
  have htrace : WordTrace (prefixWord ++ tailWord_1606164) baseStart_1606164 baseEnd_1606164 := by
    simpa [prefixWord, tailWord_1606164, baseEnd_1606164] using wordTrace_append hprefix tailTrace_1606164
  have hstable : (prefixWord ++ tailWord_1606164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606164).length < 2 ^ (prefixWord ++ tailWord_1606164).sum := by decide
  have hdescent : baseEnd_1606164 < baseStart_1606164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606190 : List Nat := [4, 1, 3, 1, 3, 10]
def baseStart_1606190 : Nat := 118140960795 + 1606190 * 2 ^ 59
def prefixEnd_1606190 : Nat := 4983230072969 + 3 ^ 40 * 1606190 * 2
def baseEnd_1606190 : Nat := 6788045205310090600315

theorem tailTrace_1606190 : CollatzResearch.WordTrace tailWord_1606190 prefixEnd_1606190 6788045205310090600315 := by
  unfold tailWord_1606190
  simp only [CollatzResearch.WordTrace]
  refine ⟨7322820256381927532218003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 39055041367370280171829349 7322820256381927532218003)
  ·
    refine ⟨10984230384572891298327005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7322820256381927532218003 10984230384572891298327005)
    ·
      refine ⟨4119086394214834236872627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10984230384572891298327005 4119086394214834236872627)
      ·
        refine ⟨6178629591322251355308941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4119086394214834236872627 6178629591322251355308941)
        ·
          refine ⟨2316986096745844258240853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6178629591322251355308941 2316986096745844258240853)
          ·
            refine ⟨6788045205310090600315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2316986096745844258240853 6788045205310090600315)
            ·
              rfl

theorem cell22_1606190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 10].length) (baseStart_1606190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606190 prefixEnd_1606190 := by exact prefixLift 1606190
  have htrace : WordTrace (prefixWord ++ tailWord_1606190) baseStart_1606190 baseEnd_1606190 := by
    simpa [prefixWord, tailWord_1606190, baseEnd_1606190] using wordTrace_append hprefix tailTrace_1606190
  have hstable : (prefixWord ++ tailWord_1606190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606190).length < 2 ^ (prefixWord ++ tailWord_1606190).sum := by decide
  have hdescent : baseEnd_1606190 < baseStart_1606190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606196 : List Nat := [2, 5, 1, 3, 1, 1, 1, 4, 4]
def baseStart_1606196 : Nat := 118140960795 + 1606196 * 2 ^ 59
def prefixEnd_1606196 : Nat := 4983230072969 + 3 ^ 40 * 1606196 * 2
def baseEnd_1606196 : Nat := 183277905184245107658499

theorem tailTrace_1606196 : CollatzResearch.WordTrace tailWord_1606196 prefixEnd_1606196 183277905184245107658499 := by
  unfold tailWord_1606196
  simp only [CollatzResearch.WordTrace]
  refine ⟨29291390444516841641231221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39055187259355788854974961 29291390444516841641231221)
  ·
    refine ⟨2746067854173453903865427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29291390444516841641231221 2746067854173453903865427)
    ·
      refine ⟨4119101781260180855798141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2746067854173453903865427 4119101781260180855798141)
      ·
        refine ⟨1544663167972567820924303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4119101781260180855798141 1544663167972567820924303)
        ·
          refine ⟨2316994751958851731386455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1544663167972567820924303 2316994751958851731386455)
          ·
            refine ⟨3475492127938277597079683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2316994751958851731386455 3475492127938277597079683)
            ·
              refine ⟨5213238191907416395619525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3475492127938277597079683 5213238191907416395619525)
              ·
                refine ⟨977482160982640574178661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5213238191907416395619525 977482160982640574178661)
                ·
                  refine ⟨183277905184245107658499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 977482160982640574178661 183277905184245107658499)
                  ·
                    rfl

theorem cell22_1606196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_1606196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606196 prefixEnd_1606196 := by exact prefixLift 1606196
  have htrace : WordTrace (prefixWord ++ tailWord_1606196) baseStart_1606196 baseEnd_1606196 := by
    simpa [prefixWord, tailWord_1606196, baseEnd_1606196] using wordTrace_append hprefix tailTrace_1606196
  have hstable : (prefixWord ++ tailWord_1606196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606196).length < 2 ^ (prefixWord ++ tailWord_1606196).sum := by decide
  have hdescent : baseEnd_1606196 < baseStart_1606196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606250 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 4, 5]
def baseStart_1606250 : Nat := 118140960795 + 1606250 * 2 ^ 59
def prefixEnd_1606250 : Nat := 4983230072969 + 3 ^ 40 * 1606250 * 2
def baseEnd_1606250 : Nat := 549852200856297182125331

theorem tailTrace_1606250 : CollatzResearch.WordTrace tailWord_1606250 prefixEnd_1606250 549852200856297182125331 := by
  unfold tailWord_1606250
  simp only [CollatzResearch.WordTrace]
  refine ⟨14646187607709512626232051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 39056500287225367003285469 14646187607709512626232051)
  ·
    refine ⟨21969281411564268939348077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14646187607709512626232051 21969281411564268939348077)
    ·
      refine ⟨8238480529336600852255529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21969281411564268939348077 8238480529336600852255529)
      ·
        refine ⟨6178860397002450639191647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8238480529336600852255529 6178860397002450639191647)
        ·
          refine ⟨9268290595503675958787471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6178860397002450639191647 9268290595503675958787471)
          ·
            refine ⟨13902435893255513938181207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9268290595503675958787471 13902435893255513938181207)
            ·
              refine ⟨20853653839883270907271811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13902435893255513938181207 20853653839883270907271811)
              ·
                refine ⟨31280480759824906360907717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20853653839883270907271811 31280480759824906360907717)
                ·
                  refine ⟨5865090142467169942670197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31280480759824906360907717 5865090142467169942670197)
                  ·
                    refine ⟨549852200856297182125331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5865090142467169942670197 549852200856297182125331)
                    ·
                      rfl

theorem cell22_1606250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_1606250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606250 prefixEnd_1606250 := by exact prefixLift 1606250
  have htrace : WordTrace (prefixWord ++ tailWord_1606250) baseStart_1606250 baseEnd_1606250 := by
    simpa [prefixWord, tailWord_1606250, baseEnd_1606250] using wordTrace_append hprefix tailTrace_1606250
  have hstable : (prefixWord ++ tailWord_1606250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606250).length < 2 ^ (prefixWord ++ tailWord_1606250).sum := by decide
  have hdescent : baseEnd_1606250 < baseStart_1606250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606269 : List Nat := [1, 4, 1, 1, 5, 1, 3, 1, 5]
def baseStart_1606269 : Nat := 118140960795 + 1606269 * 2 ^ 59
def prefixEnd_1606269 : Nat := 4983230072969 + 3 ^ 40 * 1606269 * 2
def baseEnd_1606269 : Nat := 183286234981529155300091

theorem tailTrace_1606269 : CollatzResearch.WordTrace tailWord_1606269 prefixEnd_1606269 183286234981529155300091 := by
  unfold tailWord_1606269
  simp only [CollatzResearch.WordTrace]
  refine ⟨58585443417769216749869861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39056962278512811166579907 58585443417769216749869861)
  ·
    refine ⟨10984770640831728140600599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58585443417769216749869861 10984770640831728140600599)
    ·
      refine ⟨16477155961247592210900899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10984770640831728140600599 16477155961247592210900899)
      ·
        refine ⟨24715733941871388316351349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16477155961247592210900899 24715733941871388316351349)
        ·
          refine ⟨2317100057050442654657939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24715733941871388316351349 2317100057050442654657939)
          ·
            refine ⟨3475650085575663981986909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2317100057050442654657939 3475650085575663981986909)
            ·
              refine ⟨1303368782090873993245091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3475650085575663981986909 1303368782090873993245091)
              ·
                refine ⟨1955053173136310989867637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303368782090873993245091 1955053173136310989867637)
                ·
                  refine ⟨183286234981529155300091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1955053173136310989867637 183286234981529155300091)
                  ·
                    rfl

theorem cell22_1606269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 3, 1, 5].length) (baseStart_1606269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606269 prefixEnd_1606269 := by exact prefixLift 1606269
  have htrace : WordTrace (prefixWord ++ tailWord_1606269) baseStart_1606269 baseEnd_1606269 := by
    simpa [prefixWord, tailWord_1606269, baseEnd_1606269] using wordTrace_append hprefix tailTrace_1606269
  have hstable : (prefixWord ++ tailWord_1606269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606269).length < 2 ^ (prefixWord ++ tailWord_1606269).sum := by decide
  have hdescent : baseEnd_1606269 < baseStart_1606269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606295 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 3, 5]
def baseStart_1606295 : Nat := 118140960795 + 1606295 * 2 ^ 59
def prefixEnd_1606295 : Nat := 4983230072969 + 3 ^ 40 * 1606295 * 2
def baseEnd_1606295 : Nat := 549867605275932064750193

theorem tailTrace_1606295 : CollatzResearch.WordTrace tailWord_1606295 prefixEnd_1606295 549867605275932064750193 := by
  unfold tailWord_1606295
  simp only [CollatzResearch.WordTrace]
  refine ⟨58586391715675023190316339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39057594477116682126877559 58586391715675023190316339)
  ·
    refine ⟨87879587573512534785474509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58586391715675023190316339 87879587573512534785474509)
    ·
      refine ⟨32954845340067200544552941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87879587573512534785474509 32954845340067200544552941)
      ·
        refine ⟨12358067002525200204207353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32954845340067200544552941 12358067002525200204207353)
        ·
          refine ⟨9268550251893900153155515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12358067002525200204207353 9268550251893900153155515)
          ·
            refine ⟨13902825377840850229733273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9268550251893900153155515 13902825377840850229733273)
            ·
              refine ⟨10427119033380637672299955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13902825377840850229733273 10427119033380637672299955)
              ·
                refine ⟨15640678550070956508449933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10427119033380637672299955 15640678550070956508449933)
                ·
                  refine ⟨5865254456276608690668725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15640678550070956508449933 5865254456276608690668725)
                  ·
                    refine ⟨549867605275932064750193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5865254456276608690668725 549867605275932064750193)
                    ·
                      rfl

theorem cell22_1606295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_1606295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606295 prefixEnd_1606295 := by exact prefixLift 1606295
  have htrace : WordTrace (prefixWord ++ tailWord_1606295) baseStart_1606295 baseEnd_1606295 := by
    simpa [prefixWord, tailWord_1606295, baseEnd_1606295] using wordTrace_append hprefix tailTrace_1606295
  have hstable : (prefixWord ++ tailWord_1606295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606295).length < 2 ^ (prefixWord ++ tailWord_1606295).sum := by decide
  have hdescent : baseEnd_1606295 < baseStart_1606295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606415 : List Nat := [1, 1, 2, 1, 1, 1, 5, 2, 8]
def baseStart_1606415 : Nat := 118140960795 + 1606415 * 2 ^ 59
def prefixEnd_1606415 : Nat := 4983230072969 + 3 ^ 40 * 1606415 * 2
def baseEnd_1606415 : Nat := 183302894576097250583275

theorem tailTrace_1606415 : CollatzResearch.WordTrace tailWord_1606415 prefixEnd_1606415 183302894576097250583275 := by
  unfold tailWord_1606415
  simp only [CollatzResearch.WordTrace]
  refine ⟨58590768475240283684684699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 39060512316826855789789799 58590768475240283684684699)
  ·
    refine ⟨87886152712860425527027049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58590768475240283684684699 87886152712860425527027049)
    ·
      refine ⟨65914614534645319145270287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87886152712860425527027049 65914614534645319145270287)
      ·
        refine ⟨98871921801967978717905431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65914614534645319145270287 98871921801967978717905431)
        ·
          refine ⟨148307882702951968076858147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98871921801967978717905431 148307882702951968076858147)
          ·
            refine ⟨222461824054427952115287221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148307882702951968076858147 222461824054427952115287221)
            ·
              refine ⟨20855796005102620510808177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 222461824054427952115287221 20855796005102620510808177)
              ·
                refine ⟨15641847003826965383106133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20855796005102620510808177 15641847003826965383106133)
                ·
                  refine ⟨183302894576097250583275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15641847003826965383106133 183302894576097250583275)
                  ·
                    rfl

theorem cell22_1606415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 8].length) (baseStart_1606415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606415 prefixEnd_1606415 := by exact prefixLift 1606415
  have htrace : WordTrace (prefixWord ++ tailWord_1606415) baseStart_1606415 baseEnd_1606415 := by
    simpa [prefixWord, tailWord_1606415, baseEnd_1606415] using wordTrace_append hprefix tailTrace_1606415
  have hstable : (prefixWord ++ tailWord_1606415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606415).length < 2 ^ (prefixWord ++ tailWord_1606415).sum := by decide
  have hdescent : baseEnd_1606415 < baseStart_1606415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1606432 : List Nat := [2, 1, 1, 5, 1, 2, 1, 3, 6]
def baseStart_1606432 : Nat := 118140960795 + 1606432 * 2 ^ 59
def prefixEnd_1606432 : Nat := 4983230072969 + 3 ^ 40 * 1606432 * 2
def baseEnd_1606432 : Nat := 183304834391903124691591

theorem tailTrace_1606432 : CollatzResearch.WordTrace tailWord_1606432 prefixEnd_1606432 183304834391903124691591 := by
  unfold tailWord_1606432
  simp only [CollatzResearch.WordTrace]
  refine ⟨29295694258089347794026775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 39060925677452463725369033 29295694258089347794026775)
  ·
    refine ⟨43943541387134021691040163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29295694258089347794026775 43943541387134021691040163)
    ·
      refine ⟨65915312080701032536560245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43943541387134021691040163 65915312080701032536560245)
      ·
        refine ⟨6179560507565721800302523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65915312080701032536560245 6179560507565721800302523)
        ·
          refine ⟨9269340761348582700453785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6179560507565721800302523 9269340761348582700453785)
          ·
            refine ⟨6952005571011437025340339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9269340761348582700453785 6952005571011437025340339)
            ·
              refine ⟨10428008356517155538010509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6952005571011437025340339 10428008356517155538010509)
              ·
                refine ⟨3910503133693933326753941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10428008356517155538010509 3910503133693933326753941)
                ·
                  refine ⟨183304834391903124691591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3910503133693933326753941 183304834391903124691591)
                  ·
                    rfl

theorem cell22_1606432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 3, 6].length) (baseStart_1606432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1606432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1606432 prefixEnd_1606432 := by exact prefixLift 1606432
  have htrace : WordTrace (prefixWord ++ tailWord_1606432) baseStart_1606432 baseEnd_1606432 := by
    simpa [prefixWord, tailWord_1606432, baseEnd_1606432] using wordTrace_append hprefix tailTrace_1606432
  have hstable : (prefixWord ++ tailWord_1606432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1606432).length < 2 ^ (prefixWord ++ tailWord_1606432).sum := by decide
  have hdescent : baseEnd_1606432 < baseStart_1606432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1606432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
