class Score
{
    var HighScore: int;

    predicate Valid()
    reads this`HighScore
    {
        HighScore >= 0
    }

    constructor()
    modifies this`HighScore
    ensures Valid()
    ensures HighScore == 0
    {
        HighScore := 0;
    }

    method NewScore(score: int) returns(modified: bool, currentHighScore: int)
    modifies this`HighScore
    requires Valid() ensures Valid()
    ensures if score > old(HighScore) then (modified && (HighScore == score) && (currentHighScore == score))
                                 else (!modified && (HighScore == old(HighScore)) && (currentHighScore == HighScore))
    {
        if score > HighScore
        {
            modified := true;
            HighScore := score;
            currentHighScore := HighScore;
        }
        else
        {
            modified := false;
            currentHighScore := HighScore;
        }
    }
} //  end of Score class

method TestScore()
{
    // 0 2 0 4 4 6
    var modified, HighScore;
    var HighScoreKeeper := new Score();
    
    modified, HighScore := HighScoreKeeper.NewScore(-1);
    assert !modified;
    assert HighScore == 0;

    modified, HighScore := HighScoreKeeper.NewScore(0);
    assert !modified;
    assert HighScore == 0;

    modified, HighScore := HighScoreKeeper.NewScore(2);
    assert modified;
    assert HighScore == 2;

    modified, HighScore := HighScoreKeeper.NewScore(0);
    assert !modified;
    assert HighScore == 2;

    modified, HighScore := HighScoreKeeper.NewScore(4);
    assert modified;
    assert HighScore == 4;

    modified, HighScore := HighScoreKeeper.NewScore(4);
    assert !modified;
    assert HighScore == 4;

    modified, HighScore := HighScoreKeeper.NewScore(6);
    assert modified;
    assert HighScore == 6;

    modified, HighScore := HighScoreKeeper.NewScore(-1);
    assert !modified;
    assert HighScore == 6;
}