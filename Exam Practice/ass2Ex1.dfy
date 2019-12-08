class Score
{
    var highScore: int;
    
    predicate Valid()
    reads this
    {
        highScore >= 0
    }
    
    constructor()
    ensures Valid()
    modifies this, this`highScore
    ensures highScore == 0
    {
        highScore := 0;
    }
    
    method NewScore(score: int) returns(changed: bool, newScore: int)
    requires Valid() ensures Valid()
    modifies this, this`highScore
    ensures if score > old(highScore) then (highScore == score) && newScore == highScore && changed
                                      else highScore == old(highScore) && newScore == old(highScore) && !changed
    {
        if(score > highScore)
        {
            changed := true;
            highScore := score;
        }
        else
        {
            changed := false;
        }
        
        newScore := highScore;
    }
    
    method TestScore()
    {
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

        // my own test to check negative numbers aswell
        modified, HighScore := HighScoreKeeper.NewScore(-1);
        assert !modified;
        assert HighScore == 6;
    }
} // end of score class
