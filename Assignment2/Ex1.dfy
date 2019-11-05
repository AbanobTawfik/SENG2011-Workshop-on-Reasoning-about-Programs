/////////////////////////////////////////////////////////////
//          ALL CODE IN HERE IS WRITTEN BY                 //
//                 ABANOB TAWFIK                           //
//                    Z5075490                             //
//                 November 2019                           //
/////////////////////////////////////////////////////////////

// Ex1.dfy 5 marks. 
// A class, Score, records the highest score of a game. You may assume the score cannot be
// negative. The class contains a constructor and a method called NewScore. There is also a test method
// called TestScore that is external to the class. There are all described below.
// Constructor Initialises the score to zero.
// NewScore The input parameter of this method is a score. If the input score is (strictly) higher than
// the current recorded score then it gets recorded. The method returns 2 variables: a Boolean
// indicating whether the recorded score changed or not, and the current highest score. Note that
// we are not keeping a history of scores: just the highest score.
// TestScore() This method makes a series of calls to NewScore with the scores 0, 2, 0, 4, 4, 6 in that
// order. The values returned by each call should be verified of course.
// Implement, verify and test the class.

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