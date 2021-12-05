import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Hspec

import Helpers (loadProg, evalProg)
import Transformations.Transformations
import qualified Grin.Grin as G
import Pipeline.Eval

import qualified Data.Text as T
import Reducer.Base


main :: IO ()
main = hspec spec

getProg path = do
    (Just p) <- loadProg path [] [] Nothing
    return p

spec :: Spec
spec = describe "Poitin-to-Grin transformation"  $ do
    it "zero plus zero" $ do
        p <- getProg ["test/test_data/zero_plus_zero"]

        let (poitin, grin) = transformP p

        (res, _) <- evalProgram IOReducer grin

        res `shouldBe` RT_ConstTagNode (G.Tag G.C (G.NM {G.unNM =T.pack "Zero"})) []

    it "multiply by zero" $ do
        p <- getProg ["test/test_data/zero_mult"]

        let (poitin, grin) = transformP p

        (res, _) <- evalProgram IOReducer grin

        res `shouldBe` RT_ConstTagNode (G.Tag G.C (G.NM {G.unNM =T.pack "Zero"})) []
    it "multiply by zero with lambda" $ do
        p <- getProg ["test/test_data/zero_mult_lambda"]

        let (poitin, grin) = transformP p

        (res, _) <- evalProgram IOReducer grin

        res `shouldBe` RT_ConstTagNode (G.Tag G.C (G.NM {G.unNM =T.pack "Zero"})) []
    it "multiply one by one simple" $ do
        p <- getProg ["test/test_data/mult_one_by_one"]

        let (poitin, grin) = transformP p

        (res, _) <- evalProgram IOReducer grin

        res `shouldBe` RT_ConstTagNode (G.Tag G.C (G.NM {G.unNM =T.pack "True"})) []
    it "multiply and get one" $ do
        p <- getProg ["test/test_data/mult_and_get_one"]

        let (poitin, grin) = transformP p

        (res, _) <- evalProgram IOReducer grin

        res `shouldBe` RT_ConstTagNode (G.Tag G.C (G.NM {G.unNM =T.pack "True"})) []    
    it "y combinator test" $ do
        p <- getProg ["test/test_data/another_nat_test"]

        let (poitin, grin) = transformP p

        (res, _) <- evalProgram IOReducer grin

        res `shouldBe` RT_ConstTagNode (G.Tag G.C (G.NM {G.unNM =T.pack "True"})) []    
    it "list of func" $ do
        p <- getProg ["test/test_data/list_of_funs"]

        let (poitin, grin) = transformP p

        (res, _) <- evalProgram IOReducer grin

        res `shouldBe` RT_ConstTagNode (G.Tag G.C (G.NM {G.unNM =T.pack "True"})) []    