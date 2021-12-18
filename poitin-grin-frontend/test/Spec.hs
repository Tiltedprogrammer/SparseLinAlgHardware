import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Hspec

import Helpers (loadProg, evalProg)
import Transformations.Transformations
import qualified Grin.Grin as G
import Pipeline.Eval

import qualified Data.Text as T
import Reducer.Base

import Pipeline.Pipeline
import Reducer.PrimOps (evalPrimOp)
import Reducer.Pure

main :: IO ()
main = hspec spec

getProg path = do
    (Just p) <- loadProg path [] [] Nothing
    return p

opts = defaultOpts
                    { _poFailOnLint = False
                    , _poLogging = True
                    , _poSaveBinary = False
                    , _poCFiles = []
                    }

-- evalGrin prog = optimize opts prog [] [] >>= evalProgram (PureReducer (EvalPlugin evalPrimOp))
evalGrin prog = pipeline opts Nothing  prog [] >>= evalProgram  (PureReducer (EvalPlugin evalPrimOp))

spec :: Spec
spec = describe "Poitin-to-Grin transformation"  $ do
    it "zero plus zero" $ do
        p <- getProg ["test/test_data/zero_plus_zero"]

        let (poitin, grin) = transformP p

        (res, _) <- evalGrin grin

        res `shouldBe` RT_ConstTagNode (G.Tag G.C (G.NM {G.unNM =T.pack "Zero"})) []

    it "multiply by zero" $ do
        p <- getProg ["test/test_data/zero_mult"]

        let (poitin, grin) = transformP p

        (res, _) <- evalGrin grin

        res `shouldBe` RT_ConstTagNode (G.Tag G.C (G.NM {G.unNM =T.pack "Zero"})) []
    it "multiply by zero with lambda" $ do
        p <- getProg ["test/test_data/zero_mult_lambda"]

        let (poitin, grin) = transformP p

        (res, _) <- evalGrin grin

        res `shouldBe` RT_ConstTagNode (G.Tag G.C (G.NM {G.unNM =T.pack "Zero"})) []
    it "multiply one by one simple" $ do
        p <- getProg ["test/test_data/mult_one_by_one"]

        let (poitin, grin) = transformP p

        (res, _) <- evalGrin grin

        res `shouldBe` RT_ConstTagNode (G.Tag G.C (G.NM {G.unNM =T.pack "True"})) []
    it "multiply and get one" $ do
        p <- getProg ["test/test_data/mult_and_get_one"]

        let (poitin, grin) = transformP p

        (res, _) <- evalGrin grin

        res `shouldBe` RT_ConstTagNode (G.Tag G.C (G.NM {G.unNM =T.pack "True"})) []
    it "y combinator test" $ do
        p <- getProg ["test/test_data/another_nat_test"]

        let (poitin, grin) = transformP p

        (res, _) <- evalGrin grin

        res `shouldBe` RT_ConstTagNode (G.Tag G.C (G.NM {G.unNM =T.pack "True"})) []
    it "list of func" $ do
        p <- getProg ["test/test_data/list_of_funs"]

        let (poitin, grin) = transformP p

        (res, _) <- evalGrin grin

        res `shouldBe` RT_ConstTagNode (G.Tag G.C (G.NM {G.unNM =T.pack "True"})) []
    
    it "fold with partially applied fun" $ do
        p <- getProg ["test/test_data/fold_test"]

        let (poitin, grin) = transformP p

        (res, _) <- evalGrin grin

        res `shouldBe` RT_ConstTagNode (G.Tag G.C (G.NM {G.unNM =T.pack "True"})) []
    
    it "fold of mAdd" $ do
        p <- getProg ["test/test_data/linalg_test"]

        let (poitin, grin) = transformP p

        (res, _) <- evalGrin grin

        res `shouldBe` RT_ConstTagNode (G.Tag G.C (G.NM {G.unNM =T.pack "True"})) []
    
    it "fold of mAdd 2" $ do
        p <- getProg ["test/test_data/linalg_test_2"]

        let (poitin, grin) = transformP p

        (res, _) <- evalGrin grin

        res `shouldBe` RT_ConstTagNode (G.Tag G.C (G.NM {G.unNM =T.pack "True"})) []