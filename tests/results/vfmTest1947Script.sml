Theory vfmTest1947[no_sig_docs]
Ancestors vfmTestDefs1947
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1947_0.nsv", "result1947_1.nsv", "result1947_2.nsv", "result1947_3.nsv", "result1947_4.nsv", "result1947_5.nsv", "result1947_6.nsv", "result1947_7.nsv", "result1947_8.nsv", "result1947_9.nsv", "result1947_10.nsv", "result1947_11.nsv"];
val thyn = "vfmTestDefs1947";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
