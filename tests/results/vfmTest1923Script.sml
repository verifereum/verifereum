Theory vfmTest1923[no_sig_docs]
Ancestors vfmTestDefs1923
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1923_0.nsv", "result1923_1.nsv", "result1923_2.nsv", "result1923_3.nsv", "result1923_4.nsv", "result1923_5.nsv", "result1923_6.nsv", "result1923_7.nsv", "result1923_8.nsv", "result1923_9.nsv", "result1923_10.nsv", "result1923_11.nsv", "result1923_12.nsv", "result1923_13.nsv", "result1923_14.nsv", "result1923_15.nsv", "result1923_16.nsv", "result1923_17.nsv", "result1923_18.nsv", "result1923_19.nsv", "result1923_20.nsv", "result1923_21.nsv", "result1923_22.nsv", "result1923_23.nsv"];
val thyn = "vfmTestDefs1923";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
