Theory vfmTest2076[no_sig_docs]
Ancestors vfmTestDefs2076
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2076_0.nsv", "result2076_1.nsv", "result2076_2.nsv", "result2076_3.nsv", "result2076_4.nsv", "result2076_5.nsv", "result2076_6.nsv", "result2076_7.nsv", "result2076_8.nsv", "result2076_9.nsv", "result2076_10.nsv", "result2076_11.nsv", "result2076_12.nsv", "result2076_13.nsv", "result2076_14.nsv", "result2076_15.nsv"];
val thyn = "vfmTestDefs2076";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
