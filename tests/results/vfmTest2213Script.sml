Theory vfmTest2213[no_sig_docs]
Ancestors vfmTestDefs2213
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2213_0.nsv", "result2213_1.nsv", "result2213_2.nsv", "result2213_3.nsv", "result2213_4.nsv", "result2213_5.nsv", "result2213_6.nsv", "result2213_7.nsv", "result2213_8.nsv", "result2213_9.nsv", "result2213_10.nsv", "result2213_11.nsv"];
val thyn = "vfmTestDefs2213";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
