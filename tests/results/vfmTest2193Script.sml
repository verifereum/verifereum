Theory vfmTest2193[no_sig_docs]
Ancestors vfmTestDefs2193
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2193_0.nsv", "result2193_1.nsv", "result2193_2.nsv", "result2193_3.nsv", "result2193_4.nsv", "result2193_5.nsv", "result2193_6.nsv", "result2193_7.nsv", "result2193_8.nsv", "result2193_9.nsv", "result2193_10.nsv", "result2193_11.nsv", "result2193_12.nsv", "result2193_13.nsv", "result2193_14.nsv", "result2193_15.nsv", "result2193_16.nsv", "result2193_17.nsv", "result2193_18.nsv", "result2193_19.nsv", "result2193_20.nsv", "result2193_21.nsv"];
val thyn = "vfmTestDefs2193";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
