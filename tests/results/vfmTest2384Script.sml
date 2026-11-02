Theory vfmTest2384[no_sig_docs]
Ancestors vfmTestDefs2384
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2384_0.nsv", "result2384_1.nsv", "result2384_2.nsv", "result2384_3.nsv", "result2384_4.nsv", "result2384_5.nsv", "result2384_6.nsv", "result2384_7.nsv", "result2384_8.nsv", "result2384_9.nsv", "result2384_10.nsv", "result2384_11.nsv", "result2384_12.nsv", "result2384_13.nsv", "result2384_14.nsv", "result2384_15.nsv", "result2384_16.nsv", "result2384_17.nsv", "result2384_18.nsv", "result2384_19.nsv"];
val thyn = "vfmTestDefs2384";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
