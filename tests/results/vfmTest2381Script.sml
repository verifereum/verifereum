Theory vfmTest2381[no_sig_docs]
Ancestors vfmTestDefs2381
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2381_0.nsv", "result2381_1.nsv", "result2381_2.nsv", "result2381_3.nsv", "result2381_4.nsv", "result2381_5.nsv", "result2381_6.nsv", "result2381_7.nsv", "result2381_8.nsv", "result2381_9.nsv", "result2381_10.nsv", "result2381_11.nsv", "result2381_12.nsv", "result2381_13.nsv", "result2381_14.nsv", "result2381_15.nsv", "result2381_16.nsv", "result2381_17.nsv"];
val thyn = "vfmTestDefs2381";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
