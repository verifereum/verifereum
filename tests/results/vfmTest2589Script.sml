Theory vfmTest2589[no_sig_docs]
Ancestors vfmTestDefs2589
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2589_0.nsv", "result2589_1.nsv", "result2589_2.nsv", "result2589_3.nsv"];
val thyn = "vfmTestDefs2589";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
