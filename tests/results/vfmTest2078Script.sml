Theory vfmTest2078[no_sig_docs]
Ancestors vfmTestDefs2078
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2078_0.nsv", "result2078_1.nsv", "result2078_2.nsv"];
val thyn = "vfmTestDefs2078";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
