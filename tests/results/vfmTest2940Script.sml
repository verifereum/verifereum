Theory vfmTest2940[no_sig_docs]
Ancestors vfmTestDefs2940
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2940_0.nsv", "result2940_1.nsv", "result2940_2.nsv", "result2940_3.nsv", "result2940_4.nsv"];
val thyn = "vfmTestDefs2940";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
