Theory vfmTest2185[no_sig_docs]
Ancestors vfmTestDefs2185
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2185_0.nsv", "result2185_1.nsv", "result2185_2.nsv"];
val thyn = "vfmTestDefs2185";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
