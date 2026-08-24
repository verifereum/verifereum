Theory vfmTest2085[no_sig_docs]
Ancestors vfmTestDefs2085
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2085_0.nsv"];
val thyn = "vfmTestDefs2085";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
