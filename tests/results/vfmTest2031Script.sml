Theory vfmTest2031[no_sig_docs]
Ancestors vfmTestDefs2031
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2031_0.nsv"];
val thyn = "vfmTestDefs2031";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
