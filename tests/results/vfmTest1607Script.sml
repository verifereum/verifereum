Theory vfmTest1607[no_sig_docs]
Ancestors vfmTestDefs1607
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1607_0.nsv"];
val thyn = "vfmTestDefs1607";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
