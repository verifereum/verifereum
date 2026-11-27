Theory vfmTest1887[no_sig_docs]
Ancestors vfmTestDefs1887
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1887_0.nsv", "result1887_1.nsv"];
val thyn = "vfmTestDefs1887";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
