Theory vfmTest1809[no_sig_docs]
Ancestors vfmTestDefs1809
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1809_0.nsv", "result1809_1.nsv", "result1809_2.nsv", "result1809_3.nsv"];
val thyn = "vfmTestDefs1809";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
