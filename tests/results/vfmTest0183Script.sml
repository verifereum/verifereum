Theory vfmTest0183[no_sig_docs]
Ancestors vfmTestDefs0183
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0183_0.nsv", "result0183_1.nsv", "result0183_2.nsv", "result0183_3.nsv"];
val thyn = "vfmTestDefs0183";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
