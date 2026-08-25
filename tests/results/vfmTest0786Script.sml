Theory vfmTest0786[no_sig_docs]
Ancestors vfmTestDefs0786
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0786_0.nsv", "result0786_1.nsv", "result0786_2.nsv"];
val thyn = "vfmTestDefs0786";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
