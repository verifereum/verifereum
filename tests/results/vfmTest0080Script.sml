Theory vfmTest0080[no_sig_docs]
Ancestors vfmTestDefs0080
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0080_0.nsv", "result0080_1.nsv"];
val thyn = "vfmTestDefs0080";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
