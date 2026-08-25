Theory vfmTest0078[no_sig_docs]
Ancestors vfmTestDefs0078
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0078_0.nsv", "result0078_1.nsv"];
val thyn = "vfmTestDefs0078";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
