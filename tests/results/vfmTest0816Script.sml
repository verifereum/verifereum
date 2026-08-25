Theory vfmTest0816[no_sig_docs]
Ancestors vfmTestDefs0816
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0816_0.nsv", "result0816_1.nsv"];
val thyn = "vfmTestDefs0816";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
