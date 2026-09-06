Theory vfmTest0069[no_sig_docs]
Ancestors vfmTestDefs0069
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0069_0.nsv", "result0069_1.nsv", "result0069_2.nsv", "result0069_3.nsv"];
val thyn = "vfmTestDefs0069";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
