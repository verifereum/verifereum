Theory vfmTest0133[no_sig_docs]
Ancestors vfmTestDefs0133
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0133_0.nsv", "result0133_1.nsv", "result0133_2.nsv", "result0133_3.nsv"];
val thyn = "vfmTestDefs0133";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
