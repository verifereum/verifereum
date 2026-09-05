Theory vfmTest0252[no_sig_docs]
Ancestors vfmTestDefs0252
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0252_0.nsv", "result0252_1.nsv", "result0252_2.nsv", "result0252_3.nsv"];
val thyn = "vfmTestDefs0252";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
