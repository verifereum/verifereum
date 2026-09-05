Theory vfmTest0619[no_sig_docs]
Ancestors vfmTestDefs0619
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0619_0.nsv", "result0619_1.nsv", "result0619_2.nsv"];
val thyn = "vfmTestDefs0619";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
