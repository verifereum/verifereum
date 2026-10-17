Theory vfmTest0757[no_sig_docs]
Ancestors vfmTestDefs0757
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0757_0.nsv", "result0757_1.nsv", "result0757_2.nsv", "result0757_3.nsv", "result0757_4.nsv", "result0757_5.nsv", "result0757_6.nsv", "result0757_7.nsv", "result0757_8.nsv", "result0757_9.nsv", "result0757_10.nsv", "result0757_11.nsv"];
val thyn = "vfmTestDefs0757";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
