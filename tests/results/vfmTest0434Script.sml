Theory vfmTest0434[no_sig_docs]
Ancestors vfmTestDefs0434
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0434_0.nsv", "result0434_1.nsv", "result0434_2.nsv", "result0434_3.nsv", "result0434_4.nsv", "result0434_5.nsv", "result0434_6.nsv", "result0434_7.nsv", "result0434_8.nsv", "result0434_9.nsv", "result0434_10.nsv", "result0434_11.nsv"];
val thyn = "vfmTestDefs0434";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
