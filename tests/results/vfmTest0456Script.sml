Theory vfmTest0456[no_sig_docs]
Ancestors vfmTestDefs0456
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0456_0.nsv", "result0456_1.nsv", "result0456_2.nsv", "result0456_3.nsv", "result0456_4.nsv", "result0456_5.nsv", "result0456_6.nsv", "result0456_7.nsv"];
val thyn = "vfmTestDefs0456";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
