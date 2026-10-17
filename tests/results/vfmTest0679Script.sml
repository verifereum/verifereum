Theory vfmTest0679[no_sig_docs]
Ancestors vfmTestDefs0679
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0679_0.nsv", "result0679_1.nsv", "result0679_2.nsv", "result0679_3.nsv", "result0679_4.nsv", "result0679_5.nsv", "result0679_6.nsv", "result0679_7.nsv"];
val thyn = "vfmTestDefs0679";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
