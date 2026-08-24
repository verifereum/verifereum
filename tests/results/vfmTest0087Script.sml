Theory vfmTest0087[no_sig_docs]
Ancestors vfmTestDefs0087
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0087_0.nsv", "result0087_1.nsv", "result0087_2.nsv", "result0087_3.nsv", "result0087_4.nsv", "result0087_5.nsv"];
val thyn = "vfmTestDefs0087";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
