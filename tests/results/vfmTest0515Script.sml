Theory vfmTest0515[no_sig_docs]
Ancestors vfmTestDefs0515
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0515_0.nsv", "result0515_1.nsv"];
val thyn = "vfmTestDefs0515";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
